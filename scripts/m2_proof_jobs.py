#!/usr/bin/env python3
"""Frozen M2 proof jobs: sandboxed synthesis, separate kernel validation, replay.

This program does not grant intent approval and never runs Lean tactics on the
host. A candidate is an untrusted Lean term, not a Lean module. Publication of a
checked packet is not editor acceptance: #m2_replay_proof repeats the check.
Linux and bubblewrap are required. There is no unsandboxed fallback. No model
credential is inherited. An external coding agent supplies successive candidates.
"""
from __future__ import annotations
import argparse
import ctypes
import errno
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
from typing import Any, Callable, Iterable

JOB_FORMAT = "macaulean.proof-job.v1"
PROOF_FORMAT = "macaulean.proof-term.v1"
RECEIPT_FORMAT = "macaulean.proof-receipt.v1"
JOB_FIELDS = {"format", "jobId", "bindingId", "bindingName", "schema", "approvalSource",
              "approvalDigest", "theoryDigest", "leanVersion", "targetKey", "target"}
PROOF_FIELDS = {"format", "jobId", "targetKey", "term"}
RECEIPT_FIELDS = {"format", "jobId", "targetKey", "proofKey", "theoryDigest", "theoremName",
                  "theoremRef", "axioms", "leanVersion", "status"}
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
SCHEMAS = {"polynomialIdentity", "orderedRemainder", "linearCombination"}
MAX_PACKET = 16 * 1024 * 1024
MAX_CANDIDATE = 1024 * 1024

class JobError(RuntimeError):
    pass

class StaleJob(JobError):
    pass

def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def is_digest(value: Any) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)

def _pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise JobError(f"duplicate JSON key: {key}")
        result[key] = value
    return result

def _constant(value: str) -> Any:
    raise JobError(f"non-JSON numeric constant: {value}")

def decode_json(data: bytes, fields: set[str]) -> dict[str, Any]:
    if not data or len(data) > MAX_PACKET:
        raise JobError("empty or oversized JSON packet")
    try:
        value = json.loads(data.decode("utf-8"), object_pairs_hook=_pairs, parse_constant=_constant)
    except (UnicodeError, ValueError, RecursionError) as exc:
        raise JobError(f"invalid JSON packet: {exc}") from exc
    if type(value) is not dict or set(value) != fields:
        raise JobError("wrong packet fields; no optional success flags are accepted")
    return value

def read_regular(path: Path, limit: int = MAX_PACKET) -> bytes:
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_size > limit:
            raise JobError(f"not a bounded regular file: {path}")
        with os.fdopen(fd, "rb", closefd=False) as stream:
            value = stream.read(limit + 1)
        if len(value) > limit:
            raise JobError(f"file grew beyond its size bound: {path}")
        return value
    finally:
        os.close(fd)

def parse_job(data: bytes) -> dict[str, Any]:
    job = decode_json(data, JOB_FIELDS)
    if job["format"] != JOB_FORMAT:
        raise JobError("unknown proof-job protocol")
    for field in ("jobId", "bindingId", "approvalDigest", "theoryDigest"):
        if not is_digest(job[field]):
            raise JobError(f"invalid {field}")
    if job["jobId"] != job["approvalDigest"]:
        raise JobError("job is not the approved revision")
    if not isinstance(job["schema"], str) or job["schema"] not in SCHEMAS:
        raise JobError("unknown specification schema")
    for field in ("bindingName", "approvalSource", "leanVersion", "targetKey"):
        if not isinstance(job[field], str) or not job[field]:
            raise JobError(f"missing {field}")
    if not isinstance(job["target"], list):
        raise JobError("missing closed target expression")
    return job

def parse_proof(data: bytes, job: dict[str, Any]) -> dict[str, Any]:
    packet = decode_json(data, PROOF_FIELDS)
    if packet["format"] != PROOF_FORMAT:
        raise JobError("unknown proof-term protocol")
    if packet["jobId"] != job["jobId"] or packet["targetKey"] != job["targetKey"]:
        raise JobError("candidate belongs to a different target")
    if not isinstance(packet["term"], list):
        raise JobError("proof is not a serialized kernel expression")
    return packet

def parse_receipt(data: bytes, job: dict[str, Any]) -> dict[str, Any]:
    receipt = decode_json(data, RECEIPT_FIELDS)
    if receipt["format"] != RECEIPT_FORMAT or receipt["status"] != "kernel-checked":
        raise JobError("validator did not produce checked evidence")
    for key in ("jobId", "targetKey", "theoryDigest", "leanVersion"):
        if receipt[key] != job[key]:
            raise JobError(f"validator checked a different {key}")
    if not is_digest(receipt["proofKey"]):
        raise JobError("invalid proof fingerprint")
    if not isinstance(receipt["theoremName"], str) or not receipt["theoremName"]:
        raise JobError("validator did not identify the checked theorem")
    if not isinstance(receipt["theoremRef"], list):
        raise JobError("missing structured theorem name")
    if type(receipt["axioms"]) is not list or any(type(a) is not str or a not in AXIOMS for a in receipt["axioms"]):
        raise JobError("proof contains unapproved dependency assumptions")
    return receipt

def write_once(path: Path, data: bytes) -> None:
    """Idempotent immutable write; a different prior object is never replaced."""
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    except FileExistsError:
        if read_regular(path, max(MAX_PACKET, len(data))) != data:
            raise JobError(f"refusing to overwrite different retained evidence: {path}")
        return
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        path.unlink(missing_ok=True)
        raise

@dataclass(frozen=True)
class Limits:
    seconds: int = 120
    memory_bytes: int = 4 * 1024**3
    disk_bytes: int = 64 * 1024**2
    processes: int = 512

    def __post_init__(self) -> None:
        if self.seconds < 1 or self.memory_bytes < 64 * 1024**2 or self.disk_bytes < MAX_PACKET:
            raise ValueError("invalid worker limits")
        if self.processes < 1:
            raise ValueError("invalid process limit")

    def install(self) -> None:
        resource.setrlimit(resource.RLIMIT_CPU, (self.seconds, self.seconds))
        resource.setrlimit(resource.RLIMIT_AS, (self.memory_bytes, self.memory_bytes))
        resource.setrlimit(resource.RLIMIT_FSIZE, (self.disk_bytes, self.disk_bytes))
        resource.setrlimit(resource.RLIMIT_NPROC, (self.processes, self.processes))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

@dataclass(frozen=True)
class Context:
    root: Path
    digest: str

def context_files(project: Path) -> list[tuple[Path, Path]]:
    """Only source and built Lean libraries; never .git, credentials or outputs.

    Include both the .olean directory and its linked native library parent. The
    same frozen libraries accelerate both processes; proof acceptance still uses
    the kernel and not a native-evaluation axiom.
    """
    answer: list[tuple[Path, Path]] = []
    for root in (project / "Macaulean", project / ".lake/build/lib"):
        if root.is_symlink() or not root.resolve().is_relative_to(project):
            raise JobError("proof context root escapes its project")
        if not root.is_dir():
            raise JobError(f"missing built context: {root}; build the trusted baseline first")
        for directory, dirs, names in os.walk(root, followlinks=False):
            here = Path(directory)
            for name in dirs:
                if (here / name).is_symlink():
                    raise JobError("symlink directory in proof context")
            for name in names:
                source = here / name
                if source.is_symlink():
                    raise JobError("symlink file in proof context")
                relative = source.relative_to(project)
                if root.name == "Macaulean" and source.suffix not in {".lean", ".m2"}:
                    continue
                answer.append((relative, source))
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        source = project / name
        if source.exists():
            if source.is_symlink():
                raise JobError("symlink manifest in proof context")
            answer.append((Path(name), source))
    return sorted(answer, key=lambda p: p[0].as_posix())

def context_digest(files: Iterable[tuple[Path, Path]]) -> str:
    digest = hashlib.sha256()
    for relative, source in files:
        path = relative.as_posix().encode("utf-8")
        digest.update(len(path).to_bytes(8, "big"))
        digest.update(path)
        data = read_regular(source, 512 * 1024**2)
        digest.update(len(data).to_bytes(8, "big"))
        digest.update(hashlib.sha256(data).digest())
    return digest.hexdigest()

def snapshot_context(project: Path, destination: Path) -> Context:
    files = context_files(project)
    before = context_digest(files)
    for relative, source in files:
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        data = read_regular(source, 512 * 1024**2)
        target.write_bytes(data)
        target.chmod(0o444)
    after = context_digest(context_files(project))
    copied = context_digest((relative, destination / relative) for relative, _ in files)
    if not before == after == copied:
        raise StaleJob("context changed while it was being snapshotted")
    return Context(destination, before)

@dataclass(frozen=True)
class RunResult:
    code: int
    timed_out: bool
    stdout: Path
    stderr: Path

    def checked_output(self) -> bytes:
        if self.timed_out or self.code != 0:
            raise JobError(f"Lean process did not complete successfully: exit={self.code}, timeout={self.timed_out}")
        return read_regular(self.stdout)

class Sandbox:
    def __init__(self, toolchain: Path, limits: Limits = Limits()) -> None:
        self.toolchain = toolchain.resolve(strict=True)
        self.limits = limits
        self.binary = shutil.which("bwrap")
        if sys.platform != "linux" or not self.binary:
            raise JobError("isolated proof execution requires Linux bubblewrap; no unsandboxed fallback")
        if not (self.toolchain / "bin/lean").is_file() or self.toolchain == Path("/"):
            raise JobError("invalid Lean toolchain directory")

    def command(self, context: Context, inputs: Path) -> list[str]:
        cmd = [self.binary, "--unshare-all", "--die-with-parent", "--new-session", "--clearenv"]
        for directory in ("/usr", "/bin", "/lib", "/lib64"):
            if Path(directory).exists():
                cmd += ["--ro-bind", directory, directory]
        cmd += ["--dir", "/etc"]
        if Path("/etc/ld.so.cache").is_file():
            cmd += ["--ro-bind", "/etc/ld.so.cache", "/etc/ld.so.cache"]
        cmd += [
            "--proc", "/proc", "--dev", "/dev",
            "--ro-bind", str(context.root), "/project",
            "--ro-bind", str(self.toolchain), "/toolchain",
            "--ro-bind", str(inputs), "/input",
            "--size", str(self.limits.disk_bytes), "--tmpfs", "/work",
            "--size", str(self.limits.disk_bytes), "--tmpfs", "/tmp",
            "--chdir", "/work", "--setenv", "HOME", "/work",
            "--setenv", "PATH", "/toolchain/bin:/usr/bin:/bin",
            "--setenv", "LEAN_PATH", "/project/.lake/build/lib/lean",
            "--setenv", "LANG", "C.UTF-8", "--",
            "/bin/sh", "-c",
            "set -eu\n/toolchain/bin/lean --root=/input "
            "--load-dynlib=/project/.lake/build/lib/libMacaulean_MRDI.so "
            "--load-dynlib=/project/.lake/build/lib/libMacaulean_Macaulean.so "
            "-DmaxRecDepth=32768 -DmaxHeartbeats=20000000 /input/Run.lean >&2\n"
            "exec /bin/cat /work/result.json",
        ]
        return cmd

    def run(self, context: Context, inputs: Path, logdir: Path) -> RunResult:
        logdir.mkdir(parents=True, exist_ok=False)
        stdout, stderr = logdir / "stdout", logdir / "stderr"
        with stdout.open("xb") as out, stderr.open("xb") as err:
            proc = subprocess.Popen(
                self.command(context, inputs), stdin=subprocess.DEVNULL, stdout=out, stderr=err,
                env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"},
                start_new_session=True, preexec_fn=self.limits.install,
            )
            timeout = False
            try:
                code = proc.wait(timeout=self.limits.seconds + 5)
            except subprocess.TimeoutExpired:
                timeout = True
                os.killpg(proc.pid, signal.SIGKILL)
                code = proc.wait()
        write_once(logdir / "process.json", json.dumps({"exit": code, "timedOut": timeout}).encode())
        return RunResult(code, timeout, stdout, stderr)

def assert_current(manifest: Path, original: bytes, project: Path, context: Context) -> None:
    if read_regular(manifest) != original:
        raise StaleJob("job manifest changed before publication")
    if context_digest(context_files(project)) != context.digest:
        raise StaleJob("source/build context changed before publication")

def rename_no_replace(source: Path, destination: Path) -> None:
    """Atomic no-replace rename; even an empty competing directory survives."""
    library = ctypes.CDLL(None, use_errno=True)
    operation = getattr(library, "renameat2", None)
    if operation is None:
        raise OSError(errno.ENOSYS, "atomic no-replace publication is unavailable")
    operation.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    operation.restype = ctypes.c_int
    if operation(-100, os.fsencode(source), -100, os.fsencode(destination), 1) != 0:
        code = ctypes.get_errno()
        raise OSError(code, os.strerror(code), str(destination))

def publish_evidence(destination: Path, files: dict[str, bytes], recheck: Callable[[], None]) -> None:
    """Publish an entire immutable receipt; identical concurrent writes are allowed."""
    expected = {"target.json", "proof.json", "receipt.json", "context.sha256"}
    if set(files) != expected:
        raise JobError("incomplete evidence manifest")

    def validate_existing() -> None:
        if destination.is_symlink() or not destination.is_dir():
            raise JobError("evidence address is not a regular directory")
        if {entry.name for entry in destination.iterdir()} != expected:
            raise JobError("incomplete or unexpected retained evidence")
        for name, content in files.items():
            if read_regular(destination / name) != content:
                raise JobError(f"different retained evidence: {name}")

    destination.parent.mkdir(parents=True, exist_ok=True)
    recheck()
    if destination.exists() or destination.is_symlink():
        validate_existing()
        recheck()
        return
    staging = Path(tempfile.mkdtemp(prefix=".proof-", dir=destination.parent))
    try:
        for name, content in files.items():
            write_once(staging / name, content)
        recheck()
        try:
            rename_no_replace(staging, destination)
        except OSError:
            if not destination.exists():
                raise
            validate_existing()
    finally:
        if staging.exists():
            shutil.rmtree(staging)

def run_job(manifest: Path, candidate: Path, project: Path, toolchain: Path,
            output: Path, limits: Limits = Limits()) -> Path:
    manifest = manifest.absolute()
    original = read_regular(manifest)
    job = parse_job(original)
    candidate_bytes = read_regular(candidate, MAX_CANDIDATE)
    candidate_bytes.decode("utf-8")
    if not candidate_bytes.strip():
        raise JobError("empty candidate")
    project = project.resolve(strict=True)
    output.mkdir(parents=True, exist_ok=True)
    sandbox = Sandbox(toolchain, limits)
    attempt = output / "attempts" / f"{job['jobId']}-{time.time_ns()}"
    attempt.mkdir(parents=True, exist_ok=False)
    write_once(attempt / "target.json", original)
    write_once(attempt / "candidate.lean", candidate_bytes)
    with tempfile.TemporaryDirectory(prefix="m2-proof-context-") as temp:
        context = snapshot_context(project, Path(temp) / "context")
        synth = Path(temp) / "synthesis"
        synth.mkdir()
        (synth / "job.json").write_bytes(original)
        (synth / "candidate.lean").write_bytes(candidate_bytes)
        (synth / "Run.lean").write_text(
            'import Macaulean.Verification.ProofJobs.Prover\n'
            '#m2_synthesize_proof_job "/input/job.json" "/input/candidate.lean" "/work/result.json"\n')
        raw_proof = sandbox.run(context, synth, attempt / "synthesis").checked_output()
        parse_proof(raw_proof, job)
        write_once(attempt / "proof.json", raw_proof)
        assert_current(manifest, original, project, context)
        check = Path(temp) / "validation"
        check.mkdir()
        (check / "job.json").write_bytes(original)
        (check / "proof.json").write_bytes(raw_proof)
        (check / "Run.lean").write_text(
            'import Macaulean.Verification.ProofJobs.Checker\n'
            '#m2_validate_proof_job "/input/job.json" "/input/proof.json" "/work/result.json"\n')
        raw_receipt = sandbox.run(context, check, attempt / "validation").checked_output()
        receipt = parse_receipt(raw_receipt, job)
        assert_current(manifest, original, project, context)
        write_once(attempt / "receipt.json", raw_receipt)
        destination = output / "checked" / job["jobId"] / context.digest / receipt["proofKey"]
        publish_evidence(destination, {
            "target.json": original, "proof.json": raw_proof,
            "receipt.json": raw_receipt, "context.sha256": context.digest.encode(),
        }, lambda: assert_current(manifest, original, project, context))
        return destination

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("candidate", type=Path, nargs="+")
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--seconds", type=int, default=120)
    args = parser.parse_args()
    failures = []
    for candidate in args.candidate:
        try:
            result = run_job(args.manifest, candidate, args.project, args.toolchain,
                             args.output, Limits(seconds=args.seconds))
            print(json.dumps({"status": "checked-for-frozen-job", "directory": str(result),
                              "editorReplayRequired": True}))
            return 0
        except StaleJob as exc:
            print(f"STALE: {exc}", file=sys.stderr)
            return 2
        except (JobError, OSError, UnicodeError) as exc:
            failures.append({"candidate": str(candidate), "error": str(exc)})
            print(json.dumps(failures[-1]), file=sys.stderr)
    print(json.dumps({"status": "no-accepted-proof", "attempts": failures}), file=sys.stderr)
    return 1

if __name__ == "__main__":
    raise SystemExit(main())
