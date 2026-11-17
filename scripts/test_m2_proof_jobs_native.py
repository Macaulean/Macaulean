#!/usr/bin/env python3
"""Real synthesis, independent kernel validation, and fresh source replay.

The fixture's attestation is synthetic test data, not project intent approval.
The second candidate is assistant-authored; this is not a hosted-model API test.
The same runner accepts newly agent-produced terms. Compiler/sandbox failures
cannot satisfy negative controls.
"""
from __future__ import annotations
import json
from pathlib import Path
import subprocess
import tempfile
import time
from m2_proof_jobs import JobError, Limits, parse_job, read_regular, run_job

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'ci-evidence'
RUN_ID = str(time.time_ns())

def replay(proof: Path, digest: str, label: str, *, change=False, revoke=False, comment=False):
    body = 'p -> p+1' if change else ('p -> (p)' if comment else 'p -> p')
    source = '''import Macaulean.Verification.Proofs
namespace Stage2SyntheticFixture
open Lean Elab Command
open Macaulean.M2 Macaulean.M2.Verification
open _root_.M2
'''
    if comment:
        source += '-- nonsemantic replay control: λ, 中文\n'
    source += f'toyIdentity = {body};\n#m2_contract "toyIdentity" polynomialIdentity\n'
    source += f'#m2_approve "toyIdentity" polynomialIdentity "{digest}"\n'
    if revoke:
        source += '#m2_revoke "toyIdentity" polynomialIdentity\n'
    source += '#m2_replay_proof "toyIdentity" polynomialIdentity ' + json.dumps(str(proof)) + '\n'
    source += '#m2_proof_status "toyIdentity" polynomialIdentity\nend Stage2SyntheticFixture\n'
    logdir = EVIDENCE / 'stage2-replay' / RUN_ID / label
    logdir.mkdir(parents=True, exist_ok=False)
    (logdir / 'source.lean').write_text(source, encoding='utf-8')
    with tempfile.TemporaryDirectory(prefix='m2-replay-') as tmp:
        # Preserve the export fixture's module identity in every fresh process.
        path = Path(tmp) / 'MacauleanTest/ProofJobExport.lean'
        path.parent.mkdir()
        path.write_text(source, encoding='utf-8')
        with (logdir / 'stdout').open('wb') as out, (logdir / 'stderr').open('wb') as err:
            proc = subprocess.run(['lake', 'env', 'lean',
                '--load-dynlib='+str(ROOT / '.lake/build/lib/libMacaulean_MRDI.so'),
                '--load-dynlib='+str(ROOT / '.lake/build/lib/libMacaulean_Macaulean.so'),
                f'--root={tmp}', str(path)], cwd=ROOT, stdout=out, stderr=err, timeout=240)
    (logdir / 'exit').write_text(str(proc.returncode))
    output = (logdir / 'stdout').read_text(errors='replace') + (logdir / 'stderr').read_text(errors='replace')
    if change or revoke:
        expected = 'approval fingerprint' if change else 'current source-attested contract'
        assert proc.returncode != 0 and expected in output, (label, output)
        assert 'kernel-checked partial correctness' not in output, (label, output)
    else:
        assert proc.returncode == 0 and 'kernel-checked partial correctness' in output, (label, output)
    return output

def main() -> int:
    prefix = subprocess.run(['lean', '--print-prefix'], check=True, capture_output=True, text=True).stdout.strip()
    toolchain = Path(prefix)
    manifest = EVIDENCE / 'stage2-target.json'
    job = parse_job(read_regular(manifest))
    outputs = EVIDENCE / 'stage2-native' / RUN_ID
    for label, name in [('regression', 'identity'), ('assistant-authored', 'identity-agent')]:
        result = run_job(manifest, ROOT / f'tests/proof-candidates/{name}.proof', ROOT, toolchain,
                         outputs / label, Limits(seconds=180))
        assert (result / 'receipt.json').is_file() and (result / 'proof.json').is_file()
        (EVIDENCE / f'stage2-{label}-result.json').write_text(json.dumps({'directory': str(result)}))
    print('STAGE2_NATIVE_POSITIVE_COMPLETE: two real candidates, separate synthesis and kernel acceptance', flush=True)
    # The term parser refuses the appended command before elaborating either
    # the proof or the axiom. Require that precise boundary, not any error.
    injection = read_regular(ROOT / 'tests/proof-candidates/injection.proof').decode('utf-8')
    assert injection.splitlines() == ['by', '  trivial', 'axiom injected : False']
    controls = [('hole', 'validation', 'unapproved axiom: sorryAx'),
                ('injection', 'synthesis', '<input>:3:0: expected end of input'),
                ('wrong', 'synthesis', 'type mismatch')]
    for name, stage, marker in controls:
        out = outputs / name
        try:
            run_job(manifest, ROOT / f'tests/proof-candidates/{name}.proof', ROOT, toolchain,
                    out, Limits(seconds=180))
        except JobError:
            attempts = sorted((out / 'attempts').iterdir())
            assert len(attempts) == 1, (name, attempts)
            stderr = attempts[0] / stage / 'stderr'
            assert stderr.is_file(), f'{name}: required stage never ran'
            text = stderr.read_text(encoding='utf-8', errors='replace')
            assert marker.lower() in text.lower(), f'{name}: wrong rejection: {text}'
            status = json.loads((stderr.parent / 'process.json').read_text())
            assert status['exit'] != 0 and not status['timedOut'], (name, status)
            assert not (out / 'checked').exists(), f'{name}: failed proof was published'
            if stage == 'synthesis':
                assert not (attempts[0] / 'validation').exists(), f'{name}: rejected source reached validator'
                assert not (attempts[0] / 'proof.json').exists(), f'{name}: rejected source emitted a proof'
        else:
            raise AssertionError(f'unacceptable proof passed: {name}')
    print('STAGE2_NATIVE_NEGATIVE_COMPLETE: holes, command injection and wrong proposition', flush=True)
    packet = result / 'proof.json'
    replay(packet, job['approvalDigest'], 'fresh')
    replay(packet, job['approvalDigest'], 'restarted')
    replay(packet, job['approvalDigest'], 'comment-only', comment=True)
    replay(packet, job['approvalDigest'], 'changed-code', change=True)
    replay(packet, job['approvalDigest'], 'revoked', revoke=True)
    print('STAGE2_FRESH_REPLAY_COMPLETE: literal approval, fresh processes, comments, changed code and revocation', flush=True)
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
