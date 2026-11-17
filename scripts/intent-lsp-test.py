#!/usr/bin/env python3
"""Real Lean LSP/RPC integration test; no fake elaborator or approval endpoint.

All approvals are synthetic fixtures for a toy identity function. The test inserts
exact source directives returned by the read-only panel data, then waits for Lean
and checks the resulting versioned snapshots. Logs are retained by CI.
"""
from __future__ import annotations
import json
import os
from pathlib import Path
import queue
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "ci-evidence"
EVIDENCE.mkdir(exist_ok=True)
TIMEOUT = 180


class Client:
    def __init__(self, label: str):
        self.stderr = (EVIDENCE / f"intent-lsp-{label}.stderr").open("wb")
        self.transcript = (EVIDENCE / f"intent-lsp-{label}.jsonl").open("w", encoding="utf-8")
        self.process = subprocess.Popen(
            ["lake", "env", "lean", "--server"], cwd=ROOT,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.stderr)
        self.inbox: queue.Queue = queue.Queue()
        self.ids = 0
        self.diagnostics: dict[str, list] = {}
        self.thread = threading.Thread(target=self._read, daemon=True)
        self.thread.start()
        self.request("initialize", {
            "processId": os.getpid(), "rootUri": ROOT.as_uri(),
            "capabilities": {}, "workspaceFolders": [{"uri": ROOT.as_uri(), "name": "Macaulean"}]})
        self.notify("initialized", {})

    def _read(self):
        try:
            while True:
                headers = {}
                while True:
                    line = self.process.stdout.readline()
                    if not line:
                        raise EOFError("Lean language server closed stdout")
                    if line in (b"\r\n", b"\n"):
                        break
                    k, v = line.decode("ascii").split(":", 1)
                    headers[k.lower()] = v.strip()
                size = int(headers["content-length"])
                chunks = bytearray()
                while len(chunks) < size:
                    part = self.process.stdout.read(size - len(chunks))
                    if not part:
                        raise EOFError("truncated Lean response")
                    chunks.extend(part)
                self.inbox.put(json.loads(chunks))
        except BaseException as exc:
            self.inbox.put(exc)

    def send(self, message):
        self.transcript.write(json.dumps({"send": message}, ensure_ascii=False) + "\n")
        self.transcript.flush()
        data = json.dumps(message, ensure_ascii=False).encode("utf-8")
        self.process.stdin.write(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
        self.process.stdin.flush()

    def notify(self, method, params):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def request(self, method, params, *, expect_error=False):
        self.ids += 1
        ident = self.ids
        self.send({"jsonrpc": "2.0", "id": ident, "method": method, "params": params})
        deadline = time.monotonic() + TIMEOUT
        while True:
            try:
                message = self.inbox.get(timeout=max(0.01, deadline - time.monotonic()))
            except queue.Empty as exc:
                raise TimeoutError(f"Lean did not answer {method}") from exc
            if isinstance(message, BaseException):
                raise message
            self.transcript.write(json.dumps({"receive": message}, ensure_ascii=False) + "\n")
            self.transcript.flush()
            if message.get("method") == "textDocument/publishDiagnostics":
                p = message["params"]
                self.diagnostics[p["uri"]] = p.get("diagnostics", [])
            if "method" in message and "id" in message:
                if message["method"] == "workspace/configuration":
                    answer = [None] * len(message.get("params", {}).get("items", []))
                else:
                    answer = None
                self.send({"jsonrpc": "2.0", "id": message["id"], "result": answer})
            if message.get("id") == ident and "method" not in message:
                if expect_error:
                    assert "error" in message, (method, message)
                    return message["error"]
                if "error" in message:
                    raise AssertionError((method, message["error"]))
                return message.get("result")
            if time.monotonic() > deadline:
                raise TimeoutError(f"Lean did not answer {method}")

    def sync(self, uri, version, *, errors=False):
        self.request("textDocument/waitForDiagnostics", {"uri": uri, "version": version})
        failures = [d for d in self.diagnostics.get(uri, []) if d.get("severity") == 1]
        if errors:
            assert failures, "invalid source attestation produced no error"
        else:
            assert not failures, failures
        return failures

    def open(self, uri, source, version=1):
        self.notify("textDocument/didOpen", {
            "textDocument": {"uri": uri, "languageId": "lean4", "version": version, "text": source},
            "dependencyBuildMode": "never"})
        self.sync(uri, version)

    def change(self, uri, source, version, *, errors=False):
        self.notify("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": version}, "contentChanges": [{"text": source}]})
        return self.sync(uri, version, errors=errors)

    def snapshot(self, uri, source, version, *, expect_error=False):
        session = self.request("$/lean/rpc/connect", {"uri": uri})["sessionId"]
        lines = source.splitlines()
        position = {"line": len(lines)-1, "character": max(0, len(lines[-1])-1)}
        reply = self.request("$/lean/rpc/call", {
            "textDocument": {"uri": uri}, "position": position, "sessionId": session,
            "method": "Macaulean.M2.Verification.Server.getSnapshot",
            "params": {"position": position, "version": version}}, expect_error=expect_error)
        if not expect_error:
            assert reply["documentVersion"] == version and reply["uri"] == uri
            assert reply["schema"] == "macaulean.semantic-snapshot.v1"
        return reply

    def close(self):
        try:
            if self.process.poll() is None:
                self.request("shutdown", None)
                self.notify("exit", None)
                self.process.wait(timeout=10)
        finally:
            if self.process.poll() is None:
                self.process.kill()
                self.process.wait(timeout=10)
            self.stderr.close()
            self.transcript.close()


def contract(snapshot):
    entries = snapshot["index"]["entries"]
    selected = [e for e in entries if e["name"] == "toyIdentity"]
    assert len(selected) == 1, entries
    assert selected[0]["sourceNodes"], "real elaboration did not retain nested source nodes"
    assert selected[0]["resolvedCode"], "resolved code missing from RPC inventory"
    cards = selected[0]["contracts"]
    assert len(cards) == 1, cards
    assert "Unattempted" in cards[0]["proofStatus"]
    return selected[0], cards[0]


BASE = '''import Macaulean.Verification
set_option maxRecDepth 40000
set_option maxHeartbeats 40000000
open M2
-- Synthetic LSP fixture only; λ, 中文 are source-position controls.
toyIdentity = p -> p;
#m2_contract "toyIdentity" polynomialIdentity
'''
STATUS = '#m2_status "toyIdentity" polynomialIdentity'
URI = (ROOT / "IntentRpcFixture.lean").as_uri()


def main():
    client = Client("edit")
    try:
        source = BASE + STATUS
        client.open(URI, source)
        initial = client.snapshot(URI, source, 1)
        entry, proposed = contract(initial)
        assert proposed["status"].startswith("Proposed")
        assert initial["index"]["eventCount"] == 0
        again = client.snapshot(URI, source, 1)
        assert again == initial, "read-only RPC mutated the environment"
        approved_source = BASE + proposed["approveCommand"] + STATUS
        client.change(URI, approved_source, 2)
        approved = client.snapshot(URI, approved_source, 2)
        _, card = contract(approved)
        assert card["status"] == "Intent approved by source attestation", card
        assert approved["index"]["eventCount"] == 1
        assert card["digest"] == proposed["digest"]

        stale_source = approved_source + '\nother = 1;\n' + STATUS
        client.change(URI, stale_source, 3)
        _, stale = contract(client.snapshot(URI, stale_source, 3))
        assert stale["status"].startswith("Stale"), stale
        rejected = client.snapshot(URI, stale_source, 2, expect_error=True)
        assert "version changed" in rejected["message"], rejected

        changed = approved_source.replace('toyIdentity = p -> p;', 'toyIdentity = p -> p+1;')
        failures = client.change(URI, changed, 4, errors=True)
        assert any("approval fingerprint" in d["message"] for d in failures), failures
        _, changed_card = contract(client.snapshot(URI, changed, 4))
        assert changed_card["status"] != "Intent approved by source attestation"
        assert changed_card["digest"] != proposed["digest"]

        # The original literal approval replays after a nonsemantic edit.
        comments = approved_source.replace('toyIdentity = p -> p;', '-- added comment\ntoyIdentity = p -> (p);')
        client.change(URI, comments, 5)
        replay_entry, replay = contract(client.snapshot(URI, comments, 5))
        assert replay_entry["id"] == entry["id"]
        assert replay["digest"] == proposed["digest"]
        assert replay["status"] == "Intent approved by source attestation"

        revoked_source = comments + '\n' + replay["revokeCommand"] + STATUS
        client.change(URI, revoked_source, 6)
        _, revoked = contract(client.snapshot(URI, revoked_source, 6))
        assert revoked["status"] == "Intent approval revoked"
        print("INTENT_LSP_EDITS_COMPLETE: real source approval, stale state, stale version, code edits, comments and revocation", flush=True)
    finally:
        client.close()

    # A new process must reconstruct the approval solely from the source file.
    restarted = Client("restart")
    try:
        restarted.open(URI, approved_source)
        _, replay = contract(restarted.snapshot(URI, approved_source, 1))
        assert replay["digest"] == proposed["digest"]
        assert replay["status"] == "Intent approved by source attestation"
        other_uri = (ROOT / "IntentRpcOther.lean").as_uri()
        fresh = BASE + STATUS
        restarted.open(other_uri, fresh)
        other_entry, other = contract(restarted.snapshot(other_uri, fresh, 1))
        assert other_entry["id"] != entry["id"]
        assert other["status"].startswith("Proposed")
        print("INTENT_LSP_REPLAY_COMPLETE: fresh-process source replay and document isolation", flush=True)
    finally:
        restarted.close()


if __name__ == "__main__":
    main()
