"""Protocol and isolation-policy tests, not substitutes for Lean kernel tests."""
from __future__ import annotations
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import m2_proof_jobs as p


def raw(value):
    return json.dumps(value, ensure_ascii=False).encode()


def job():
    return {"format": p.JOB_FORMAT, "jobId": "a"*64, "bindingId": "b"*64,
            "bindingName": "f", "schema": "polynomialIdentity", "approvalSource": "SYNTHETIC TEST ONLY",
            "approvalDigest": "a"*64, "theoryDigest": "c"*64, "leanVersion": "4.33.1",
            "targetKey": "exact-constructor-payload", "target": [1, [0]]}


def proof(j=None):
    j = j or job()
    return {"format": p.PROOF_FORMAT, "jobId": j["jobId"], "targetKey": j["targetKey"], "term": [7, 0]}


def receipt(j=None):
    j = j or job()
    return {"format": p.RECEIPT_FORMAT, "jobId": j["jobId"], "targetKey": j["targetKey"],
            "proofKey": "d"*64, "theoryDigest": j["theoryDigest"], "theoremName": "syntheticTest",
            "theoremRef": [1, [0], "syntheticTest"], "axioms": [], "leanVersion": j["leanVersion"],
            "status": "kernel-checked"}


class Packets(unittest.TestCase):
    def test_job_roundtrip(self):
        self.assertEqual(p.parse_job(raw(job())), job())

    def test_no_authority_from_name(self):
        value = job(); value["approvalSource"] = ""
        with self.assertRaises(p.JobError): p.parse_job(raw(value))

    def test_missing_target(self):
        value = job(); value.pop("target")
        with self.assertRaises(p.JobError): p.parse_job(raw(value))

    def test_extra_success_flag(self):
        value = job(); value["verified"] = True
        with self.assertRaises(p.JobError): p.parse_job(raw(value))

    def test_wrong_revision(self):
        value = job(); value["jobId"] = "e"*64
        with self.assertRaises(p.JobError): p.parse_job(raw(value))

    def test_path_as_job_id(self):
        value = job(); value["jobId"] = "../../elsewhere"
        with self.assertRaises(p.JobError): p.parse_job(raw(value))

    def test_unknown_schema(self):
        value = job(); value["schema"] = "alwaysTrue"
        with self.assertRaises(p.JobError): p.parse_job(raw(value))

    def test_schema_is_not_object(self):
        value = job(); value["schema"] = {}
        with self.assertRaises(p.JobError): p.parse_job(raw(value))

    def test_wrong_protocol(self):
        value = job(); value["format"] = "v2"
        with self.assertRaises(p.JobError): p.parse_job(raw(value))

    def test_duplicate_key(self):
        source = raw(job()).replace(b'"format":', b'"jobId":"fake", "format":')
        with self.assertRaises(p.JobError): p.parse_job(source)

    def test_invalid_json_constant(self):
        source = raw(job()).replace(b'"target": [1, [0]]', b'"target": NaN')
        with self.assertRaises(p.JobError): p.parse_job(source)

    def test_invalid_utf8(self):
        with self.assertRaises(p.JobError): p.parse_job(b'\xff')

    def test_empty_object_not_success(self):
        with self.assertRaises(p.JobError): p.parse_job(b'{}')

    def test_empty_input_not_success(self):
        with self.assertRaises(p.JobError): p.parse_job(b'')

    def test_oversize(self):
        with self.assertRaises(p.JobError): p.parse_job(b' '*(p.MAX_PACKET+1))

    def test_two_packets_not_success(self):
        with self.assertRaises(p.JobError): p.parse_job(raw(job()) + raw(job()))

    def test_proof_roundtrip(self):
        self.assertEqual(p.parse_proof(raw(proof()), job()), proof())

    def test_proof_wrong_goal(self):
        value = proof(); value["targetKey"] = "True"
        with self.assertRaises(p.JobError): p.parse_proof(raw(value), job())

    def test_proof_wrong_job(self):
        value = proof(); value["jobId"] = "e"*64
        with self.assertRaises(p.JobError): p.parse_proof(raw(value), job())

    def test_proof_rejects_tactic_text(self):
        value = proof(); value["term"] = "by trivial"
        with self.assertRaises(p.JobError): p.parse_proof(raw(value), job())

    def test_proof_extra_helper_declarations(self):
        value = proof(); value["declarations"] = ["axiom P : False"]
        with self.assertRaises(p.JobError): p.parse_proof(raw(value), job())

    def test_receipt_roundtrip_is_only_protocol(self):
        self.assertEqual(p.parse_receipt(raw(receipt()), job()), receipt())

    def test_sorry_receipt(self):
        value = receipt(); value["axioms"] = ["sorryAx"]
        with self.assertRaises(p.JobError): p.parse_receipt(raw(value), job())

    def test_native_decide_receipt(self):
        value = receipt(); value["axioms"] = ["Lean.ofReduceBool"]
        with self.assertRaises(p.JobError): p.parse_receipt(raw(value), job())

    def test_new_axiom_receipt(self):
        value = receipt(); value["axioms"] = ["worker.myLemma"]
        with self.assertRaises(p.JobError): p.parse_receipt(raw(value), job())

    def test_nonstring_axiom(self):
        value = receipt(); value["axioms"] = [{}]
        with self.assertRaises(p.JobError): p.parse_receipt(raw(value), job())

    def test_receipt_requires_complete_status(self):
        value = receipt(); value["status"] = "partial"
        with self.assertRaises(p.JobError): p.parse_receipt(raw(value), job())

    def test_receipt_context_fields_match(self):
        for key in ("jobId", "targetKey", "theoryDigest", "leanVersion"):
            with self.subTest(key=key):
                value = receipt(); value[key] = "changed"
                with self.assertRaises(p.JobError): p.parse_receipt(raw(value), job())

    def test_receipt_requires_theorem(self):
        value = receipt(); value["theoremName"] = ""
        with self.assertRaises(p.JobError): p.parse_receipt(raw(value), job())


class Files(unittest.TestCase):
    def test_immutable_write(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp)/"evidence.json"
            p.write_once(path, b"a"); p.write_once(path, b"a")
            with self.assertRaises(p.JobError): p.write_once(path, b"b")
            self.assertEqual(path.read_bytes(), b"a")

    def test_symlink_read_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); (root/"target").write_bytes(b"secret")
            (root/"link").symlink_to(root/"target")
            with self.assertRaises(OSError): p.read_regular(root/"link")

    def test_nonregular_read_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaises(p.JobError): p.read_regular(Path(temp))

    def test_bounded_read(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/"large"; path.write_bytes(b"1234")
            with self.assertRaises(p.JobError): p.read_regular(path, 3)

    def test_missing_output_is_not_pass(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            with self.assertRaises(OSError): p.RunResult(0,False,root/"absent",root/"err").checked_output()

    def test_failed_process_cannot_emit_success(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); (root/"stdout").write_bytes(raw(receipt()))
            with self.assertRaises(p.JobError): p.RunResult(1,False,root/"stdout",root/"err").checked_output()

    def test_timeout_even_if_exit_zero(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); (root/"stdout").write_bytes(raw(receipt()))
            with self.assertRaises(p.JobError): p.RunResult(0,True,root/"stdout",root/"err").checked_output()


class Isolation(unittest.TestCase):
    @staticmethod
    def project(root):
        (root/"Macaulean").mkdir(parents=True)
        (root/"Macaulean/A.lean").write_text("def x := 1")
        (root/".lake/build/lib/lean").mkdir(parents=True)
        (root/".lake/build/lib/lean/A.olean").write_bytes(b"synthetic-not-a-real-olean")
        (root/".git").mkdir(); (root/".git/config").write_text("SECRET-CREDENTIAL")
        return root

    def test_context_does_not_copy_git(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); project=self.project(root/"project")
            context=p.snapshot_context(project,root/"snapshot")
            self.assertFalse((context.root/".git").exists())
            self.assertEqual(context.digest,p.context_digest(p.context_files(project)))

    def test_context_detects_changed_source(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); project=self.project(root/"project")
            original=p.context_digest(p.context_files(project))
            (project/"Macaulean/A.lean").write_text("def x := 2")
            self.assertNotEqual(original,p.context_digest(p.context_files(project)))

    def test_context_detects_changed_olean(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); project=self.project(root/"project")
            original=p.context_digest(p.context_files(project))
            (project/".lake/build/lib/lean/A.olean").write_bytes(b"changed")
            self.assertNotEqual(original,p.context_digest(p.context_files(project)))

    def test_context_rejects_symlink(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); project=self.project(root/"project")
            (project/"Macaulean/secret.lean").symlink_to(project/".git/config")
            with self.assertRaises(p.JobError): p.context_files(project)

    def test_stale_job_not_published(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); project=self.project(root/"project")
            context=p.snapshot_context(project,root/"snapshot")
            manifest=root/"job.json"; original=raw(job()); manifest.write_bytes(original)
            p.assert_current(manifest,original,project,context)
            manifest.write_bytes(raw({**job(),"jobId":"e"*64}))
            with self.assertRaises(p.StaleJob): p.assert_current(manifest,original,project,context)

    def test_missing_sandbox_fails_closed(self):
        with tempfile.TemporaryDirectory() as temp, patch("shutil.which",return_value=None):
            with self.assertRaises(p.JobError): p.Sandbox(Path(temp))

    def test_namespace_mount_policy(self):
        with tempfile.TemporaryDirectory() as temp, patch("shutil.which",return_value="/usr/bin/bwrap"):
            root=Path(temp); (root/"toolchain/bin").mkdir(parents=True)
            (root/"toolchain/bin/lean").write_text("synthetic")
            sandbox=p.Sandbox(root/"toolchain")
            command=sandbox.command(p.Context(root/"snapshot","digest"),root/"inputs")
            self.assertIn("--unshare-all",command)
            self.assertIn("--clearenv",command)
            self.assertIn("--new-session",command)
            self.assertNotIn("--share-net",command)
            self.assertNotIn("--bind",command)
            self.assertNotIn("/home",command)
            self.assertNotIn("/root",command)
            self.assertEqual(command.count("--tmpfs"),2)
            self.assertEqual(command.count("--size"),2)
            self.assertIn("--root=/input", command[-1])

    def test_limits_are_positive(self):
        with self.assertRaises(ValueError): p.Limits(seconds=0)
        with self.assertRaises(ValueError): p.Limits(processes=0)


class Publication(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.destination = self.root / "checked" / "proof"
        self.files = {"target.json": raw(job()), "proof.json": raw(proof()),
                      "receipt.json": raw(receipt()), "context.sha256": b"c"*64}

    def tearDown(self):
        self.temp.cleanup()

    def publish(self):
        p.publish_evidence(self.destination, self.files, lambda: None)

    def test_complete_publication(self):
        self.publish()
        self.assertEqual(set(f.name for f in self.destination.iterdir()), set(self.files))
        for name, value in self.files.items():
            self.assertEqual((self.destination/name).read_bytes(), value)

    def test_identical_publication_is_idempotent(self):
        self.publish(); self.publish()

    def test_missing_receipt_is_not_success(self):
        self.publish(); (self.destination/"receipt.json").unlink()
        with self.assertRaises(p.JobError): self.publish()

    def test_corrupt_receipt_is_not_success(self):
        self.publish(); (self.destination/"receipt.json").write_bytes(b"forged")
        with self.assertRaises(p.JobError): self.publish()

    def test_corrupt_target_is_not_success(self):
        self.publish(); (self.destination/"target.json").write_bytes(b"other-target")
        with self.assertRaises(p.JobError): self.publish()

    def test_unexpected_sidecar_is_not_success(self):
        self.publish(); (self.destination/"verified.flag").write_text("true")
        with self.assertRaises(p.JobError): self.publish()

    def test_missing_manifest_component_rejected(self):
        self.files.pop("receipt.json")
        with self.assertRaises(p.JobError): self.publish()

    def test_symlink_destination_rejected(self):
        self.destination.parent.mkdir(); (self.root/"other").mkdir()
        self.destination.symlink_to(self.root/"other",target_is_directory=True)
        with self.assertRaises(p.JobError): self.publish()

    def test_stale_during_staging_not_published(self):
        calls = []
        def recheck():
            calls.append(True)
            if len(calls) == 2: raise p.StaleJob("edited")
        with self.assertRaises(p.StaleJob): p.publish_evidence(self.destination,self.files,recheck)
        self.assertFalse(self.destination.exists())
        self.assertEqual(list(self.destination.parent.iterdir()), [])

    def test_race_checks_entire_winner(self):
        real_rename = p.rename_no_replace
        def race(source,dest):
            dest.mkdir()
            for name,value in self.files.items(): (dest/name).write_bytes(value)
            return real_rename(source,dest)
        with patch("m2_proof_jobs.rename_no_replace",side_effect=race): self.publish()
        for name,value in self.files.items(): self.assertEqual((self.destination/name).read_bytes(),value)

    def test_empty_racing_directory_is_not_overwritten(self):
        real_rename = p.rename_no_replace
        def race(source,dest):
            dest.mkdir(); return real_rename(source,dest)
        with patch("m2_proof_jobs.rename_no_replace",side_effect=race):
            with self.assertRaises(p.JobError): self.publish()
        self.assertTrue(self.destination.is_dir())
        self.assertEqual(list(self.destination.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
