"""Startup-policy regressions; real Lean execution remains a separate CI gate."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from m2_proof_jobs import Context, Limits, Sandbox


class WorkerStartupTests(unittest.TestCase):
    def command(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "bin").mkdir()
            (root / "bin/lean").write_text("fixture, never executed")
            with patch("m2_proof_jobs.shutil.which", return_value="/usr/bin/bwrap"), \
                 patch("m2_proof_jobs.sys.platform", "linux"):
                return Sandbox(root).command(Context(root / "context", "fixture"), root / "input")

    def test_early_stack_and_runtime_thread_environment(self):
        cmd = self.command()
        settings = {cmd[i + 1]: cmd[i + 2] for i, token in enumerate(cmd) if token == "--setenv"}
        self.assertEqual(settings["LEAN_NUM_THREADS"], "1")
        self.assertEqual(settings["LEAN_STACK_SIZE_KB"], "65536")
        self.assertEqual(settings["LEAN_PATH"], "/project/.lake/build/lib/lean")

    def test_shell_does_not_override_with_cpu_count_defaults(self):
        launch = self.command()[-1]
        self.assertIn("/toolchain/bin/lean -j1 -s65536 ", launch)
        self.assertIn("-DmaxRecDepth=32768", launch)
        self.assertIn("/input/Run.lean >&2", launch)
        self.assertTrue(launch.endswith("exec /bin/cat /work/result.json"))

    def test_memory_and_cpu_limits_are_not_removed(self):
        limits = Limits()
        self.assertEqual(limits.memory_bytes, 16 * 1024**3)
        with patch("m2_proof_jobs.resource.setrlimit") as set_limit:
            limits.install()
        import resource
        calls = {args[0]: args[1] for args, _ in set_limit.call_args_list}
        self.assertEqual(calls[resource.RLIMIT_AS], (limits.memory_bytes, limits.memory_bytes))
        self.assertEqual(calls[resource.RLIMIT_CPU], (limits.seconds, limits.seconds))
        self.assertEqual(calls[resource.RLIMIT_FSIZE], (limits.disk_bytes, limits.disk_bytes))
        self.assertEqual(calls[resource.RLIMIT_NPROC], (limits.processes, limits.processes))

    def test_explicit_smaller_budget_is_honored(self):
        import resource
        limit = 2 * 1024**3
        with patch("m2_proof_jobs.resource.setrlimit") as set_limit:
            Limits(memory_bytes=limit).install()
        set_limit.assert_any_call(resource.RLIMIT_AS, (limit, limit))
        with self.assertRaises(ValueError):
            Limits(memory_bytes=-1)

    def test_network_and_environment_isolation_survive_startup_fix(self):
        cmd = self.command()
        for flag in ("--unshare-all", "--clearenv", "--die-with-parent", "--new-session"):
            self.assertIn(flag, cmd)
        self.assertNotIn("--share-net", cmd)
        self.assertNotIn("--bind", cmd)
        self.assertEqual(cmd.count("--tmpfs"), 2)


if __name__ == "__main__":
    unittest.main()
