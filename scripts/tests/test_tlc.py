"""The TLC driver keeps sanitizer preloads out of the JVM.

The generated-C sanitizer run (docs/testing.md section 11) preloads the Clang
ASan runtime into the driver; a JVM that inherits it crashes on its own signal
handling and alternate signal stack, so every TLC launch must drop it.
"""
import os
import unittest
from unittest.mock import patch

import tlc
from harness.process import ProcResult


class JvmEnvironment(unittest.TestCase):
    def test_strips_preloads_from_an_environment(self):
        env = tlc.jvm_env({
            "LD_PRELOAD": "/asan/libclang_rt.asan-x86_64.so",
            "DYLD_INSERT_LIBRARIES": "/asan/libclang_rt.asan_osx_dynamic.dylib",
            "PATH": "/bin",
        })
        self.assertEqual(env, {"PATH": "/bin"})
        self.assertEqual(tlc.PRELOAD_VARS, ("LD_PRELOAD", "DYLD_INSERT_LIBRARIES"))

    def test_defaults_to_the_process_environment(self):
        with patch.dict(os.environ, {"LD_PRELOAD": "/asan/libclang_rt.asan.so", "TLX_JAVA": "java"}, clear=True):
            self.assertEqual(tlc.jvm_env(), {"TLX_JAVA": "java"})

    def test_tlc_runs_do_not_inherit_preloads(self):
        commands = []

        def run(cmd, **kwargs):
            commands.append((cmd, kwargs))
            return ProcResult("", "", 0, 0.0)

        with patch.object(tlc, "run_proc", side_effect=run), \
                patch.object(tlc, "check_tlc_model"), \
                patch.dict(os.environ, {"LD_PRELOAD": "/asan/libclang_rt.asan.so",
                                        "DYLD_INSERT_LIBRARIES": "/asan/libclang_rt.asan.dylib"}):
            out, rc, wall = tlc.run_tlc_raw("Model.tla", [])
        self.assertEqual((out, rc, wall), ("", 0, 0.0))
        self.assertEqual(len(commands), 1)
        _, kwargs = commands[0]
        self.assertNotIn("LD_PRELOAD", kwargs["env"])
        self.assertNotIn("DYLD_INSERT_LIBRARIES", kwargs["env"])


if __name__ == "__main__":
    unittest.main()
