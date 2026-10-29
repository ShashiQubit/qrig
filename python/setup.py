"""Build hook: compile the Lean-generated C core if the binaries are not present yet."""
from __future__ import annotations

import os
import subprocess
import sys

from setuptools import setup
from setuptools.command.build_py import build_py

HERE = os.path.dirname(os.path.abspath(__file__))


class BuildWithNative(build_py):
    def run(self):
        exe_candidates = [
            os.path.join(HERE, "qrig", "_bin", "qrig-core"),
            os.path.join(HERE, "qrig", "_bin", "qrig-core.exe"),
        ]
        if not any(os.path.exists(p) for p in exe_candidates):
            # Recompile from the committed generated C (needs a Lean toolchain for
            # lean.h and the runtime libraries, but not the Lean sources).
            subprocess.check_call([
                sys.executable,
                os.path.join(HERE, "build_native.py"),
                "--no-lake",
            ])
        super().run()


cmdclass = {"build_py": BuildWithNative}

try:
    from wheel.bdist_wheel import bdist_wheel as _bdist_wheel
except ImportError:
    try:
        from setuptools.command.bdist_wheel import bdist_wheel as _bdist_wheel
    except ImportError:
        _bdist_wheel = None

if _bdist_wheel is not None:
    class bdist_wheel(_bdist_wheel):
        def finalize_options(self):
            super().finalize_options()
            # Mark wheel as platform-specific because it bundles native binary
            self.root_is_pure = False

        def get_tag(self):
            # ABI-independent: works across any Python 3.9+ interpreter on the target OS/architecture
            _, _, plat = super().get_tag()
            plat_override = os.environ.get("QRIG_PLAT_NAME")
            if plat_override:
                plat = plat_override
            elif plat.startswith("linux_x86_64"):
                plat = "manylinux2014_x86_64"
            elif plat.startswith("linux_aarch64"):
                plat = "manylinux2014_aarch64"
            return "py3", "none", plat

    cmdclass["bdist_wheel"] = bdist_wheel


setup(cmdclass=cmdclass)
