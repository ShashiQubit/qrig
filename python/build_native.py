#!/usr/bin/env python3
"""Build the native core of the ``qrig`` Python package from the verified Lean sources.

Steps
-----
1. ``lake build Qrig``   -- type-check the Lean sources and let the Lean compiler emit C
                            (``.lake/build/ir/Qrig/**/*.c``).
2. copy the generated C files to ``python/csrc/generated/`` (they are committed, so the
   package can be rebuilt from C alone).
3. compile
     * ``qrig/_bin/qrig-core`` (or .exe on Windows) : a self-contained executable
       (Lean runtime linked statically); used by the default "process" backend;
     * ``qrig/_bin/libqrig.so`` (.dylib/.dll) : an in-process shared library linked against
       the Lean toolchain runtime; used by the faster "inproc" backend.

Usage:  python build_native.py [--no-lake] [--toolchain PATH]
"""
from __future__ import annotations

import argparse
import glob
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
GEN = os.path.join(HERE, "csrc", "generated")
BIN = os.path.join(HERE, "qrig", "_bin")

IS_WIN = sys.platform == "win32"
IS_MAC = sys.platform == "darwin"
IS_LINUX = sys.platform.startswith("linux")


def find_toolchain(explicit: str | None) -> str:
    if explicit:
        return explicit
    env = os.environ.get("LEAN_TOOLCHAIN")
    if env and os.path.isdir(env):
        return env
    try:
        prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT, text=True).strip()
        if prefix and os.path.isdir(prefix):
            return prefix
    except (OSError, subprocess.CalledProcessError):
        pass
    tc_file = os.path.join(ROOT, "lean-toolchain")
    if os.path.exists(tc_file):
        with open(tc_file) as f:
            tc = f.read().strip().replace("/", "--").replace(":", "---")
        candidate = os.path.expanduser(os.path.join("~", ".elan", "toolchains", tc))
        if os.path.isdir(candidate):
            return candidate
    # Fallback to any installed toolchain in .elan/toolchains if available
    toolchains_dir = os.path.expanduser(os.path.join("~", ".elan", "toolchains"))
    if os.path.isdir(toolchains_dir):
        for name in sorted(os.listdir(toolchains_dir), reverse=True):
            p = os.path.join(toolchains_dir, name)
            if os.path.isdir(p) and os.path.exists(os.path.join(p, "include", "lean", "lean.h")):
                return p
    return os.path.expanduser(os.path.join("~", ".elan", "toolchains", "leanprover--lean4---v4.28.0"))


def run(cmd, **kw):
    print("+", " ".join(cmd), flush=True)
    subprocess.check_call(cmd, **kw)


def _find_lib(tc: str, name: str) -> str:
    """Find a library archive in $tc/lib/lean or $tc/lib."""
    for sub in ("lean", ""):
        p = os.path.join(tc, "lib", sub, name) if sub else os.path.join(tc, "lib", name)
        if os.path.exists(p):
            return p
    return os.path.join(tc, "lib", name)


def main() -> int:
    default_cc = os.environ.get("CC")
    if not default_cc:
        if IS_WIN:
            default_cc = "gcc"
        elif IS_MAC:
            default_cc = "clang"
        else:
            default_cc = "cc"

    ap = argparse.ArgumentParser()
    ap.add_argument("--no-lake", action="store_true", help="skip 'lake build', reuse generated C")
    ap.add_argument("--toolchain", default=None, help="path of the Lean toolchain")
    ap.add_argument("--cc", default=default_cc)
    args = ap.parse_args()

    tc = find_toolchain(args.toolchain)
    inc = os.path.join(tc, "include")
    if not os.path.exists(os.path.join(inc, "lean", "lean.h")):
        print(f"error: Lean toolchain not found at {tc}", file=sys.stderr)
        return 1

    if not args.no_lake:
        run(["lake", "build", "Qrig"], cwd=ROOT)
        ir = os.path.join(ROOT, ".lake", "build", "ir", "Qrig")
        if os.path.isdir(GEN):
            shutil.rmtree(GEN)
        os.makedirs(GEN)
        for src in glob.glob(os.path.join(ir, "**", "*.c"), recursive=True):
            rel = os.path.relpath(src, ir).replace(os.sep, "_")
            shutil.copy(src, os.path.join(GEN, "Qrig_" + rel))

    gen_c = sorted(glob.glob(os.path.join(GEN, "*.c")))
    if not gen_c:
        print("error: no generated C files", file=sys.stderr)
        return 1
    os.makedirs(BIN, exist_ok=True)
    csrc = os.path.join(HERE, "csrc")
    shim = os.path.join(csrc, "qrig_shim.c")
    main_c = os.path.join(csrc, "qrig_main.c")
    flags = ["-O2", "-w", "-I", inc]

    # Static runtime archives from Lean
    static_libs = [
        _find_lib(tc, "libInit.a"),
        _find_lib(tc, "libleanrt.a"),
        _find_lib(tc, "libuv.a"),
        _find_lib(tc, "libgmp.a"),
        _find_lib(tc, "libc++.a"),
        _find_lib(tc, "libc++abi.a"),
    ]

    # OS-specific link flags
    if IS_WIN:
        sys_flags = [
            "-lws2_32", "-lbcrypt", "-luserenv", "-lpsapi", "-liphlpapi",
            "-ldbghelp", "-lole32", "-lshell32", "-luser32", "-ladvapi32", "-lm"
        ]
        exe_name = "qrig-core.exe"
        so_name = "libqrig.dll"
    elif IS_MAC:
        sys_flags = ["-lpthread", "-lm"]
        exe_name = "qrig-core"
        so_name = "libqrig.dylib"
    else:  # Linux / POSIX
        sys_flags = ["-lpthread", "-ldl", "-lm", "-s"]
        exe_name = "qrig-core"
        so_name = "libqrig.so"

    # 1. self-contained executable
    exe = os.path.join(BIN, exe_name)
    run([args.cc, *flags, main_c, shim, *gen_c, "-o", exe, *static_libs, *sys_flags])

    # 2. optional in-process shared library
    shared_candidate = None
    for cand in ("libleanshared.so", "libleanshared.dylib", "libleanshared.dll"):
        p = _find_lib(tc, cand)
        if os.path.exists(p):
            shared_candidate = p
            break
        p_bin = os.path.join(tc, "bin", cand)
        if os.path.exists(p_bin):
            shared_candidate = p_bin
            break

    if shared_candidate:
        so = os.path.join(BIN, so_name)
        shared_dir = os.path.dirname(shared_candidate)
        shared_flags = ["-shared", "-fPIC", shim, *gen_c, "-o", so,
                        f"-L{shared_dir}", "-lleanshared"]
        if not IS_WIN:
            shared_flags.append(f"-Wl,-rpath,{shared_dir}")
        try:
            run([args.cc, *flags, *shared_flags])
        except subprocess.CalledProcessError:
            print("warning: could not build the in-process library; "
                  "the process backend will be used", file=sys.stderr)
    print("done:", os.listdir(BIN))
    return 0


if __name__ == "__main__":
    sys.exit(main())
