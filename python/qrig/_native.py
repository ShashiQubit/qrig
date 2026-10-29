"""Access to the native (Lean-generated C) core of qrig.

Two interchangeable backends are provided:

* ``inproc``  -- ``_bin/libqrig.so`` is loaded with :mod:`ctypes` and called directly
  (requires the Lean runtime ``libleanshared.so``, i.e. a Lean installation);
* ``process`` -- the self-contained executable ``_bin/qrig-core`` (Lean runtime linked
  statically) is started once and spoken to through a pipe.

The backend is chosen with the environment variable ``QRIG_BACKEND``
(``inproc`` / ``process``); by default ``inproc`` is tried first.
"""
from __future__ import annotations

import atexit
import ctypes
import os
import subprocess
import sys
import threading

_BIN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "_bin")


class QrigError(RuntimeError):
    """Raised when the verified core reports an error (bad input, type error, ...)."""


class _InprocBackend:
    name = "inproc"

    def __init__(self, path: str):
        self.lib = ctypes.CDLL(path)
        self.lib.qrig_init.restype = ctypes.c_int
        self.lib.qrig_call_c.restype = ctypes.c_void_p
        self.lib.qrig_call_c.argtypes = [ctypes.c_char_p, ctypes.c_char_p]
        self.lib.qrig_free.argtypes = [ctypes.c_void_p]
        if self.lib.qrig_init() != 0:
            raise OSError("qrig: Lean runtime initialisation failed")
        self.lock = threading.Lock()

    def call(self, cmd: str, arg: str) -> str:
        with self.lock:
            p = self.lib.qrig_call_c(cmd.encode(), arg.encode())
            if not p:
                raise QrigError("native call failed")
            try:
                return ctypes.string_at(p).decode("utf-8", errors="replace")
            finally:
                self.lib.qrig_free(p)


class _ProcessBackend:
    name = "process"

    def __init__(self, path: str):
        self.path = path
        self.lock = threading.Lock()
        self.proc = None
        self._start()
        atexit.register(self.close)

    def _start(self):
        self.path = _ensure_executable(self.path)
        self.proc = subprocess.Popen([self.path], stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def call(self, cmd: str, arg: str) -> str:
        data = arg.encode()
        with self.lock:
            if self.proc is None or self.proc.poll() is not None:
                self._start()
            try:
                self.proc.stdin.write(cmd.encode() + b"\n" + str(len(data)).encode() + b"\n" + data)
                self.proc.stdin.flush()
                header = self.proc.stdout.readline()
                if not header:
                    raise QrigError("qrig-core terminated unexpectedly")
                n = int(header.strip())
                out = self.proc.stdout.read(n) if n else b""
            except (BrokenPipeError, ValueError, OSError) as e:
                self.proc = None
                raise QrigError(f"communication with qrig-core failed: {e}") from e
        return out.decode("utf-8", errors="replace")

    def close(self):
        if self.proc is not None and self.proc.poll() is None:
            try:
                self.proc.stdin.close()
                self.proc.wait(timeout=5)
            except Exception:  # pragma: no cover
                self.proc.kill()
        self.proc = None


def _ensure_executable(path: str) -> str:
    """Return an executable path for ``path``, restoring a lost executable bit
    (e.g. after a checkout or an unzip)."""
    if sys.platform == "win32":
        return path
    if os.access(path, os.X_OK):
        return path
    try:
        os.chmod(path, os.stat(path).st_mode | 0o111)
        return path
    except OSError:  # read-only install: fall back to a private executable copy
        import shutil
        import tempfile
        ext = os.path.splitext(path)[1]
        tmp = os.path.join(tempfile.mkdtemp(prefix="qrig-"), f"qrig-core{ext}")
        shutil.copyfile(path, tmp)
        os.chmod(tmp, 0o755)
        return tmp


def _find_library() -> str | None:
    if sys.platform == "win32":
        candidates = ["libqrig.dll", "qrig.dll", "libqrig.so"]
    elif sys.platform == "darwin":
        candidates = ["libqrig.dylib", "libqrig.so"]
    else:
        candidates = ["libqrig.so"]
    for name in candidates:
        p = os.path.join(_BIN, name)
        if os.path.exists(p):
            return p
    return None


def _find_executable() -> str | None:
    if sys.platform == "win32":
        candidates = ["qrig-core.exe", "qrig-core"]
    else:
        candidates = ["qrig-core", "qrig-core.exe"]
    for name in candidates:
        p = os.path.join(_BIN, name)
        if os.path.exists(p):
            return p
    return None


_backend = None


def _make_backend():
    choice = os.environ.get("QRIG_BACKEND", "").strip().lower()
    so = _find_library()
    exe = _find_executable()
    errors = []
    if choice in ("", "inproc") and so is not None:
        try:
            return _InprocBackend(so)
        except OSError as e:
            errors.append(f"inproc: {e}")
            if choice == "inproc":
                raise
    if choice in ("", "process") and exe is not None:
        return _ProcessBackend(exe)
    raise ImportError("qrig: no native backend available; run python/build_native.py "
                      + "; ".join(errors))


def backend():
    global _backend
    if _backend is None:
        _backend = _make_backend()
    return _backend


def call(cmd: str, arg: str = "") -> str:
    """Call the verified core; raise :class:`QrigError` on reported errors."""
    out = backend().call(cmd, arg)
    if out.startswith("ERR: "):
        raise QrigError(out[5:])
    return out
