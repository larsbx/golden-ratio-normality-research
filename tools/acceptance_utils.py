"""Small shared helpers for observable, fail-closed acceptance commands."""
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
CONTRACT = json.loads((ROOT / "research-contract.json").read_text())


def validated_intervals(contract=CONTRACT):
    """Resolve interval fixtures without accepting vacuous or mismatched cases."""
    intervals = []
    cases = contract["prefix_cases"]
    for entry in contract["interval_cases"]:
        if not isinstance(entry, dict) or set(entry) != {"lower_case", "upper_case", "tolerance"}:
            raise ValueError("invalid interval fields")
        lower, upper, tolerance = (entry[key] for key in ("lower_case", "upper_case", "tolerance"))
        if any(type(value) is not int for value in (lower, upper, tolerance)):
            raise ValueError("interval indices and tolerance must be integers")
        if not (0 <= lower < len(cases) and 0 <= upper < len(cases)):
            raise ValueError("interval references a missing prefix case")
        if tolerance < 1:
            raise ValueError("interval tolerance must be positive")
        b, lower_length, width = cases[lower]
        upper_b, upper_length, upper_width = cases[upper]
        if (b, width) != (upper_b, upper_width):
            raise ValueError("interval endpoints must share a base and block width")
        lower_starts, upper_starts = lower_length + 1 - width, upper_length + 1 - width
        if not 1 <= lower_starts <= upper_starts:
            raise ValueError("interval starts must be positive and ordered")
        intervals.append({**entry, "base": b, "width": width,
                          "lower_length": lower_length, "upper_length": upper_length,
                          "lower_starts": lower_starts, "upper_starts": upper_starts})
    return intervals


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def command(args, log, *, env=None, timeout=600, expect_success=True, cwd=ROOT):
    """A timeout is an exception, never an expected negative result."""
    args = [str(arg) for arg in args]
    started = time.monotonic()
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    metadata = {"command": args, "returncode": result.returncode,
                "seconds": round(time.monotonic() - started, 3),
                "stdout": result.stdout, "stderr": result.stderr}
    write_json(log, metadata)
    if expect_success and result.returncode != 0:
        raise RuntimeError(f"command failed ({result.returncode}); see {log}\n"
                           + result.stdout[-3000:] + result.stderr[-3000:])
    return result


def git_output(*args, cwd=ROOT):
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


def verify_submodule():
    path = ROOT / "vendor/finite-math-kernels"
    actual = git_output("rev-parse", "HEAD", cwd=path)
    if actual != CONTRACT["finite_math_kernels_revision"]:
        raise RuntimeError("finite-math-kernels revision differs from research contract")
    if git_output("status", "--porcelain", "--untracked-files=no", cwd=path):
        raise RuntimeError("finite-math-kernels has modified tracked sources")
    return actual


def source_hashes():
    """Include tracked and untracked nonignored inputs; exclude evidence reports."""
    raw = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"], cwd=ROOT)
    result = {}
    for name in sorted(set(raw.decode().split("\0"))):
        if not name or name.startswith(("evidence/", "vendor/")):
            continue
        path = ROOT / name
        if path.is_file():
            result[name] = digest(path)
    return result


def locate_program(variable, fallback, candidate=None):
    import shutil
    value = os.environ.get(variable) or shutil.which(fallback)
    if not value and candidate and Path(candidate).is_file():
        value = str(candidate)
    if not value:
        raise RuntimeError(f"missing {fallback}; install the pinned toolchain or set {variable}")
    # Keep an elan/pixi multicall symlink's invocation name intact.
    return str(Path(value).absolute())
