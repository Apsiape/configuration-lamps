"""Run every check of this repository and report the results.

Usage: python verification/run_all.py
Exits with status 0 only if every check passes. Each check prints its own details.
"""
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CHECKS = ["relators1d_check.py", "relators_check.py", "ladder_check.py", "embedding3v_check.py", "choi_rank_check.py"]


def main():
    failed = []
    for name in CHECKS:
        print(f"== {name}", flush=True)
        result = subprocess.run([sys.executable, name], cwd=HERE, timeout=1800)
        if result.returncode != 0:
            failed.append(name)
    print()
    for name in CHECKS:
        print(("FAIL  " if name in failed else "pass  ") + name)
    if failed:
        sys.exit(1)
    print("All checks passed. They are finite regressions; the general statements are proved in the manuscript.")


if __name__ == "__main__":
    main()
