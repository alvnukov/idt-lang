from __future__ import annotations

import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

PIPELINE = (
    ("python3", "-m", "theory_verifier", "--json", "theory_verifier_manifest.json"),
    ("python3", "scripts/check_proofs.py"),
    ("python3", "-m", "unittest", "discover", "-s", "tests"),
)


def main() -> int:
    for command in PIPELINE:
        print("$ " + " ".join(command))
        completed = subprocess.run(command, cwd=ROOT, check=False)
        if completed.returncode != 0:
            return completed.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
