#!/usr/bin/env python3
"""Require every native case and all original aggregate observations."""
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "compatibility"))
import coverage_ledger as coverage
import prior_contracts as prior
import task10_relocation as relocation
import task26_relocation as physical
from run_paired import require


def validate(text):
    ledger = coverage.receipt(relocation.LEDGER)
    supplement = relocation.load()
    coverage.verify(ledger, supplement)
    relocation.validate_stream(ledger, "native", prior.semantic_stream(text),
                               supplement)
    physical.validate_vectors(text)


def main():
    completed = subprocess.run([str(HERE / "selftest.exe")], cwd=HERE,
                               stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True,
                               timeout=300)
    print(completed.stdout, end="")
    require(completed.returncode == 0, "native launcher failed")
    validate(completed.stdout)
    print("Native coverage: 630 original + 12 registry checks; 11 vectors")


if __name__ == "__main__":
    main()
