#!/usr/bin/env bash
# Run the checks that require a local Lean toolchain and collect one report.
#
# Written because the audit environment has no `lake`: everything in
# INVENTORY_AUDIT.md section 9 that needs a compiler has to run here.
#
# Read-only with respect to tracked sources. It compiles, runs tests and
# evaluators, and writes a single report file. It does not edit or commit.
#
# Usage:
#     bash scripts/audit_build_status.sh [OUTPUT]
#
# Default OUTPUT is build_status_report.txt in the repository root.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${1:-$ROOT/build_status_report.txt}"
cd "$ROOT" || exit 1

: > "$OUT"

section() {
  {
    echo
    echo "=============================================================="
    echo "== $1"
    echo "=============================================================="
  } | tee -a "$OUT"
}

run() {
  local label="$1"; shift
  section "$label"
  echo "\$ $*" | tee -a "$OUT"
  "$@" 2>&1 | tee -a "$OUT"
  local status=${PIPESTATUS[0]}
  echo "[exit $status]" | tee -a "$OUT"
  return "$status"
}

{
  echo "IDT build status report"
  echo "date    : $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  echo "commit  : $(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
  echo "branch  : $(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)"
  echo "lean    : $(lean --version 2>/dev/null || echo 'NOT FOUND')"
  echo "lake    : $(lake --version 2>/dev/null || echo 'NOT FOUND')"
} | tee -a "$OUT"

if ! command -v lake >/dev/null 2>&1; then
  section "ABORT"
  echo "lake not on PATH; run this on a machine with the Lean toolchain" \
    | tee -a "$OUT"
  exit 2
fi

# 1. Does everything actually compile? Until 2026-07-27 this was vacuous: the
#    lakefile had no default_target, so `lake build` reported success without
#    compiling anything. See INVENTORY_AUDIT.md section 10.1.
run "lake build" lake build

# 2. Vacuous-theorem policy: every theorem asserting True must be declared.
run "vacuous theorem check" python3 scripts/check_vacuous_theorems.py
run "vacuous theorem inventory" python3 scripts/check_vacuous_theorems.py --report

# 3. Python test suite, including the rewritten forbidden-import scan tests.
if python3 -c "import pytest" >/dev/null 2>&1; then
  run "pytest" python3 -m pytest tests -q
else
  run "unittest" python3 -m unittest discover -s tests -q
fi

# 4. Three of the five formerly machine-checked cards are flagged for a
#    hand-built complex sesquilinear structure, so this exits 1 by design.
run "full QM proof closure" python3 scripts/evaluate_full_qm_proof_closure.py

section "SUMMARY"
{
  echo "Report written to: $OUT"
  echo
  echo "What to look for:"
  echo "  * any lake build failure at all; the build is only meaningful"
  echo "    while lakefile.lean keeps @[default_target] on lean_lib Proofs"
  echo "  * whether 'proved' moved from 2, in either direction"
  echo "  * any test failure that is NOT a temp-file cleanup error"
  echo
  echo "If 'proved' moved, README.md and PUBLIC_CLAIM_SHEET.md item 23"
  echo "need to be updated to match."
} | tee -a "$OUT"
