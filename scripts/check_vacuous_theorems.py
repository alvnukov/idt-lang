#!/usr/bin/env python3
"""Detect Lean theorems that assert nothing.

A theorem whose conclusion is ``True`` -- directly, or through a definition
declared as ``def X ... : Prop := True`` -- carries no information regardless of
how it is proved. Such artifacts are indistinguishable from proofs when read by
a human or by an agent, and they have historically been cited in this repository
as evidence (see ``INVENTORY_AUDIT.md``).

Policy enforced here:

* a file containing at least one vacuous theorem must declare
  ``EMPTY_PLACEHOLDER`` in its header;
* a file declaring ``EMPTY_PLACEHOLDER`` must actually contain a vacuous
  theorem, so the marker cannot rot into decoration.

Exit code 0 when the policy holds, 1 otherwise.

Usage:
    python3 scripts/check_vacuous_theorems.py [--root DIR] [--report]
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

MARKER = "EMPTY_PLACEHOLDER"

DECL = re.compile(
    r"^(theorem|lemma|def|structure|inductive|abbrev|axiom|instance|example)"
    r"\s+([^\s:(\[{]+)",
    re.M,
)
PROP_TRUE_ALIAS = re.compile(r"^def\s+([^\s:(\[{]+)[^:\n]*:\s*Prop\s*:=\s*True\s*$", re.M)
ARROW = re.compile(r"→|->")


@dataclass
class FileReport:
    path: Path
    total: int = 0
    vacuous: list[str] = field(default_factory=list)
    marked: bool = False

    @property
    def needs_marker(self) -> bool:
        return bool(self.vacuous) and not self.marked

    @property
    def stale_marker(self) -> bool:
        return self.marked and not self.vacuous


def strip_comments(source: str) -> str:
    source = re.sub(r"/-.*?-/", "", source, flags=re.S)
    return re.sub(r"--[^\n]*", "", source)


def vacuous_names(source: str) -> tuple[str, ...]:
    """Names of theorems in ``source`` whose conclusion is ``True``."""
    body = strip_comments(source)
    aliases = set(PROP_TRUE_ALIAS.findall(body))

    marks = [(m.start(), m.group(1), m.group(2)) for m in DECL.finditer(body)]
    marks.append((len(body), "EOF", ""))

    found: list[str] = []
    for index in range(len(marks) - 1):
        start, kind, name = marks[index]
        if kind not in ("theorem", "lemma"):
            continue
        signature = re.split(r":=", body[start : marks[index + 1][0]], maxsplit=1)[0]
        conclusion = ARROW.split(signature)[-1]
        if not ARROW.search(signature):
            conclusion = conclusion.split(":")[-1]
        token = conclusion.strip()
        if token == "True" or token in aliases:
            found.append(name)
    return tuple(found)


def count_theorems(source: str) -> int:
    body = strip_comments(source)
    return len(re.findall(r"^(?:theorem|lemma)\s", body, flags=re.M))


def scan(root: Path) -> list[FileReport]:
    reports: list[FileReport] = []
    for path in sorted(root.rglob("*.lean")):
        source = path.read_text(encoding="utf-8")
        report = FileReport(path=path)
        report.total = count_theorems(source)
        report.vacuous = list(vacuous_names(source))
        report.marked = MARKER in source
        if report.total or report.marked:
            reports.append(report)
    return reports


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("Proofs"))
    parser.add_argument(
        "--report",
        action="store_true",
        help="print every file that contains a vacuous theorem, then exit 0",
    )
    args = parser.parse_args()

    if not args.root.exists():
        print(f"error: {args.root} does not exist", file=sys.stderr)
        return 2

    reports = scan(args.root)
    offenders = [r for r in reports if r.needs_marker]
    stale = [r for r in reports if r.stale_marker]
    with_vacuous = [r for r in reports if r.vacuous]

    total_theorems = sum(r.total for r in reports)
    total_vacuous = sum(len(r.vacuous) for r in reports)

    if args.report:
        print(f"files scanned          : {len(reports)}")
        print(f"theorems               : {total_theorems}")
        print(f"vacuous theorems       : {total_vacuous}")
        print(f"files with vacuous thm : {len(with_vacuous)}")
        for report in with_vacuous:
            state = "marked" if report.marked else "UNMARKED"
            print(f"  [{state}] {report.path}  {len(report.vacuous)}/{report.total}")
            for name in report.vacuous:
                print(f"      {name}")
        return 0

    ok = True
    for report in offenders:
        ok = False
        print(
            f"{report.path}: {len(report.vacuous)} theorem(s) assert True but the "
            f"file does not declare {MARKER}: {', '.join(report.vacuous)}",
            file=sys.stderr,
        )
    for report in stale:
        ok = False
        print(
            f"{report.path}: declares {MARKER} but contains no vacuous theorem; "
            "remove the marker",
            file=sys.stderr,
        )

    if ok:
        print(
            f"OK: {total_vacuous} vacuous theorem(s) in {len(with_vacuous)} file(s), "
            "all declared"
        )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
