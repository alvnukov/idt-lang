"""Replay five public IDT examples offline, without writing an experiment history."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if __name__ == "__main__":
    sys.dont_write_bytecode = True
if not __package__:
    sys.path.insert(0, str(ROOT))

from scripts import probe_pump_locked_hbt as hbt
from scripts import probe_vacancy_cut_flux as flux
from scripts.probe_active_readout_panels import network_design, summarize
from theory_experiments.primitive_screen import Limits
from theory_experiments.ternary_network_nulls import (
    evaluate_ternary_network_nulls,
    parse_ternary_network_nulls,
)

SCHEMA = "idt-public-demo/1"
FIXTURES = ROOT / "data" / "ternary_network_null_controls.json"
MANIFEST_FILE = "theory_verifier_manifest.json"
TARGETS = ("hbar_I", "G_I", "alpha_em_I", "full_QM_I")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def governance_at_root():
    # Some verifier inputs use paths relative to the repository. Never chdir
    # the caller's process or infer "blocked" from the different label "target".
    from theory_verifier.core import parse_manifest, verify_manifest

    raw = json.loads((ROOT / MANIFEST_FILE).read_bytes())
    manifest = parse_manifest(raw)
    report = verify_manifest(manifest)
    require(report.ok, f"manifest verification failed: {len(report.issues)} issue(s)")
    return {"origin": "manifest_governance", "source": MANIFEST_FILE, "version": raw["theory_version"],
            "verifier_ok": report.ok, "checks": len(report.checks), "issues": len(report.issues),
            "symbol_status": {key: manifest.symbols[key].status for key in TARGETS},
            "blocked_derivation_ids_for_selected_targets": [
                d.identifier for d in manifest.derivations if d.target in TARGETS and d.status == "blocked"],
            "claim_sheet": "PUBLIC_CLAIM_SHEET.md"}


def governance():
    cmd = [sys.executable, "-B", "-c", ("import json; from scripts.public_demo import governance_at_root; "
                                       "print(json.dumps(governance_at_root()))")]
    result = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True, timeout=15, check=False)
    require(result.returncode == 0, "manifest verifier could not certify the current checkout")
    return json.loads(result.stdout)


def detector_histogram():
    with hbt.DEFAULT_FILE.open("rb") as src:
        bins, _ = hbt.read_histogram(src.read(hbt.SOURCE_SIZE + 1))
    window = hbt.window_report(bins, 1500)
    counts = window["signed_lag_counts"]
    return {"origin": "published_measured_histogram", "dataset_doi": "10.5281/zenodo.6337697",
            "half_window_ps": window["half_width_ps"], "minus_four_counts": counts[-4],
            "plus_four_counts": counts[4], "source_sha256": hbt.SOURCE_SHA256,
            "scope": "Unlike-arm pairs at four pump periods. A clean fixed four-cycle forbids "
                     "them; these delay bins do not establish independent outcomes or exclude clocks on emissions."}


def same_port_fixture():
    fixture = json.loads(FIXTURES.read_bytes())
    results = {}
    reference = []
    for ident in ("modfive_dark_mobile", "modfive_dark_prime"):
        rows = [item for item in fixture if item["id"] == ident]
        require(len(rows) == 1, f"missing or duplicate fixture: {ident}")
        candidate = parse_ternary_network_nulls(rows[0])
        reference.append((candidate.initial, candidate.contacts, candidate.readouts))
        (check,), details = evaluate_ternary_network_nulls(candidate, Limits(max_cases=96))
        require(details["contacts_consumed"] == len(candidate.contacts) and
                len(details["comparisons"]) == 1 and check.status in
                ("counterexample", "no_counterexample_within_bounds"), "incomplete finite port check")
        results[ident] = {"rule": candidate.rule, "modulus": candidate.modulus,
                          "predicted_dark": details["comparisons"][0]["predicted_dark"], "status": check.status}
    require(reference[0] == reference[1], "candidates did not face the same submitted test")
    seed, contacts, ((after, port, dark),) = reference[0]
    return {"origin": "prescribed_finite_fixture", "source": str(FIXTURES.relative_to(ROOT)),
            "initial": list(seed), "contacts": [list(t) for t in contacts], "after": after, "port": port,
            "submitted_dark": dark, "candidates": results, "scope": "A submitted target, not a laboratory reading."}


def build_report():
    plan = summarize(network_design())
    before, after = ((3, 3, 3), (1, 3, 3))
    return {"schema": SCHEMA, "detector": detector_histogram(), "same_port": same_port_fixture(),
            "planning": {"origin": "conditional_finite_design", "adaptive_worst_cost": plan["worst_cost"],
                         "best_fixed_cost": plan["optimal_fixed_cost"], "first_test": plan["root_test"],
                         "wildcard_retained_at_all_leaves":
                             all("unmodeled" in leaf for leaf in plan["retained_terminal_sets"]),
                         "scope": "Fresh preparations and declared cost units only; not measured savings."},
            "shutter": {"origin": "conditional_stationary_model", "leaves_before": list(before),
                        "leaves_after": list(after), "first_arm_share_before":
                            flux.iid(before)["first_arm_share_of_stationary_exit_flow"],
                        "first_arm_share_after": flux.iid(after)["first_arm_share_of_stationary_exit_flow"],
                        "scope": "Share of stationary mean transfers under independent uniform edge proposals; "
                                 "not a first-particle probability."},
            "governance": governance(),
            "boundary": "No derivation of full QM, GR, or the Standard Model; no physical constant fitted here."}


def human(r):
    d, s, p, v, g = (r[k] for k in ("detector", "same_port", "planning", "shutter", "governance"))
    def outcome(row):
        return "dark" if row["predicted_dark"] else "bright"

    return "\n".join([
        "IDT public demo | measured data, model tests, and claim boundaries",
        (f"Measured: {d['minus_four_counts']:,} / {d['plus_four_counts']:,} opposite-arm coincidences "
         f"at -4 / +4 pump periods. Dataset: {d['dataset_doi']}."),
        "  " + d["scope"],
        (f"Finite target: port {s['port']} after {s['after']} contacts is prescribed "
         f"{'dark' if s['submitted_dark'] else 'bright'}. Mobile rational model: "
         f"{outcome(s['candidates']['modfive_dark_mobile'])}; mod-5 model: "
         f"{outcome(s['candidates']['modfive_dark_prime'])}. Not a measurement."),
        (f"Test design: adaptive worst cost {p['adaptive_worst_cost']}; best fixed panel "
         f"{p['best_fixed_cost']}. A model with no predictions remains possible. {p['scope']}"),
        f"Shutter model: first-arm share {v['first_arm_share_before']} -> {v['first_arm_share_after']}. "
        + v["scope"],
        f"Governance: {g['version']}; {g['checks']} verifier checks, {g['issues']} issues. "
        "Manifest symbol labels: " + ", ".join(f"{k}={g['symbol_status'][k]}" for k in TARGETS) + ".",
        "  Registered blocked derivations for those targets: "
        + (", ".join(g["blocked_derivation_ids_for_selected_targets"]) or "none") + ".",
        f"  See {g['claim_sheet']} for first-principles restrictions. " + r["boundary"],
    ])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit the idt-public-demo/1 record")
    args = parser.parse_args(argv)
    try:
        report = build_report()
        print(json.dumps(report, ensure_ascii=False, sort_keys=True) if args.json else human(report))
        return 0
    except (OSError, ValueError, KeyError, ArithmeticError, subprocess.SubprocessError) as exc:
        print(f"public_demo: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
