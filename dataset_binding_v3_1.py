#!/usr/bin/env python3
"""
Dataset Binding v3.1

Loads experimental fixtures, checks whether numerical bounds are allowed,
and computes simple derived quantities where possible.
"""

from __future__ import annotations

import math
from pathlib import Path
from typing import Any, Dict, List
import yaml


REQUIRED_VISIBILITY_BOUND_FIELDS = ["V_obs", "V_env", "sigma_V", "tau_s", "delta_x_m"]


def load_yaml(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as f:
        return yaml.safe_load(f)


def fixture_bound_status(fx: Dict[str, Any]) -> Dict[str, Any]:
    req = fx.get("required_for_lambda_bound")
    if not req:
        return {"can_compute_lambda_bound": False, "reason": "no required_for_lambda_bound block"}
    missing = [k for k in REQUIRED_VISIBILITY_BOUND_FIELDS if req.get(k) is None]
    return {
        "can_compute_lambda_bound": len(missing) == 0,
        "missing": missing,
        "reason": "complete" if not missing else "missing required fields"
    }


def lambda_bound(delta: float, tau: float, m: float, m0: float, alpha: float, dx: float, rI: float) -> float:
    factor = (m / m0) ** alpha * (1.0 - math.exp(-(dx * dx) / (4.0 * rI * rI)))
    if tau <= 0 or factor <= 0:
        raise ValueError("tau and sensitivity factor must be positive")
    return delta / (tau * factor)


def summarize_fixture(fx: Dict[str, Any]) -> Dict[str, Any]:
    summary = {
        "id": fx["id"],
        "title": fx.get("title"),
        "year": fx.get("year"),
        "status": fx.get("status"),
        "fixture_type": fx.get("fixture_type"),
    }
    summary["lambda_bound_gate"] = fixture_bound_status(fx)
    if "derived_rough" in fx:
        summary["derived_rough"] = fx["derived_rough"]
    return summary


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--fixtures-dir", default="/mnt/data/fixtures_v3_1")
    parser.add_argument("--report", default="/mnt/data/dataset_binding_report_v3_1.md")
    args = parser.parse_args()

    fixtures_dir = Path(args.fixtures_dir)
    summaries = []
    for path in sorted(fixtures_dir.glob("*.yaml")):
        fx = load_yaml(path)
        summaries.append(summarize_fixture(fx))

    lines = ["# Dataset Binding Report v3.1", ""]
    for s in summaries:
        lines.append(f"## {s['id']}")
        lines.append("")
        lines.append(f"- title: {s.get('title')}")
        lines.append(f"- year: {s.get('year')}")
        lines.append(f"- type: {s.get('fixture_type')}")
        lines.append(f"- status: {s.get('status')}")
        gate = s["lambda_bound_gate"]
        lines.append(f"- can_compute_lambda_bound: {gate.get('can_compute_lambda_bound')}")
        if gate.get("missing"):
            lines.append(f"- missing: {', '.join(gate['missing'])}")
        if s.get("derived_rough"):
            lines.append("- derived_rough:")
            for k, v in s["derived_rough"].items():
                lines.append(f"  - {k}: {v}")
        lines.append("")

    report_path = Path(args.report)
    report_path.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {report_path}")


if __name__ == "__main__":
    main()
