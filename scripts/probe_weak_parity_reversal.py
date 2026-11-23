"""Finite neutron beta spin-reversal adapter; not a physical candidate test.

Rows are fixed detector-geometry labels d=+,-; columns are independently
calibrated axial-spin labels s=+,-. Neither relabeling is spatial parity.
The synthetic convention n_ds ∝ (1-d*s*x) makes the superratio contrast x;
x is not a corrected neutron-decay A0.
"""

import json
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt, sqrt
from typing import Literal

from scripts.probe_raw_packet_phase_quotients import run_probe as run_phase_quotients

Number = int | F
Sign = Literal[-1, 1]


@dataclass(frozen=True)
class Cell:
    """Observed and expected background counts over the specified live time."""

    observed: Number | None
    background: Number | None
    live_time: Number | None

    def corrected_rate(self) -> tuple[F | None, str | None]:
        observed, background, live_time = self.observed, self.background, self.live_time
        if observed is None or background is None or live_time is None:
            return None, "missing_input"
        if live_time <= 0:
            return None, "nonpositive_live_time"
        if observed < 0 or background < 0:
            return None, "negative_observed_or_background"
        net = F(observed) - background
        if net <= 0:
            return None, "nonpositive_net_count"
        return net / live_time, None


Cells = tuple[tuple[Cell | None, Cell | None], tuple[Cell | None, Cell | None]]
Rates = tuple[tuple[F, F], tuple[F, F]]


@dataclass(frozen=True)
class Estimate:
    status: Literal["evaluated", "inconclusive"]
    problems: dict[str, str]
    corrected_rates: Rates | None = None
    ratio: F | None = None
    exact_contrast: F | None = None
    approximate_contrast: float | None = None

    def matches_contrast(self, expected: F) -> bool:
        """Check the squared-ratio identity exactly, on the correct branch."""
        return (
            self.ratio is not None
            and -1 < expected < 1
            and self.ratio == ((1 - expected) / (1 + expected)) ** 2
        )


def estimate(cells: Cells) -> Estimate:
    """Subtract background and divide by live time before forming the ratio."""
    problems: dict[str, str] = {}
    rates: list[F] = []
    for d, row in zip(("+", "-"), cells, strict=True):
        for s, cell in zip(("+", "-"), row, strict=True):
            rate, problem = (
                (None, "missing_cell") if cell is None else cell.corrected_rate()
            )
            if rate is None:
                problems[f"d{d}s{s}"] = problem or "missing_rate"
            else:
                rates.append(rate)
    if problems:
        return Estimate("inconclusive", problems)

    pp, pm, mp, mm = rates
    ratio = (pp * mm) / (pm * mp)
    a, b = isqrt(ratio.numerator), isqrt(ratio.denominator)
    exact = (
        F(b - a, b + a)
        if a * a == ratio.numerator and b * b == ratio.denominator
        else None
    )
    # Never convert an unbounded ratio to float. Rationalize first so that
    # a ratio close to 1 need not lose the entire signal to cancellation.
    small = min(ratio, 1 / ratio)
    magnitude = float(1 - small) / (1 + sqrt(float(small))) ** 2
    approximate = (
        float(exact) if exact is not None else (-magnitude if ratio > 1 else magnitude)
    )
    return Estimate("evaluated", {}, ((pp, pm), (mp, mm)), ratio, exact, approximate)


def relabel(cells: Cells, *, flip_d: bool = False, flip_s: bool = False) -> Cells:
    """Permute entire cells, including their exposure/background records."""
    first, second = cells[::-1] if flip_d else cells
    return (first[::-1], second[::-1]) if flip_s else (first, second)


def synthetic_table(x: F, delta: F = F(0)) -> Cells:
    """Deterministic expected counts, not samples or empirical event data.

    L_s=(3,2), epsilon_d=(200,100) in arbitrary synthetic units. The joint
    efficiency factor 1-d*s*delta is not canceled by the superratio.
    """
    if not (-1 < x < 1 and -1 < delta < 1):
        raise ValueError("synthetic contrasts must lie strictly between -1 and 1")

    def cell(d: Sign, s: Sign) -> Cell:
        live = 3 if s == 1 else 2
        rate = 200 if d == 1 else 100
        net = live * rate * (1 - d * s * x) * (1 - d * s * delta)
        return Cell(net, 0, live)

    return ((cell(1, 1), cell(1, -1)), (cell(-1, 1), cell(-1, -1)))


@dataclass(frozen=True)
class IsotropicCalibrator:
    cells: Cells
    independent_isotropic_matched: bool


@dataclass(frozen=True)
class CalibrationCheck:
    status: Literal[
        "inconclusive",
        "detected_nonzero_calibrator_contrast",
        "zero_calibrator_contrast_in_these_cells",
    ]
    reason: str
    estimate: Estimate | None = None


def calibration_check(calibrator: IsotropicCalibrator | None) -> CalibrationCheck:
    """An exact diagnostic, not statistical significance or a model pass."""
    if calibrator is None or not calibrator.independent_isotropic_matched:
        return CalibrationCheck(
            "inconclusive",
            "An independent isotropic calibrator with matched response is required.",
        )
    result = estimate(calibrator.cells)
    if result.status == "inconclusive":
        return CalibrationCheck(
            "inconclusive", "Invalid or missing calibrator cells.", result
        )
    if result.matches_contrast(F(0)):
        return CalibrationCheck(
            "zero_calibrator_contrast_in_these_cells",
            "No joint bias detected by this exact control; this is not a model pass.",
            result,
        )
    return CalibrationCheck(
        "detected_nonzero_calibrator_contrast",
        "A nonzero instrument contrast is detected under the calibrator assumptions.",
        result,
    )


def spatial_parity(chi: Sign, spin: Sign, momentum: Sign) -> tuple[Sign, Sign, Sign]:
    """One-axis sign illustration: reverse pseudoscalar chi and polar p, not axial S."""
    return (-1 if chi == 1 else 1, spin, -1 if momentum == 1 else 1)


def fixture_control(
    fixture_plus: F, fixture_minus: F, *, assume_additive: bool
) -> tuple[F, F] | None:
    """Separate retaining and sign-changing parts if x(chi)=a+chi*b is supplied.

    The assumption includes unchanged calibrations under fixture reversal.
    It is not inferred from the two observed contrasts.
    """
    if not assume_additive:
        return None
    return (fixture_plus + fixture_minus) / 2, (fixture_plus - fixture_minus) / 2


def _report_estimate(result: Estimate) -> dict[str, object]:
    return {
        "status": result.status,
        "problems": result.problems,
        "corrected_rates": (
            [[str(rate) for rate in row] for row in result.corrected_rates]
            if result.corrected_rates is not None
            else None
        ),
        "ratio": str(result.ratio) if result.ratio is not None else None,
        "exact_contrast": (
            str(result.exact_contrast) if result.exact_contrast is not None else None
        ),
        "approximate_contrast": result.approximate_contrast,
    }


def run_probe() -> dict[str, object]:
    """Replay finite controls and retain the physical mapping obstruction."""
    controls = []
    for x, net_counts in (
        (F(0), ((600, 400), (300, 200))),
        (F(1, 5), ((480, 480), (360, 160))),
        (F(-1, 5), ((720, 320), (240, 240))),
    ):
        cells = synthetic_table(x)
        if (
            tuple(
                tuple(
                    cell.observed - cell.background
                    for cell in row
                    if cell is not None
                    and cell.observed is not None
                    and cell.background is not None
                )
                for row in cells
            )
            != net_counts
        ):
            raise RuntimeError("unexpected synthetic net counts")
        checks = {
            name: estimate(relabel(cells, flip_d=fd, flip_s=fs))
            for name, fd, fs in (
                ("none", False, False),
                ("detector_only", True, False),
                ("spin_only", False, True),
                ("both", True, True),
            )
        }
        for name, result in checks.items():
            expected = x if name in ("none", "both") else -x
            if not result.matches_contrast(expected):
                raise RuntimeError(f"label-reversal control failed: {x}, {name}")
        controls.append(
            {
                "synthetic_x": str(x),
                "net_counts": net_counts,
                "labels_reversed": {
                    name: _report_estimate(result) for name, result in checks.items()
                },
            }
        )
    delta = F(1, 5)
    counterfeit = synthetic_table(F(0), delta)
    bias = calibration_check(IsotropicCalibrator(counterfeit, True))
    indistinguishable = counterfeit == synthetic_table(delta)
    if not indistinguishable or bias.status != "detected_nonzero_calibrator_contrast":
        raise RuntimeError("nonfactorizing-efficiency control failed")

    state: tuple[Sign, Sign, Sign] = (1, 1, 1)
    chi, spin, momentum = state
    chi_p, spin_p, momentum_p = spatial_parity(*state)
    odd = (spin * momentum, spin_p * momentum_p)
    even = (chi * odd[0], chi_p * odd[1])
    if odd != (1, -1) or even != (1, 1):
        raise RuntimeError("fixture parity control failed")
    fixture_examples = {}
    for name, plus, minus in (
        ("retaining", F(1, 5), F(1, 5)),
        ("cancelling", F(1, 5), F(-1, 5)),
        ("mixed", F(3, 10), F(1, 10)),
    ):
        separated = fixture_control(plus, minus, assume_additive=True)
        if separated is None:
            raise RuntimeError("missing explicitly conditional fixture decomposition")
        retaining, reversing = separated
        fixture_examples[name] = {
            "x_chi_plus": str(plus),
            "x_chi_minus": str(minus),
            "retaining": str(retaining),
            "fixture_sign_changing": str(reversing),
        }

    menu = run_phase_quotients().contrast
    return {
        "schema": "idt-weak-parity-reversal-probe-v1",
        "cell_order": [["d+s+", "d+s-"], ["d-s+", "d-s-"]],
        "estimator": "n=(observed-background)/live_time; R=n++*n--/(n+-*n-+); C=(1-sqrt(R))/(1+sqrt(R))",
        "synthetic_controls": controls,
        "joint_efficiency_control": {
            "formula": "epsilon_ds=epsilon_d*(1-d*s*delta)",
            "true_x": "0",
            "delta": str(delta),
            "same_cells_as_signal_only": indistinguishable,
            "counterfeit_contrast": (
                _report_estimate(bias.estimate) if bias.estimate is not None else None
            ),
            "without_matched_calibrator": calibration_check(None).status,
            "with_matched_calibrator": bias.status,
            "calibrator_assumptions": "independent, isotropic, matched instrument response",
            "interpretation": bias.reason,
        },
        "fixture_control": {
            "under_spatial_parity": "(chi,S,p) -> (-chi,S,-p)",
            "S_dot_p_before_after": odd,
            "chi_times_S_dot_p_before_after": even,
            "assumptions": "x(chi)=a+chi*b and unchanged independent calibrations",
            "examples": fixture_examples,
            "without_assumptions": "inconclusive",
        },
        "candidate_bridge": {
            "status": "not_evaluable",
            "predicted_a0": None,
            "source": "scripts/probe_raw_packet_phase_quotients.py",
            "basis_pairs": menu.basis_pairs,
            "pushforward_checks": menu.pushforward_checks,
            "selected_eigenvalue": menu.selected_eigenvalue,
            "signed_coefficients_on_sample": menu.signed_coefficients_on_sample,
            "positive_counts_on_same_sample": menu.positive_counts_on_same_sample,
            "menu_reversal_is_physical_parity": False,
            "menu_reversal": "W -> W^-1 exchanges H and D under a one-side menu mirror",
            "missing": [
                "physical detector-geometry/electron-momentum calibration",
                "independent axial neutron-spin calibration",
                "positive four-cell output and detector-response calibration",
                "effective neutron beta-decay dynamics and response corrections to A0",
            ],
            "interpretation": "Integer pushforwards are not probabilities or neutron beta data.",
        },
        "empirical_metadata_is_event_data": False,
        "empirical_metadata": [
            {
                "experiment": "PERKEO III",
                "source": "https://arxiv.org/abs/1812.04666",
                "neutrons": "cold beam",
                "a0": "-0.11985",
                "stat": "0.00017",
                "syst": "0.00012",
            },
            {
                "experiment": "UCNA",
                "source": "https://arxiv.org/abs/1712.00884",
                "neutrons": "stored ultracold",
                "a0": "-0.12054",
                "stat": "0.00044",
                "syst": "0.00068",
            },
        ],
        "claim_boundary": (
            "Exact finite/synthetic controls only. Published A0 metadata are not four-cell "
            "inputs or a fit target. No photon test, weak chirality or physical A0 prediction."
        ),
    }


def main() -> None:
    print(json.dumps(run_probe(), indent=2, sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    main()
