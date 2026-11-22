"""Prospective all-record Renou-T game; conditional statistics, not new data.

Fresh x in {0,1,2} and z in {0,...,5} are independently uniform GIVEN THE
PAST. Twelve setting pairs have signed score +/-1, six have score zero;
all 16 joint outputs are retained. Thus P(active|past)=2/3 and T<=B gives
P(win|active,past)<=p0=(1+B/12)/2. The null is an ordinary real two-source
model on EACH trial, independent sources conditional on the shared classical
past. Marginal independence alone, fresh common resources, settings-dependent
selection, block tomography or readout-corrected frequencies do not suffice.
Use no herald, or an event-ready herald BEFORE settings; every subsequent
settings draw and its raw output must be recorded. This file cannot verify
those physical assertions or detect omitted trials that were renumbered.

Predetermine p1=53/64, from the native ideal T=63/8, not from measured data.
For win/loss/inactive multiply by p1/p0, (1-p1)/(1-p0), 1. When p1<=p0,
do not bet: every factor is one. For q<=p0 the conditional mean factor is
1/3+(2/3)[q*p1/p0+(1-q)*(1-p1)/(1-p0)]<=1. The nonnegative product is a
supermartingale without iid trials. Stop it at its first crossing of K>1
or a finite horizon: its mean remains <=1, so P(any crossing by then)<=1/K.
Taking increasing horizons gives the same bound for indefinite monitoring.
No fixed stopping time is required; outcome-dependent discarding is forbidden.

The reported external SDP number B=7.6605 is imported, NOT proved or certified.
Inference is conditional on a supplied VALID upper bound and protocol claims;
flags attest claims, they do not validate them. For a settings-independent
conditional compromise probability bounded by h on EVERY history, use
B_eff=(1-h)B+12h. An average contamination rate is insufficient.

Default execution uses synthetic exact controls only, with no physical
inference. Optional JSONL accepts exactly trial,x,z,a,b1,b2,c integer fields;
trial starts at 1 and is consecutive. It refuses booleans, missing fields,
duplicates, nonintegers, and invalid outputs. Counts/final products commute,
but threshold crossings require the original order. Crossing decisions use
exact fractions; displayed log10 products are approximate diagnostics only.
No tomography, weighted rows, frequency tables or survivor normalization.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import log10
from pathlib import Path
from typing import cast

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.gaussian_dyadic_words import g
from scripts.probe_two_source_phase_network import (
    AXIS_PAIRS,
    BOUND,
    Experiment,
    analyzer,
    distributions,
    functional,
)

P1 = F(53, 64)
FIELDS = frozenset(("trial", "x", "z", "a", "b1", "b2", "c"))
ATTESTATIONS = (
    "valid_bound",
    "fresh_uniform_settings",
    "conditional_source_independence",
    "complete_raw_records",
    "no_tomography_correction",
    "no_or_presetting_herald",
)


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


@dataclass(frozen=True)
class Bet:
    bound: F = BOUND
    contamination: F = F(0)

    def __post_init__(self) -> None:
        if not 0 <= self.bound <= 12 or not 0 <= self.contamination <= 1:
            raise ValueError("bound must be in [0,12], contamination in [0,1]")

    @property
    def effective_bound(self) -> F:
        return (1 - self.contamination) * self.bound + 12 * self.contamination

    @property
    def p0(self) -> F:
        return (1 + self.effective_bound / 12) / 2

    @property
    def betting(self) -> bool:
        return P1 > self.p0

    def factor(self, score: int) -> F:
        if type(score) is not int or score not in (-1, 0, 1):
            raise ValueError("score must be the integer -1, 0 or 1")
        if not self.betting or score == 0:
            return F(1)
        return P1 / self.p0 if score == 1 else (1 - P1) / (1 - self.p0)


def score(x: int, z: int, a: int, b1: int, b2: int, c: int) -> int:
    values = (x, z, a, b1, b2, c)
    allowed = (range(3), range(6), (-1, 1), (0, 1), (0, 1), (-1, 1))
    if any(type(v) is not int or v not in domain for v, domain in zip(values, allowed)):
        raise ValueError("invalid setting or raw output")
    i, j = AXIS_PAIRS[z // 2]
    if x not in (i, j):
        return 0
    sign = -1 if x == j and z % 2 else 1
    bell = (1 if b2 == 0 else -1, 1 if b1 == 0 else -1, -1 if b1 == b2 else 1)
    return sign * bell[x] * a * c


@dataclass(frozen=True)
class Summary:
    wins: int
    losses: int
    inactive: int
    first_crossing: int | None
    final: F


def accumulate(scores: tuple[int, ...], bet: Bet, threshold: F) -> Summary:
    if threshold <= 1:
        raise ValueError("threshold must exceed one")
    value, first = F(1), None
    for trial, item in enumerate(scores, 1):
        value *= bet.factor(item)
        if first is None and value >= threshold:
            first = trial
    wins, losses, inactive = (scores.count(k) for k in (1, -1, 0))
    need(value == bet.factor(1) ** wins * bet.factor(-1) ** losses, "count compression")
    return Summary(wins, losses, inactive, first, value)


def masses(records: Experiment) -> dict[int, F]:
    result = {k: F(0) for k in (-1, 0, 1)}
    need(set(records) == set(product(range(3), range(6))), "all 18 setting pairs")
    for (x, z), table in records.items():
        need(len(table) == 16 and sum(table.values()) == 1, "all output cells")
        for (a, b1, b2, c), probability in table.items():
            need(probability >= 0, "positive raw probability")
            result[score(x, z, a, b1, b2, c)] += probability / 18
    need(result[0] == F(1, 3), "setting-only activity")
    need(18 * (result[1] - result[-1]) == functional(records), "Renou-T coefficients")
    return result


def exact_controls() -> None:
    bet = Bet()
    need(bet.p0 == F(13107, 16000), "reported-bound conversion")
    for q in (F(0), bet.p0 / 2, bet.p0):
        mean = F(1, 3) + F(2, 3) * (q * bet.factor(1) + (1 - q) * bet.factor(-1))
        need(mean <= 1 and (q != bet.p0 or mean == 1), "conditional null factor")
    critical = (F(63, 8) - BOUND) / (12 - BOUND)
    for h in (critical, F(1, 10), F(1)):
        stopped = Bet(contamination=h)
        need(
            not stopped.betting and all(stopped.factor(k) == 1 for k in (-1, 0, 1)),
            "do not reverse the bet",
        )

    threshold = F(21, 20)
    for adaptive in (False, True):
        total, expectation, crossing = F(0), F(0), F(0)
        for sequence in product((-1, 0, 1), repeat=6):
            probability, history = F(1), 0
            for item in sequence:
                q = bet.p0 / 2 if adaptive and history % 2 else bet.p0
                probability *= (
                    F(1, 3) if not item else F(2, 3) * (q if item == 1 else 1 - q)
                )
                history += item
            observed = accumulate(sequence, bet, threshold)
            total += probability
            expectation += probability * observed.final
            if observed.first_crossing is not None:
                crossing += probability
        need(
            total == 1 and expectation <= 1 and crossing <= 1 / threshold,
            "finite optional-crossing inequality, including adaptive null",
        )
    early = accumulate((1,) * 5 + (-1,), bet, threshold)
    late = accumulate((-1,) + (1,) * 5, bet, threshold)
    need(
        early.final == late.final
        and early.first_crossing == 5
        and late.first_crossing is None,
        "order changes crossings, not final counts",
    )
    full = accumulate((1, -1) * 300, bet, F(20))
    selected = accumulate((1,) * 300, bet, F(20))
    need(
        full.final < 1
        and full.first_crossing is None
        and selected.first_crossing is not None,
        "adversarial loss deletion manufactures a crossing",
    )

    ket = (g(F(3, 4), F(1, 2)), g(F(1, 4), F(1, 4)), g(F(1, 4)))
    base = analyzer(ket)
    native = masses(distributions(base))
    erased = masses(distributions(base, erase_imaginary=True))
    need(
        native == {1: F(53, 96), -1: F(11, 96), 0: F(1, 3)},
        "native all-record distribution",
    )
    need(native[1] / (1 - native[0]) == P1, "predetermined ideal alternative")
    need(18 * (erased[1] - erased[-1]) == F(43, 8), "real-erasure control")
    need(
        sum(native[k] * bet.factor(k) for k in native) > 1,
        "synthetic alternative expectation",
    )
    need(
        sum(erased[k] * bet.factor(k) for k in erased) < 1,
        "erased prediction is not a separation",
    )


def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    out: dict[str, object] = {}
    for key, value in pairs:
        if key in out:
            raise ValueError(f"duplicate JSON field: {key}")
        out[key] = value
    return out


def parse_record(raw: object, trial: int) -> int:
    if not isinstance(raw, dict) or set(raw) != FIELDS:
        raise ValueError("each record must contain exactly trial,x,z,a,b1,b2,c")
    row = cast(dict[str, object], raw)
    if any(type(v) is not int for v in row.values()):
        raise ValueError(
            "record values must be integers, not booleans or coerced numbers"
        )
    values = cast(dict[str, int], row)
    if values["trial"] != trial:
        raise ValueError("trial numbers must start at one and be consecutive")
    return score(*(values[key] for key in ("x", "z", "a", "b1", "b2", "c")))


def read_scores(path: Path) -> tuple[int, ...]:
    out = []
    with path.open(encoding="utf-8") as stream:
        for trial in range(1, 10002):
            line = stream.readline(4097)
            if not line:
                break
            if trial > 10000 or len(line) > 4096:
                raise ValueError(
                    "bounded reader: at most 10000 records, 4096 characters each"
                )
            if not line.strip():
                raise ValueError("blank records are not silently discarded")
            out.append(
                parse_record(json.loads(line, object_pairs_hook=unique_object), trial)
            )
    if not out:
        raise ValueError("empty input is not experimental evidence")
    return tuple(out)


def eligibility(attested: frozenset[str], bet: Bet) -> tuple[bool, list[str]]:
    missing = sorted(set(ATTESTATIONS) - attested)
    if not bet.betting:
        missing.append("predetermined alternative does not exceed the null bound")
    return not missing, missing


def parser_controls() -> None:
    valid: dict[str, object] = {
        "trial": 1,
        "x": 0,
        "z": 0,
        "a": 1,
        "b1": 0,
        "b2": 0,
        "c": 1,
    }
    need(parse_record(valid, 1) == 1, "raw record")
    for invalid in (
        None,
        {},
        valid | {"trial": 2},
        valid | {"a": True},
        valid | {"x": 0.0},
        valid | {"z": 6},
        valid | {"weight": 1},
    ):
        try:
            parse_record(invalid, 1)
        except ValueError:
            pass
        else:
            raise ArithmeticError("invalid record accepted")
    need(not eligibility(frozenset(), Bet())[0], "uncertified inputs not eligible")
    need(
        not eligibility(frozenset(ATTESTATIONS), Bet(contamination=F(1)))[0],
        "null-dominated input not eligible",
    )
    try:
        json.loads('{"x":0,"x":1}', object_pairs_hook=unique_object)
    except ValueError:
        pass
    else:
        raise ArithmeticError("duplicate fields accepted")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jsonl", type=Path, help="complete ordered raw trial records")
    parser.add_argument(
        "--bound",
        type=F,
        default=BOUND,
        help="supplied upper bound; default is external reported 7.6605, not certified",
    )
    parser.add_argument(
        "--contamination",
        type=F,
        default=F(0),
        help="per-history settings-independent upper fraction",
    )
    parser.add_argument(
        "--threshold", type=F, default=F(20), help="exact crossing threshold >1"
    )
    for name in ATTESTATIONS:
        parser.add_argument(
            "--attest-" + name.replace("_", "-"), dest=name, action="store_true"
        )
    args = parser.parse_args()
    try:
        bet = Bet(args.bound, args.contamination)
        if args.threshold <= 1:
            raise ValueError("threshold must exceed one")
    except ValueError as error:
        parser.error(str(error))
    exact_controls()
    parser_controls()
    if args.jsonl is None:
        print(
            "PASS: exact full-table native T=63/8, p1=53/64; real erasure T=43/8; conditional/adaptive null, optional crossings, order and postselection controls."
        )
        print(
            "Synthetic predictions only: NOT ELIGIBLE for physical inference. Reported B=7.6605 is not certified here; all trials and conditional source/settings assumptions remain supplied."
        )
        return
    try:
        observed = accumulate(read_scores(args.jsonl), bet, args.threshold)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        parser.error(str(error))
    attested = frozenset(name for name in ATTESTATIONS if getattr(args, name))
    eligible, missing = eligibility(attested, bet)
    log_product = observed.wins * log10(float(bet.factor(1))) + observed.losses * log10(
        float(bet.factor(-1))
    )
    print(
        json.dumps(
            {
                "eligibility": "conditional_on_unverified_attestations"
                if eligible
                else "not_eligible_no_physical_inference",
                "missing_or_disabled": missing,
                "bound": str(bet.bound),
                "effective_bound": str(bet.effective_bound),
                "p0": str(bet.p0),
                "predetermined_p1": str(P1),
                "trials": observed.wins + observed.losses + observed.inactive,
                "wins": observed.wins,
                "losses": observed.losses,
                "inactive": observed.inactive,
                "first_crossing_exact": observed.first_crossing,
                "threshold": str(args.threshold),
                "conditional_anytime_false_crossing_bound": str(1 / args.threshold)
                if eligible
                else None,
                "log10_final_product_approximate_not_for_threshold_decisions": log_product,
                "warning": "Input provenance and assumptions are not checked by this program; no SDP certificate or physical significance is supplied.",
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
