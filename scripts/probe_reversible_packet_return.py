"""Even-step same-event returns under two *supplied* reversible offer laws.

Run: python3 -m scripts.probe_reversible_packet_return [--spectrum PATH]

Keep raw rule 32, its doubled cube, matching, and one-root preparation fixed.
Choose either a fresh uniform center (idle on a disabled offer) or a fresh
uniform enabled center at every step. Neither stochastic law follows from the
raw rule. Separately, an optional offline reader replays three descriptive
windows of a hash-pinned KamLAND *prompt-energy* table. They are not time bins
of either kernel. No fit, exclusion of a physical model, or QM derivation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation
from fractions import Fraction as Q
from itertools import combinations, pairwise
from math import lcm, sqrt
from pathlib import Path

from scripts.probe_facilitated_forest_signal import carriers, lift, need
from scripts.probe_localized_shell_packets import RawShell


@dataclass(frozen=True)
class Kernel:
    # P[x,y] = rows[x].get(y,0)/denominator. Integer weights normalize to pi.
    rows: tuple[dict[int, int], ...]
    weights: tuple[int, ...]
    denominator: int


def verify_balance(rows, weights, denominator):
    size = len(rows)
    need(len(weights) == size and all(w > 0 for w in weights), "invalid weights")
    need(denominator > 0, "invalid kernel denominator")
    for row in rows:
        need(all(0 <= y < size and n > 0 for y, n in row.items()), "invalid transition")
        need(sum(row.values()) == denominator, "row not stochastic")
    for x in range(size):
        for y in range(size):
            need(
                weights[x] * rows[x].get(y, 0) == weights[y] * rows[y].get(x, 0),
                "detailed balance fails",
            )
    return size * size


def kernels(offers, center_count):
    """Count multiplicities of raw labeled offers; never infer them from distances."""
    degrees = tuple(map(len, offers))
    need(min(degrees) > 0, "empty enabled set")
    common = lcm(*degrees)
    all_rows, active_rows = [], []
    for x, row in enumerate(offers):
        need(all(0 <= c < center_count for c in row), "center outside offer alphabet")
        counts = Counter(row.values())
        active_rows.append({y: n * (common // len(row)) for y, n in counts.items()})
        if len(row) < center_count:
            counts[x] += center_count - len(row)
        all_rows.append(dict(counts))
    return {
        "all_centers": Kernel(tuple(all_rows), (1,) * len(offers), center_count),
        "enabled_centers": Kernel(tuple(active_rows), degrees, common),
    }


def even_samples(kernel, event, preparation, horizon):
    """Exact unsmoothed q(0),q(2),..., via direct Markov steps on the indicator.

    preparation maps state indices to unnormalized positive starting mass.
    Keep one common denominator for each integer-valued matrix/vector product.
    """
    size = len(kernel.rows)
    need(bool(event) and bool(preparation), "empty preparation or detector")
    need(all(0 <= x < size for x in event), "unknown detector state")
    need(
        all(0 <= x < size and w > 0 for x, w in preparation.items()),
        "invalid preparation",
    )
    values = [int(x in event) for x in range(size)]
    total = sum(preparation.values())
    result = []
    for t in range(2 * horizon + 1):
        if t % 2 == 0:
            result.append(Q(sum(w * values[x] for x, w in preparation.items()), total))
        if t < 2 * horizon:
            values = [sum(m * values[y] for y, m in row.items()) for row in kernel.rows]
            total *= kernel.denominator
    return result


def check_differences(samples):
    """All (-1)^j Delta^j q(k) inside this finite triangle (not beyond it)."""
    scale = lcm(*(Q(v).denominator for v in samples))
    row = [int(v * scale) for v in samples]
    checked = 0
    while row:
        need(min(row) >= 0, "negative signed forward difference")
        checked += len(row)
        row = [a - b for a, b in pairwise(row)]
    return checked


def controls(offers, root, kernel, vertex_states, base):
    # Reuse actual labeled raw offers in this source-ordered schedule.
    pair_map = []
    for s, row in enumerate(offers):
        after_one = row.get(1, s)
        pair_map.append(offers[after_one].get(0, after_one))
    x = root
    ordered = [Q(1)]
    for _ in range(3):
        x = pair_map[x]
        ordered.append(Q(x == root))
    labels = [v for v in range(len(vertex_states)) if v not in base.neighbors[0]]
    event = {vertex_states[v] for v in labels}
    conditioned = {s: kernel.weights[s] for s in event}
    # A separate scalar completely monotone sequence under three clock laws.
    # The last clock has positive mass at zero, so it does not dominate delta_2.
    clocks = ({1: Q(1)}, {2: Q(1)}, {0: Q(1, 2), 6: Q(1, 2)})
    means = [sum(t * p for t, p in clock.items()) for clock in clocks]
    responses = [
        sum(p * (1 + Q(1, 2) ** t) / 2 for t, p in clock.items()) for clock in clocks
    ]
    return {
        "ordered_offers": {
            "schedule": [1, 0],
            "even_returns": list(map(str, ordered)),
            "pair_map_bijective": len(set(pair_map)) == len(offers),
            "return_edge_from_root_image": pair_map[pair_map[root]] == root,
            "boundary": "The ordered pair acts bijectively, but root -> image has no reverse edge "
            "under that same pair map. Invertibility is not detailed balance.",
        },
        "coarse_detector": {
            "accepted_vertex_labels": labels,
            "point_prepared": list(map(str, even_samples(kernel, event, {root: 1}, 4))),
            "stationary_conditioned": list(
                map(str, even_samples(kernel, event, conditioned, 4))
            ),
            "boundary": "A point preparation is not pi conditioned on this coarse event.",
        },
        "clock_mixture": {
            "sequence": "q(t)=(1+2^(-t))/2",
            "clocks": [{t: str(p) for t, p in clock.items()} for clock in clocks],
            "mean_times": list(map(str, means)),
            "mean_readouts": list(map(str, responses)),
            "boundary": "Increasing mean times alone do not give stochastic ordering of the clock laws.",
        },
    }


def packet_report():
    base = carriers()["cube"]
    raw, rungs = lift(base)
    initial = raw.prepare(sum(rungs), [0])
    moves = RawShell(raw).orbit(initial, 32)
    words = sorted(moves)
    index = {word: i for i, word in enumerate(words)}
    offers = tuple({c: index[y] for c, y in moves[x].items()} for x in words)
    vertices = tuple(
        index[raw.prepare(sum(rungs), [v])] for v in range(len(base.stars))
    )
    point_events = {frozenset([s]) for s in range(len(words))}
    unions = {
        frozenset(g)
        for n in range(1, len(vertices) + 1)
        for g in combinations(vertices, n)
    }
    events = point_events | unions | {frozenset(range(len(words)))}
    laws = kernels(offers, len(raw.stars))
    horizon = 12
    summaries = {}
    for name, kernel in laws.items():
        checked = verify_balance(kernel.rows, kernel.weights, kernel.denominator)
        root_returns = None
        for event in events:
            samples = even_samples(
                kernel, event, {x: kernel.weights[x] for x in event}, horizon
            )
            n_diff = check_differences(samples)
            if event == {index[initial]}:
                root_returns = list(map(str, samples))
        need(root_returns is not None, "missing root point event")
        summaries[name] = {
            "offer_law": "uniform fresh center; disabled idles"
            if name == "all_centers"
            else "uniform among currently enabled centers using fresh randomness",
            "stationary_law": "uniform"
            if name == "all_centers"
            else "proportional to enabled degree",
            "stationary_weight_sum": sum(kernel.weights),
            "detailed_balance_pairs_checked": checked,
            "max_k": horizon,
            "difference_tests_per_event": n_diff,
            "raw_point_events": len(point_events),
            "vertex_unions": len(unions),
            "distinct_events_checked": len(events),
            "root_even_returns": root_returns,
        }
    return {
        "rule": 32,
        "root_vertex": 0,
        "raw_states": len(words),
        "offered_centers": len(raw.stars),
        "raw_labeled_directed_events": sum(map(len, offers)),
        "kernels": summaries,
        "controls": controls(
            offers, vertices[0], laws["enabled_centers"], vertices, base
        ),
        "conditional_argument": (
            "For a finite detailed-balanced Markov kernel P, positive stationary pi, nonempty F, "
            "preparation pi|F and readout 1_F, q(2k)=<1_F,P^(2k)1_F>_pi/pi(F). The reversible "
            "Markov contraction is self-adjoint; its squared eigenvalues u lie in [0,1]. Thus "
            "q(2k) is the kth moment of a positive probability measure there, and its signed "
            "differences integrate u^k(1-u)^j. This argument covers all k,j and F under these "
            "hypotheses; the executable difference checks cover only the reported finite triangle."
        ),
        "scope": "Both clocks are supplied; not a derivation of a stochastic law, QM, or a physical neutrino exclusion.",
    }


SPECTRUM_SHA256 = "95d2c0d6bdc25e6624809668ec7e92ffcab06fa72ee36955056d99f9f1d400f9"
SPECTRUM_SIZE = 5776
RELEASE = "https://www.awa.tohoku.ac.jp/KamLAND/4th_result_data_release/"
WINDOWS = (("4.4", "5.0"), ("2.6", "3.1"), ("1.7", "2.2"))
# Review transcription of aggregates, not raw rows or a collaboration likelihood.
REFERENCE = (
    (227, "280.1990", "9.1812"),
    (205, "438.5270", "27.9275"),
    (270, "316.0680", "89.3786"),
)


def parse_spectrum(data):
    """Parse the release schema (independent of the identity check in spectrum_report)."""
    lines = data.decode("ascii").splitlines()
    if len(lines) != 76:
        raise ValueError("expected exactly 76 headerless spectrum rows")
    rows = []
    for i, line in enumerate(lines):
        fields = line.split()
        if len(fields) != 9:
            raise ValueError(f"expected nine columns in row {i + 1}")
        try:
            vals = tuple(Q(Decimal(s)) for s in fields)
        except (InvalidOperation, OverflowError, ValueError) as exc:
            raise ValueError(f"invalid decimal in row {i + 1}") from exc
        if vals[0] != Q(95 + 10 * i, 100) or vals[1].denominator != 1 or min(vals) < 0:
            raise ValueError(
                f"invalid energy grid, count, or nonnegative yield in row {i + 1}"
            )
        rows.append(vals)
    return rows


def window_summary(bounds, bins, observed, reactor, background):
    if reactor <= 0:
        raise ValueError("nonpositive total no-oscillation reactor expectation")
    return {
        "prompt_MeV_left_closed_right_open": list(bounds),
        "bins": bins,
        "observed": observed,
        "reactor_no_oscillation": str(reactor),
        "modeled_nonreactor": str(background),
        "ratio": str((observed - background) / reactor),
        "counting_only_sigma": sqrt(observed) / float(reactor),
    }


def summarize_windows(rows):
    result = []
    for bounds in WINDOWS:
        lo, hi = map(Q, bounds)
        selected = [row for row in rows if lo <= row[0] < hi]
        # Ignore fitted three-flavor reactor column index 3, never subtract it.
        observed = int(sum(row[1] for row in selected))
        reactor = sum(row[2] for row in selected)
        background = sum(sum(row[4:9]) for row in selected)
        result.append(
            window_summary(bounds, len(selected), observed, reactor, background)
        )
    return result


def spectrum_report(path: Path | None):
    reference = [
        window_summary(bounds, int((Q(bounds[1]) - Q(bounds[0])) * 10), n, Q(r), Q(b))
        for bounds, (n, r, b) in zip(WINDOWS, REFERENCE, strict=True)
    ]
    windows = reference
    if path is not None:
        with path.open("rb") as stream:
            data = stream.read(SPECTRUM_SIZE + 1)
        if len(data) != SPECTRUM_SIZE:
            raise ValueError("spectrum size mismatch; refusing replay")
        if hashlib.sha256(data).hexdigest() != SPECTRUM_SHA256:
            raise ValueError("spectrum SHA-256 mismatch; refusing replay")
        windows = summarize_windows(parse_spectrum(data))
        if windows != reference:
            raise ValueError(
                "pinned table window sums disagree with review transcription"
            )
    return {
        "status": "hash-verified offline replay"
        if path is not None
        else "review summaries only; not replayed",
        "replayed": path is not None,
        "source": {
            "column_dictionary": RELEASE + "4th_result_data_release.html",
            "table": RELEASE
            + "4th_result_data_release_files/EnergySpectrum_0.1MeVbin_4th_result.dat",
            "sha256": SPECTRUM_SHA256,
            "bytes": SPECTRUM_SIZE,
            "rows": 76,
            "columns": [
                "prompt_energy_midpoint_MeV",
                "observed",
                "no_oscillation_reactor",
                "fitted_three_flavor_reactor_unused",
                "accidentals",
                "alpha_n",
                "Li_He",
                "geoneutrino_U",
                "geoneutrino_Th",
            ],
        },
        "published_sources": {
            "KamLAND_analysis_not_reproduced": "https://arxiv.org/abs/1009.4771",
            "independent_atmospheric_L_over_E_different_experiment": "https://arxiv.org/abs/hep-ex/0404034",
        },
        "descriptive_windows": windows,
        "statistic": "(N - modeled_nonreactor)/no_oscillation_reactor; floating sigma=sqrt(N)/no_oscillation_reactor (counting only)",
        "limitations": (
            "Selected prompt-energy windows; no event-by-event L/E, baseline-response map, "
            "covariance, systematic/background uncertainty, fitted significance or physical exclusion. "
            "The atmospheric result is not independent replication of these reactor windows."
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--spectrum",
        type=Path,
        help="optional local official KamLAND spectrum; exact bytes required",
    )
    args = parser.parse_args()
    try:
        empirical = spectrum_report(args.spectrum)
    except (OSError, ValueError) as exc:
        parser.error(str(exc))
    print(
        json.dumps(
            {"raw_packet": packet_report(), "kamland": empirical}, sort_keys=True
        )
    )


if __name__ == "__main__":
    main()
