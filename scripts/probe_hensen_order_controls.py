"""Exact conditional order control; network-free, with optional pinned raw input.

FIXED ANALYSIS: reuse the released Hensen2015 selection/readout recipe in
theory_experiments.bell_trial_test without changing cuts. Within each
(measurement day, measurement run, setting A, setting B) accepted subsequence,
count sign changes between neighboring entries. These are NOT neighboring
raw triggers, attempts, or necessarily neighboring accepted trials overall.

For each party separately the null is conditional exchangeability in this
specific strong form: conditional on the accepted setting sequence, author
day/run labels and that party's positive/negative counts in every stratum,
all within-stratum binary assignments are equiprobable under the product of
the stratum permutation groups. Independent Bernoulli outcomes with a fixed
probability per stratum suffice, but are NOT inferred from a Bell violation.
Neither general memorylessness nor independence of settings is established.

The statistic is the sum of within-stratum transitions. Its conditional
distribution is an exact convolution of binary runs counts. Two-sided p is
min(1, 2*min(lower inclusive tail, upper inclusive tail)). Bonferroni correct
the two separately tested party outcomes; no independence between parties is
assumed by that correction. The fixed family threshold is 1/20. This is a
retrospective exploratory control, not prospective empirical validation.

No outcomes, change points, timing windows or run boundaries are optimized.
The author's approximately 45-minute runs and accepted settings are the
strata. Released records are already broadly two-photon preselected; all
emitted/attempted triggers are unavailable. Detector/reset/selection effects
and between-context or cross-party memory can escape this statistic. Failure
to reject is not evidence of independence, a rotor, or IDT-specific physics.

Default execution checks synthetic exact controls only and reports empirical
status not_tested. --raw-file accepts only the existing checksum-pinned
bell_open_data.txt. This script never downloads, writes, or redistributes raw
data. The 4TU metadata gives General Terms of Use, not a verified open raw-
redistribution license. The exact run-count combinatorics are not Lean proofs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import unittest
from collections import Counter, defaultdict
from collections.abc import Sequence
from fractions import Fraction
from functools import cache
from itertools import pairwise, product
from math import comb
from pathlib import Path
from typing import cast

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_experiments.bell_trial_test import (
    RAW_SHA256,
    RAW_SIZE,
    assert_loaded_sources,
    read_pinned_raw,
    reduce_records,
    reviewed_counts,
    source_hashes,
)

FAMILY_ALPHA = Fraction(1, 20)
Stratum = tuple[int, int, int, int]


def require(condition: bool, message: object) -> None:
    if not condition:
        raise AssertionError(message)


def transitions(word: Sequence[int]) -> int:
    if any(sign not in (-1, 1) for sign in word):
        raise ValueError("binary outcome signs required")
    return sum(left != right for left, right in pairwise(word))


def choose(n: int, k: int) -> int:
    return comb(n, k) if 0 <= k <= n else 0


@cache
def transition_counts(positive: int, negative: int) -> tuple[tuple[int, int], ...]:
    """Number of binary assignments at each transition count, fixed margins.

    With both signs present and r runs: r=2k has two endpoint orientations,
    each with C(a-1,k-1)C(b-1,k-1) compositions. r=2k+1 has k+1 runs of
    one sign and k of the other. Transitions are runs minus one.
    """
    if min(positive, negative) < 0 or positive + negative > 512:
        raise ValueError("nonnegative counts and total <=512 required")
    if min(positive, negative) == 0:
        return ((0, 1),)
    counts: list[tuple[int, int]] = []
    for runs in range(2, positive + negative + 1):
        k = runs // 2
        if runs % 2 == 0:
            count = 2 * choose(positive - 1, k - 1) * choose(negative - 1, k - 1)
        else:
            count = choose(positive - 1, k) * choose(negative - 1, k - 1) + choose(
                positive - 1, k - 1
            ) * choose(negative - 1, k)
        if count:
            counts.append((runs - 1, count))
    require(
        sum(count for _, count in counts) == comb(positive + negative, positive),
        "exact runs count does not exhaust fixed-margin assignments",
    )
    return tuple(counts)


def convolve(left: dict[int, int], right: Sequence[tuple[int, int]]) -> dict[int, int]:
    out: Counter[int] = Counter()
    for x, nx in left.items():
        for y, ny in right:
            out[x + y] += nx * ny
    return dict(out)


def two_sided_p(distribution: dict[int, int], observed: int) -> Fraction:
    if observed not in distribution or any(
        count <= 0 for count in distribution.values()
    ):
        raise ValueError(
            "observation must lie in a positive conditional count distribution"
        )
    total = sum(distribution.values())
    lower = sum(count for value, count in distribution.items() if value <= observed)
    upper = sum(count for value, count in distribution.items() if value >= observed)
    return min(Fraction(1), Fraction(2 * min(lower, upper), total))


def party_test(words: Sequence[Sequence[int]]) -> dict[str, object]:
    if not words or any(not word for word in words) or sum(map(len, words)) > 512:
        raise ValueError("nonempty strata, total observations 1..512 required")
    distribution = {0: 1}
    observed = informative = 0
    expected = Fraction(0)
    assignments = 1
    for word in words:
        observed += transitions(word)
        positive, negative = word.count(1), word.count(-1)
        local = transition_counts(positive, negative)
        informative += len(local) > 1
        expected += Fraction(2 * positive * negative, len(word))
        assignments *= comb(len(word), positive)
        distribution = convolve(distribution, local)
    require(sum(distribution.values()) == assignments, "product null assignments")
    require(
        Fraction(
            sum(value * count for value, count in distribution.items()), assignments
        )
        == expected,
        "independent conditional mean check",
    )
    p = two_sided_p(distribution, observed)
    adjusted = min(Fraction(1), 2 * p)
    smallest = min(two_sided_p(distribution, value) for value in distribution)
    smallest_adjusted = min(Fraction(1), 2 * smallest)
    return {
        "observations": sum(map(len, words)),
        "strata": len(words),
        "informative_strata": informative,
        "same_stratum_subsequence_neighbors": sum(len(word) - 1 for word in words),
        "observed_transitions": observed,
        "expected_transitions_exact": str(expected),
        "null_support": [min(distribution), max(distribution)],
        "conditional_assignments": str(assignments),
        "null_counts": [
            [value, str(count)] for value, count in sorted(distribution.items())
        ],
        "two_sided_p_exact": str(p),
        "two_sided_p_display": float(p),
        "two_party_bonferroni_p_exact": str(adjusted),
        "smallest_attainable_bonferroni_p_exact": str(smallest_adjusted),
        "rejection_possible_at_family_alpha": smallest_adjusted <= FAMILY_ALPHA,
        "conditional_null_rejected": adjusted <= FAMILY_ALPHA,
    }


def accepted_strata(reduced: dict[str, object]) -> dict[Stratum, list[tuple[int, int]]]:
    """Use only author run/day labels and accepted settings; preserve row order."""
    strata: dict[Stratum, list[tuple[int, int]]] = defaultdict(list)
    records = cast(list[dict[str, object]], reduced["records"])
    for row in records:
        if row["accepted"] is True:
            fields = cast(list[str], row["source_fields"])
            key = (
                int(fields[1]),
                int(fields[2]),
                cast(int, row["a"]),
                cast(int, row["b"]),
            )
            strata[key].append((cast(int, row["x"]), cast(int, row["y"])))
    return dict(strata)


def analyze_pinned_bytes(raw: bytes) -> dict[str, object]:
    """Pure in-memory analysis of the exact pinned data; no network or writes."""
    assert_loaded_sources()
    sources = source_hashes()
    analysis_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if len(raw) != RAW_SIZE or hashlib.sha256(raw).hexdigest() != RAW_SHA256:
        raise ValueError("raw size/digest mismatch; not a physics rejection")
    reduced = reduce_records(raw.decode("ascii"))
    registry = reviewed_counts()
    expected = cast(dict[str, object], registry["reviewed_counts"])
    if {key: reduced[key] for key in expected} != expected:
        raise ValueError("released-record reduction differs from the fixed recipe")
    strata = accepted_strata(reduced)
    parties = {
        name: party_test(
            [[outcomes[index] for outcomes in rows] for rows in strata.values()]
        )
        for index, name in enumerate(("Alice", "Bob"))
    }
    require(source_hashes() == sources, "source files changed during analysis")
    require(
        hashlib.sha256(Path(__file__).read_bytes()).hexdigest() == analysis_hash,
        "analysis source changed during analysis",
    )
    return {
        "empirical_status": "conditional_order_test_completed",
        "raw_sha256": RAW_SHA256,
        "released_rows": reduced["released_rows"],
        "accepted_trials": reduced["N"],
        "author_day_run_groups": len({key[:2] for key in strata}),
        "accepted_setting_strata": len(strata),
        "stratum_size_histogram": dict(
            sorted(Counter(map(len, strata.values())).items())
        ),
        "family_alpha_exact": str(FAMILY_ALPHA),
        "parties": parties,
        "source_sha256": sources,
        "analysis_source_sha256": analysis_hash,
        "conditioning": "accepted settings a,b and author day/run; each party's signs conditioned on its own stratum counts",
        "neighbor_definition": "neighbors on the same-(day,run,a,b) accepted subsequence; not raw-trigger neighbors",
        "interpretation": "failure to reject does not establish independence or an event-memory/rotor model",
        "dataset_doi": "10.4121/uuid:6e19e9b2-4a2d-40b5-8dd3-a660bf3c0a31",
        "license_boundary": "4TU General Terms of Use; no raw data bundled or redistribution permission asserted",
    }


def exact_controls() -> dict[str, object]:
    for size in range(11):
        for positive in range(size + 1):
            brute = Counter(
                transitions(word)
                for word in product((-1, 1), repeat=size)
                if word.count(1) == positive
            )
            require(
                dict(brute) == dict(transition_counts(positive, size - positive)),
                "exhaustive binary-word oracle",
            )
    deterministic = party_test(((1,), (-1,), (1, -1), (-1, 1), (1, 1)))
    require(
        deterministic["informative_strata"] == 0,
        "fixed margins may remove all information",
    )
    require(
        deterministic["smallest_attainable_bonferroni_p_exact"] == "1",
        "uninformative null",
    )
    synthetic = party_test((tuple([1] * 10 + [-1] * 10),))
    require(
        synthetic["two_party_bonferroni_p_exact"] == "2/46189", "synthetic clustering"
    )
    return {
        "exact_controls": "passed",
        "oracle": "all binary words of lengths zero through ten",
        "uninformative_margin_control": "passed",
        "synthetic_clustering_control": "passed",
        "empirical_status": "not_tested_without_optional_pinned_raw_file",
    }


class OrderControlTests(unittest.TestCase):
    def test_exhaustive_oracle(self) -> None:
        self.assertEqual(exact_controls()["exact_controls"], "passed")

    def test_independent_convolution_oracle(self) -> None:
        words1 = [word for word in product((-1, 1), repeat=4) if word.count(1) == 2]
        words2 = [word for word in product((-1, 1), repeat=3) if word.count(1) == 1]
        brute = Counter(
            transitions(a) + transitions(b) for a, b in product(words1, words2)
        )
        self.assertEqual(
            convolve(dict(transition_counts(2, 2)), transition_counts(1, 2)),
            dict(brute),
        )

    def test_sign_flip_reversal_and_stratum_order(self) -> None:
        words = ((1, 1, -1, 1, -1), (-1, 1, -1, -1))
        transformed = tuple(
            tuple(-sign for sign in reversed(word)) for word in reversed(words)
        )
        self.assertEqual(party_test(words), party_test(transformed))

    def test_day_run_settings_define_subsequence_neighbors(self) -> None:
        records: list[dict[str, object]] = []
        for run, a, x in ((1, 0, 1), (1, 1, -1), (1, 0, -1), (2, 0, 1)):
            records.append(
                {
                    "accepted": True,
                    "source_fields": ["time", "1", str(run)],
                    "a": a,
                    "b": 0,
                    "x": x,
                    "y": 1,
                }
            )
        records.append({"accepted": False})
        strata = accepted_strata({"records": records})
        self.assertEqual(strata[(1, 1, 0, 0)], [(1, 1), (-1, 1)])
        self.assertEqual(len(strata), 3)
        self.assertEqual(sum(len(rows) - 1 for rows in strata.values()), 1)

    def test_invalid_inputs_and_wrong_raw(self) -> None:
        with self.assertRaises(ValueError):
            transitions((1, 0))
        with self.assertRaises(ValueError):
            transition_counts(-1, 2)
        with self.assertRaises(ValueError):
            party_test(())
        with self.assertRaises(ValueError):
            analyze_pinned_bytes(b"not the pinned data")

    def test_exact_pvalue_and_marginal_information_wall(self) -> None:
        result = party_test(((1, 1, -1), (1, 1, 1, -1)))
        self.assertEqual(result["two_sided_p_exact"], "2/3")
        self.assertEqual(result["two_party_bonferroni_p_exact"], "1")
        self.assertEqual(result["smallest_attainable_bonferroni_p_exact"], "2/3")
        self.assertFalse(result["rejection_possible_at_family_alpha"])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--raw-file",
        type=Path,
        help="optional local checksum-pinned bell_open_data.txt",
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    try:
        result = exact_controls()
        if args.raw_file is not None:
            result["empirical"] = analyze_pinned_bytes(read_pinned_raw(args.raw_file))
            result["empirical_status"] = "conditional_order_test_completed"
        if args.json:
            print(json.dumps(result, indent=2, sort_keys=True))
        else:
            print(
                "PASS: exact conditional-runs controls and exhaustive short-word oracle."
            )
            print("Empirical status:", result["empirical_status"])
            if "empirical" in result:
                empirical = cast(dict[str, object], result["empirical"])
                print(
                    json.dumps(
                        {
                            key: empirical[key]
                            for key in (
                                "accepted_trials",
                                "accepted_setting_strata",
                                "parties",
                            )
                        },
                        sort_keys=True,
                    )
                )
            print(
                "Condition only on accepted settings and author day/run; no new cuts or change points."
            )
            print(
                "Subsequence neighbors are not raw triggers. No independence or rotor acceptance follows."
            )
        return 0
    except (OSError, ValueError, UnicodeError) as error:
        print(
            f"hensen_order_control: input error, not physics rejection: {error}",
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
