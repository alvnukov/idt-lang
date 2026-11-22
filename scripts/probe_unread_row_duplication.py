"""Coherent duplicate/swap bridge from port locality to row noncontextuality.

CONDITIONAL ANALYTICAL ARGUMENT, not a Lean proof or a physical status upgrade.
Fix one preparation and an input dimension d. A complete finite test is a
Gaussian-dyadic occupied-column isometry T. Supply these operational premises:

* all required rectangular isometries, native completions, addressed disjoint
  arms and balanced coherent path embeddings are available;
* the complete output distribution depends only on the FULL occupied-column
  isometry, not its circuit history, unused completion columns or apparatus;
* relabeling outputs covariantly relabels their probabilities;
* adding zero output rows preserves all old probabilities;
* every reversible operation supported outside a named port leaves that port's
  probability unchanged (complement locality, not a derived spacetime law);
* probabilities are nonnegative and normalized over ALL output records.

No row-noncontextuality, probability splitting, amplitude-power ansatz or Born
weights are premises of the argument. No detector calibration is smuggled into
the logical certificate below. Blank stability plus nonnegative normalization
gives zero probability for new zero rows. Loss/discard/herald records cannot be
silently removed from the complete distribution.

After blank padding and relabeling, let T,S have the same m-by-d shape and
the same selected row r. Put pi=1+i and D(T,S)=[T;S]/pi. This is coherent
path embedding, psi -> (psi,psi)/pi, NOT cloning psi -> psi tensor psi.
The native B=(1/pi)[[1,1],[1,-1]] has identical copy phases. Its inverse on
every sibling pair takes D(T,T) exactly to [T;0], with no global-phase quotient.

1. In D(T,T), swapping the selected equal sibling rows fixes the FULL isometry.
   Extensionality and covariance give equal probabilities a=b. Complement
   locality and normalization conserve a pair's total when only that pair is
   changed. Undoing other sibling pairs is outside each selected port. Therefore
   undoing all pairs identifies a+b with p_T+0, and a=b=p_T/2. This derives
   probability halving; it does not infer halving merely from amplitudes.
2. Complete T,S to native square unitaries Q_T,Q_S. U=Q_S Q_T* maps EVERY
   occupied column of T to S. Applying U only on the right arm sends D(T,T)
   to D(T,S), preserving the selected left probability p_T/2. Starting from
   D(S,S) and changing only its left arm gives the right probability p_S/2.
3. The two selected rows of D(T,S) are both r/pi. Their swap fixes the whole
   isometry. Covariance and extensionality give p_T/2=p_S/2.

This bypasses, but does not refute, the direct unread-rest ideal obstruction:
((1+6i),3,3,3)/8 and ((1+6i),5,1,1)/8 have identical first rows but unread
coordinate ideals 3D and D. Zero output padding and invertible unread matrices
preserve that distinction. The duplicate construction uses larger experiments
and pair-total comparison, not a direct unread-rest transformation T -> S.

NON-DUPLICATION / BOUNDARIES. probe_native_row_probability supplies fine-row
noncontextuality before its common-Gram linearization. This supplies a route to
that premise, conditionally on the operational assumptions above. In contrast,
DyadicEffectDomainActualization supplies effect-domain sum closure/additivity
and calibration. RecordReplicationAndLocalReadout tests a monomial family;
copying distinguishable records alone there does not select an exponent. Here
coherent copies, reversible uncopying and equality of full occupied maps matter.
No arbitrary PSD boundary factorization, pure-preparation calibration, infinite
dimension, nonnative approximation, actualization or full QM is established.

The compiler uses paired logical rails, including an encoded phase operation.
Bare unpaired native T-only ports fix their uniform vector and cannot implement
B. Thus the conditional operation stock cannot be transferred to that raw model.

ROBUST FINITE CERTIFICATE. Let a,b be selected sibling masses in D(T,T), c,d
in D(S,S), and x,y in D(T,S). Define observed discrepancies
  e_T=p_T-a-b, e_S=p_S-c-d, s_T=a-b, s_S=c-d,
  l_T=a-x, l_S=d-y, s_M=x-y.
Exactly, p_T-p_S=e_T-e_S-s_T-s_S+2*l_T-2*l_S+2*s_M.
Hence the absolute gap is at most |e_T|+|e_S|+|s_T|+|s_S|
+2*(|l_T|+|l_S|+|s_M|). No discrepancy is assumed small. If simultaneous
absolute uncertainty eta on each of the eight input probabilities is supplied,
adding 22*eta is a conservative bound. The script derives no sampling interval.
Default observations are labeled SYNTHETIC; --observations reads user-supplied
exact rational frequencies, not a claim that frequencies equal true probabilities.
Near-equal amplitude rows alone give no small-error premise without a separate
operational continuity control. Later common-padding rescaling can amplify an
absolute error by 2**k, so this finite bound is not uniform robust Born closure.
"""

from __future__ import annotations

import argparse
import json
import sys
import unittest
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    I,
    Matrix,
    Move,
    eye,
    g,
    isometry,
    run,
    synthesize_isometry,
    unitary,
)

PI_INV = g(F(1, 2), F(-1, 2))
B: Matrix = ((PI_INV, PI_INV), (PI_INV, g(-1) * PI_INV))
VARIABLES = ("p_t", "p_s", "a", "b", "c", "d", "x", "y")
EQUATIONS: dict[str, dict[str, int]] = {
    "merge_t": {"p_t": 1, "a": -1, "b": -1},
    "merge_s": {"p_s": 1, "c": -1, "d": -1},
    "sibling_t": {"a": 1, "b": -1},
    "sibling_s": {"c": 1, "d": -1},
    "remote_t": {"a": 1, "x": -1},
    "remote_s": {"d": 1, "y": -1},
    "mixed_swap": {"x": 1, "y": -1},
}
CERTIFICATE = {
    "merge_t": 1,
    "merge_s": -1,
    "sibling_t": -1,
    "sibling_s": -1,
    "remote_t": 2,
    "remote_s": -2,
    "mixed_swap": 2,
}


def need(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def adjoint(a: Matrix) -> Matrix:
    return tuple(tuple(a[j][i].star() for j in range(len(a))) for i in range(len(a[0])))


def multiply(a: Matrix, b: Matrix) -> Matrix:
    if not a or not b or any(len(row) != len(b) for row in a):
        raise ValueError("incompatible nonempty matrix dimensions")
    return tuple(
        tuple(
            sum((x * b[k][j] for k, x in enumerate(row)), ZERO)
            for j in range(len(b[0]))
        )
        for row in a
    )


def inverse_word(word: tuple[Move, ...]) -> tuple[Move, ...]:
    return tuple(op for op in reversed(word) for _ in range(3))


def readdress(word: tuple[Move, ...], addresses: tuple[int, ...]) -> tuple[Move, ...]:
    return tuple((tag, addresses[j], addresses[k]) for tag, j, k in word)


def duplicate(t: Matrix, s: Matrix) -> Matrix:
    if len(t) != len(s) or len(t[0]) != len(s[0]):
        raise ValueError("pad to the same shape before duplicating")
    return tuple(tuple(PI_INV * value for value in row) for row in t + s)


def example(width: int) -> tuple[Matrix, Matrix]:
    if width < 1:
        raise ValueError("positive input dimension")
    first = g(F(1, 8), F(6, 8))
    left = (first, g(F(3, 8)), g(F(3, 8)), g(F(3, 8)))
    right = (first, g(F(5, 8)), g(F(1, 8)), g(F(1, 8)))
    tail = tuple(
        tuple(ONE if i == j else ZERO for j in range(width)) for i in range(1, width)
    )
    t = tuple((value,) + (ZERO,) * (width - 1) for value in left) + tail
    s = tuple((value,) + (ZERO,) * (width - 1) for value in right) + tail
    # Nontrivially mix input columns, retaining equality of the entire named row.
    word: tuple[Move, ...] = tuple(("T", j, j + 1) for j in range(width - 1))
    frame = run(eye(width), word + (("i", 0, 0),) if width > 1 else word)
    return multiply(t, frame), multiply(s, frame)


def matrix_chain(t: Matrix, s: Matrix, selected: int = 0) -> dict[str, object]:
    need(isometry(t) and isometry(s), "native tests")
    need(len(t) == len(s) and t[selected] == s[selected], "same shape and exact row")
    m, width = len(t), len(t[0])
    wt, ws = synthesize_isometry(t), synthesize_isometry(s)
    qt, qs = run(eye(m), wt), run(eye(m), ws)
    need(tuple(row[:width] for row in qt) == t, "T completion columns")
    need(tuple(row[:width] for row in qs) == s, "S completion columns")
    u = multiply(qs, adjoint(qt))
    need(unitary(u) and multiply(u, t) == s, "whole occupied-column arm map")
    tt, ss, ts = duplicate(t, t), duplicate(s, s), duplicate(t, s)
    need(all(isometry(test) for test in (tt, ss, ts)), "all doubled tests")
    right_word = readdress(inverse_word(wt) + ws, tuple(range(m, 2 * m)))
    left_word = inverse_word(ws) + wt
    need(run(tt, right_word) == ts, "right-only change T to S")
    need(run(ss, left_word) == ts, "left-only change S to T")
    need(all(j >= m and k >= m for _, j, k in right_word), "left named port untouched")
    need(all(j < m and k < m for _, j, k in left_word), "right named port untouched")
    for test in (tt, ss, ts):
        swapped = list(test)
        swapped[selected], swapped[m + selected] = (
            swapped[m + selected],
            swapped[selected],
        )
        need(tuple(swapped) == test, "selected equal-row swap fixes full isometry")
    wb = synthesize_isometry(B)
    need(run(eye(2), wb) == B, "exact balanced splitter compilation")
    inverse_pairs = tuple(readdress(inverse_word(wb), (j, m + j)) for j in range(m))
    all_inverse = tuple(op for pair in inverse_pairs for op in pair)
    padded = t + ((ZERO,) * width,) * m
    need(run(tt, all_inverse) == padded, "uncopy gives exact T plus blank rows")
    need(run(padded, inverse_word(all_inverse)) == tt, "coherent copy is reversible")
    selected_pair = {selected, m + selected}
    need(
        all(
            j not in selected_pair and k not in selected_pair
            for index, pair in enumerate(inverse_pairs)
            if index != selected
            for _, j, k in pair
        ),
        "all other uncopy gates are outside both named siblings",
    )
    return {
        "input_columns": width,
        "original_outputs": m,
        "completion_moves": [len(wt), len(ws)],
        "right_only_moves": len(right_word),
        "balanced_splitter_moves": len(wb),
        "full_map_swap_and_uncopy": "exact",
    }


def certificate_check() -> None:
    combined = {
        variable: sum(
            CERTIFICATE[name] * equation.get(variable, 0)
            for name, equation in EQUATIONS.items()
        )
        for variable in VARIABLES
    }
    need(
        combined
        == {
            variable: int(variable == "p_t") - int(variable == "p_s")
            for variable in VARIABLES
        },
        "exact symbolic probability-gap certificate without Born values",
    )


def pair_total_certificate(outputs: int, first: int, second: int) -> None:
    """Derive pair mass from complete normalization and complementary masses.

    X is duplicated, V has only this pair unmerged, P has all pairs unmerged.
    P_first=p_T and P_second=0 come from blank stability and normalization.
    Every row below is a separately justified zero discrepancy, not a Born
    assignment. The sum is X_first+X_second-p_T.
    """
    if not 0 <= first < second < outputs:
        raise ValueError("two distinct valid ordered outputs required")
    terms: list[dict[str, int]] = [
        {
            f"{name}{j}": sign
            for name, sign in (("X", 1), ("V", -1))
            for j in range(outputs)
        }
    ]
    terms.extend(
        {f"X{j}": -1, f"V{j}": 1} for j in range(outputs) if j not in (first, second)
    )
    terms.extend({f"V{j}": 1, f"P{j}": -1} for j in (first, second))
    terms.extend(({f"P{first}": 1, "p_t": -1}, {f"P{second}": 1}))
    keys = set().union(*(term.keys() for term in terms))
    total = {key: sum(term.get(key, 0) for term in terms) for key in keys}
    need(
        {key: value for key, value in total.items() if value}
        == {f"X{first}": 1, f"X{second}": 1, "p_t": -1},
        "pair-total derivation from complete records and complement locality",
    )


@dataclass(frozen=True)
class Observations:
    values: dict[str, F]

    def __post_init__(self) -> None:
        if set(self.values) != set(VARIABLES) or any(
            value < 0 or value > 1 for value in self.values.values()
        ):
            raise ValueError("exactly eight named probabilities in [0,1] required")
        for left, right in (("a", "b"), ("c", "d"), ("x", "y")):
            if self.values[left] + self.values[right] > 1:
                raise ValueError("selected sibling probabilities exceed one")

    def report(self, radius: F = F(0)) -> dict[str, object]:
        if radius < 0:
            raise ValueError("nonnegative simultaneous coordinate uncertainty required")
        discrepancies = {
            name: sum(
                (coefficient * self.values[key] for key, coefficient in row.items()),
                F(0),
            )
            for name, row in EQUATIONS.items()
        }
        gap = self.values["p_t"] - self.values["p_s"]
        need(
            gap
            == sum(
                (CERTIFICATE[name] * value for name, value in discrepancies.items()),
                F(0),
            ),
            "numerical evaluation of symbolic certificate",
        )
        budget = sum(
            (abs(CERTIFICATE[name] * value) for name, value in discrepancies.items()),
            F(0),
        )
        uncertainty_factor = sum(
            abs(CERTIFICATE[name])
            * sum(abs(coefficient) for coefficient in row.values())
            for name, row in EQUATIONS.items()
        )
        need(
            abs(gap) <= budget and uncertainty_factor == 22,
            "triangle bound and uncertainty accounting",
        )
        return {
            "signed_discrepancies": {
                name: str(value) for name, value in discrepancies.items()
            },
            "absolute_row_gap": str(abs(gap)),
            "discrepancy_budget": str(budget),
            "supplied_simultaneous_coordinate_radius": str(radius),
            "conditional_population_bound": str(
                min(F(1), budget + uncertainty_factor * radius)
            ),
            "warning": "radius is supplied, not a derived sampling confidence interval",
        }


def negative_controls() -> dict[str, object]:
    t, s = example(1)

    def residue(value: Gaussian) -> tuple[int, int]:
        residues = tuple(
            x.numerator * pow(x.denominator, -1, 3) % 3 for x in (value.re, value.im)
        )
        return residues[0], residues[1]

    need(all(residue(row[0]) == (0, 0) for row in t[1:]), "unread 3D ideal")
    need(
        t[1][0] == g(F(3, 8)) and s[2][0] == g(F(1, 8)),
        "unread ideals exactly 3D and D",
    )
    need(residue(s[2][0]) != (0, 0), "odd ideal not inverted by dyadic localization")
    before = ((g(F(1, 2)),),) * 4
    after = before[:2] + multiply(B, before[2:])
    need(
        isometry(before) and isometry(after) and before[0] == after[0],
        "remote splitter holds named row fixed",
    )

    def quartic_first(test: Matrix) -> F:
        weights = tuple(row[0].norm2() ** 2 for row in test)
        return weights[0] / sum(weights)

    quartic = (quartic_first(before), quartic_first(after))
    need(quartic == (F(1, 4), F(1, 6)), "quartic violates complement locality")
    need(multiply(adjoint(B), B) == eye(2), "split then inverse has identity endpoint")
    history_identity, history_split_unsplit = (F(1), F(0)), (F(1, 2), F(1, 2))
    need(
        history_identity != history_split_unsplit,
        "classical gate records violate occupied-map extensionality",
    )
    uniform = ((ONE,), (ONE,))
    bare = run(eye(2), (("T", 0, 1),))
    need(multiply(bare, uniform) == uniform, "raw T fixes uniform line")
    need(
        multiply(B, uniform) != uniform,
        "balanced logical splitter ineligible for bare T-only stock",
    )
    need(
        multiply(((I, ZERO), (ZERO, ONE)), uniform) != uniform,
        "local phase also not bare T-only",
    )
    return {
        "direct_unread_ideals": ["3D", "D"],
        "direct_wall_scope": "persists under zero padding; duplication bypasses it via different comparisons",
        "quartic_remote_first_probabilities": [str(value) for value in quartic],
        "classical_history_identity": [str(value) for value in history_identity],
        "classical_history_split_inverse": [
            str(value) for value in history_split_unsplit
        ],
        "history_scope": "a classical equal-branch update at each splitter keeps records; not a reversible apparatus model",
        "raw_T_only_eligibility": False,
        "paired_logical_operation_stock": "supplied; physical acceptance and readout not derived",
    }


def synthetic_observations() -> Observations:
    return Observations(
        dict(
            zip(
                VARIABLES,
                (
                    F(3, 5),
                    F(11, 20),
                    F(31, 100),
                    F(29, 100),
                    F(27, 100),
                    F(28, 100),
                    F(3, 10),
                    F(29, 100),
                ),
                strict=True,
            )
        )
    )


def audit() -> dict[str, object]:
    certificate_check()
    for outputs in (8, 10, 12):
        pair_total_certificate(outputs, 0, outputs // 2)
    return {
        "ok": True,
        "matrix_chains": [matrix_chain(*example(width)) for width in (1, 2, 3)],
        "symbolic_certificate": CERTIFICATE,
        "negative_controls": negative_controls(),
        "synthetic_not_experimental_budget": synthetic_observations().report(),
        "boundary": "conditional row-noncontextuality bridge; no Born premise in certificate, no physical or Lean status upgrade",
    }


class DuplicationTests(unittest.TestCase):
    def test_matrix_chains(self) -> None:
        for width in (1, 2, 3):
            self.assertEqual(matrix_chain(*example(width))["input_columns"], width)

    def test_symbolic_certificate(self) -> None:
        certificate_check()
        for outputs in range(2, 13):
            pair_total_certificate(outputs, 0, outputs - 1)

    def test_exact_logical_observations(self) -> None:
        values = (F(3, 5), F(3, 5)) + (F(3, 10),) * 6
        report = Observations(dict(zip(VARIABLES, values, strict=True))).report()
        self.assertEqual(report["discrepancy_budget"], "0")

    def test_nonzero_discrepancy_budget(self) -> None:
        report = synthetic_observations().report(F(1, 1000))
        self.assertEqual(report["absolute_row_gap"], "1/20")
        self.assertEqual(report["discrepancy_budget"], "9/100")
        self.assertEqual(report["conditional_population_bound"], "14/125")

    def test_negative_controls(self) -> None:
        self.assertFalse(negative_controls()["raw_T_only_eligibility"])

    def test_reject_incomplete_or_invalid_observations(self) -> None:
        with self.assertRaises(ValueError):
            Observations({"p_t": F(1)})
        with self.assertRaises(ValueError):
            Observations(dict.fromkeys(VARIABLES, F(1)))
        with self.assertRaises(ValueError):
            synthetic_observations().report(F(-1))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--observations",
        type=Path,
        help="JSON object: p_t,p_s,a,b,c,d,x,y as rational strings",
    )
    parser.add_argument(
        "--coordinate-radius",
        default="0",
        help="supplied simultaneous absolute probability error, not estimated here",
    )
    args = parser.parse_args()
    result = audit()
    if args.observations is not None:
        raw: object = json.loads(args.observations.read_text())
        if not isinstance(raw, dict) or any(
            not isinstance(key, str) or not isinstance(value, (str, int))
            for key, value in raw.items()
        ):
            raise ValueError("JSON object with rational strings or integers required")
        observations = Observations({key: F(value) for key, value in raw.items()})
        result["supplied_observations_not_independently_calibrated"] = (
            observations.report(F(args.coordinate_radius))
        )
    elif F(args.coordinate_radius) != 0:
        parser.error("--coordinate-radius requires --observations")
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(
            "PASS: exact coherent duplicate/swap/uncopy chains in input dimensions 1, 2, 3."
        )
        print(
            "PASS: probability-gap certificate uses only operational discrepancies, not Born weights."
        )
        print(
            "PASS: direct odd-ideal, remote quartic, history, and unpaired raw-port controls."
        )
        print(result["boundary"])


if __name__ == "__main__":
    main()
