"""A conditional three-family RAW-port magnitude wall, not an IDT falsification.

The model being tested identifies the three observed family labels with ONE
raw three-port carrier. Its only reversible generators are addressed
T=((1+i,1-i),(1-i,1+i))/2 with identity bypass. Every word U is unitary,
fixes s=(1,1,1), and has det(U) in {1,i,-1,-i}. Two up/down embeddings give
the SAME constraint for U_up* U_down only when BOTH use this same aligned
carrier and basis. Arbitrary changes of embedding, encoded paired logical
rails, additional phase controls or a larger carrier are not covered.

DETERMINANT LOCK. The centered two-dimensional block has eigenvalues lambda1,
lambda2. If det U=i, tr U=1+(1+i)t for real t, so |3-tr U|^2>=2; det=-i
is analogous, and det=-1 gives |3-tr U|^2>=4. Row sums give
  |3-tr U| <= S = sum_{i!=j}|Uij|.
Thus S<sqrt(2) forces det U=1. All numerical uses below compare exact squares,
not floating thresholds. A second sufficient lock is ||U-I||_infinity<
2*sqrt(2)/3, since row sums imply ||U-I||_infinity>=2|3-tr U|/3.

The spectral/Euclidean operator-norm lock radius sqrt(2-sqrt(2)) is SHARP
for the containing class of fixed-uniform unitaries with det in mu4: at the
boundary P_uniform+exp(i*pi/4)P_center has determinant i. This is NOT claimed
to be the sharp induced-infinity-norm radius or an exact finite native word.
The simple bound ||U-I||_infinity<=2 max_i sum_{j!=i}|Uij| also holds.

TRIANGLE THEOREM, analytical argument rather than Lean proof. For det U=1,
the centered block V is in SU(2), hence V+V*=2cI with real c=tr(V)/2.
Consequently U+U*=2cI+2(1-c)P_uniform. Row/column sums then give
  U12=a+ix, U23=a+iy, U31=a+iz,
  U21=b+ix, U32=b+iy, U13=b+iz,
with real a,b,x,y,z and x+y+z=0 (the last identity uses real trace).
For example (a,x)=(a/2,-y)+(a/2,-z); the Euclidean triangle inequality
implies |U12|<=|U23|+|U31|. Both oriented cycles obey all three triangle
inequalities. The finite exact native-word controls check these identities
without replacing magnitude inequalities by squared-magnitude inequalities.

PHASES / LABELS. Arbitrary diagonal row/column rephasings preserve magnitudes
but need not preserve the raw group. The exclusion asks whether ANY raw
representative has those magnitudes: row sums force that representative's
diagonals near 1 when aligned offdiagonals are small, irrespective of the
conventional CKM phases. Independent row/column permutations DO preserve the
raw group (T^2 is an address swap). Align the three uniquely dominant entries
first; remaining simultaneous label permutations merely exchange the cycles.
Neither an arbitrary convention for det(CKM) nor a preferred CKM phase is used.

FIXED COMPARATOR. PDG 2024, CKM review, eq. (12.27), p.12, dated May 31 2024:
https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf
Primary PDF pin supplied by the coordinating source audit:
SHA256 2e4dc8575ff12482a2b40c4f7ced7e4983a8d2f0748ca58d4809b088f3faf942.
This network-free script checks the transcribed table arithmetically; it does
not independently retrieve/checksum the PDF. These are global-fit magnitudes,
not raw event data. Marginal reported ranges are used as a rectangular
robustness box, NOT an independently calibrated joint confidence region or
p-value. Rounding means the central table is not treated as exactly unitary.

The central reverse-cycle gap is .22487-.04111-.003732=.180028. Therefore
every raw candidate has sup magnitude distance at least .180028/3 from this
table: at that radius its total offdiagonal mass remains <sqrt(2), so leaving
the determinant-one sector cannot escape the triangle. The analogous box
gap is .178488, giving distance >=.059496 for every table inside the box.
These are lower bounds, not claimed optimal distances or a significance level.

THREE-INPUT WITNESS. For a=|U12|, b=|U23|, c=|U13|, unitary cofactors give
|U31|<=ab+c, |U21|<=a+c, |U32|<=b+c. Thus S<=2a+2b+ab+4c. The separate
coarse box a in [.20,.25], b<=.06, c<=.01 forces S<=.675<sqrt(2), then the
triangle forces a(1-b)<=b+c. But .20*(1-.06)=.188>.07. This conditional
test uses only those THREE input intervals plus unitarity, not fitted |U31|.
The box is an explicit conservative comparator covering the quoted values;
this script does not manufacture independent experimental intervals for it.

NEGATIVE CONTROLS. A single native T01 (det=i) has one isolated nonzero
offdiagonal pair and violates a cycle triangle. If arbitrary determinant phase
is allowed, I+(zeta-1)ww*, w=(1,-1,0)/sqrt(2), has only that pair mixed with
arbitrarily small magnitude. This is outside the raw gate stock. The wall
does not exclude physical CP violation, CKM theory, encoded carriers, general
IDT, or a model with a separately justified nonaligned family embedding.
"""

from __future__ import annotations

import argparse
import json
import sys
import unittest
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    I,
    Matrix,
    apply,
    eye,
    g,
    run,
    unitary,
)

SOURCE_URL = "https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf"
SOURCE_SHA256 = "2e4dc8575ff12482a2b40c4f7ced7e4983a8d2f0748ca58d4809b088f3faf942"
PHASES = (ONE, I, g(-1), g(0, -1))
CYCLES = (((0, 1), (1, 2), (2, 0)), ((1, 0), (2, 1), (0, 2)))
Magnitudes = tuple[tuple[F, ...], ...]


def need(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


@dataclass(frozen=True)
class Entry:
    central: F
    low: F
    high: F

    def __post_init__(self) -> None:
        if not 0 <= self.low <= self.central <= self.high <= 1:
            raise ValueError("invalid magnitude interval")


def entry(value: str, below: str, above: str | None = None) -> Entry:
    center = F(value)
    return Entry(center, center - F(below), center + F(above or below))


PDG = (
    (
        entry(".97435", ".00016"),
        entry(".22501", ".00068"),
        entry(".003732", ".000085", ".000090"),
    ),
    (
        entry(".22487", ".00068"),
        entry(".97349", ".00016"),
        entry(".04183", ".00069", ".00079"),
    ),
    (
        entry(".00858", ".00017", ".00019"),
        entry(".04111", ".00068", ".00077"),
        entry(".999118", ".000034", ".000029"),
    ),
)


def adjoint(a: Matrix) -> Matrix:
    return tuple(tuple(a[j][i].star() for j in range(3)) for i in range(3))


def multiply(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(sum((a[i][k] * b[k][j] for k in range(3)), ZERO) for j in range(3))
        for i in range(3)
    )


def determinant(a: Matrix) -> Gaussian:
    return (
        a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
        - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
        + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])
    )


def magnitude_squares(a: Matrix) -> Magnitudes:
    return tuple(tuple(value.norm2() for value in row) for row in a)


def triangle_squared(sides: tuple[F, ...]) -> bool:
    """Exact triangle test on SQUARED side lengths, retaining the cross term."""
    largest = max(sides)
    rest = list(sides)
    rest.remove(largest)
    excess = largest - sum(rest, F(0))
    return excess <= 0 or excess * excess <= 4 * rest[0] * rest[1]


def raw_constraints(a: Matrix) -> Gaussian:
    need(unitary(a), "unitary raw word")
    need(all(sum(row, ZERO) == ONE for row in a), "fixed uniform vector")
    need(
        all(sum((a[i][j] for i in range(3)), ZERO) == ONE for j in range(3)),
        "fixed uniform covector",
    )
    det = determinant(a)
    need(det in PHASES, "determinant in mu4")
    need(
        det * a[2][0].star() == a[0][1] * a[1][2] - a[0][2] * a[1][1]
        and det * a[1][0].star() == a[0][2] * a[2][1] - a[0][1] * a[2][2]
        and det * a[2][1].star() == a[0][2] * a[1][0] - a[0][0] * a[1][2],
        "three-input unitary cofactor identities",
    )
    trace = sum((a[i][i] for i in range(3)), ZERO)
    if det == ONE:
        need(trace.im == 0, "real SU2 centered trace")
        c = (trace.re - 1) / 2
        need(
            all(
                a[i][j] + a[j][i].star() == g(2 * c * F(i == j) + F(2, 3) * (1 - c))
                for i in range(3)
                for j in range(3)
            ),
            "SU2 Hermitian-part identity",
        )
        for cycle in CYCLES:
            values = tuple(a[i][j] for i, j in cycle)
            need(
                len({value.re for value in values}) == 1
                and sum((value.im for value in values), F(0)) == 0,
                "equal cycle real parts and zero imaginary sum",
            )
            need(
                triangle_squared(tuple(value.norm2() for value in values)),
                "oriented cycle triangle",
            )
        need(
            all(a[i][j].im == a[j][i].im for i in range(3) for j in range(3)),
            "symmetric imaginary offdiagonals",
        )
    else:
        minimum = F(4) if det == g(-1) else F(2)
        need((g(3) - trace).norm2() >= minimum, "trace determinant-lock inequality")
    return det


def native_controls(depth: int = 6) -> dict[str, int]:
    layer = [eye(3)]
    counts = {"all_words": 0, "determinant_one_words": 0}
    for length in range(depth + 1):
        for matrix in layer:
            det = raw_constraints(matrix)
            need(det == PHASES[length % 4], "native determinant exponent")
            counts["all_words"] += 1
            counts["determinant_one_words"] += int(det == ONE)
        layer = [
            apply(matrix, ("T", i, j))
            for matrix in layer
            for i, j in ((0, 1), (1, 2), (0, 2))
        ]
    up = run(eye(3), (("T", 0, 1), ("T", 1, 2), ("T", 0, 2)))
    down = run(eye(3), (("T", 1, 2), ("T", 0, 2), ("T", 0, 1), ("T", 1, 2)))
    relative = multiply(adjoint(up), down)
    need(
        raw_constraints(relative) == I,
        "two SAME-aligned-carrier embeddings retain constraint",
    )
    sample = run(eye(3), (("T", 0, 1), ("T", 1, 2)) * 2)
    for row_order in permutations(range(3)):
        for col_order in permutations(range(3)):
            permuted = tuple(tuple(sample[i][j] for j in col_order) for i in row_order)
            raw_constraints(permuted)
    for left in PHASES:
        for right in PHASES:
            rephased = tuple(
                tuple(
                    (left if i == 0 else ONE)
                    * sample[i][j]
                    * (right if j == 1 else ONE)
                    for j in range(3)
                )
                for i in range(3)
            )
            need(
                magnitude_squares(rephased) == magnitude_squares(sample),
                "row and column phase invariance of magnitudes",
            )
    counts["independent_permutations_checked"] = 36
    return counts


def total_offdiagonal(a: Magnitudes) -> F:
    return sum((a[i][j] for i in range(3) for j in range(3) if i != j), F(0))


def cycle_gaps(a: Magnitudes) -> tuple[F, ...]:
    return tuple(
        2 * max(a[i][j] for i, j in cycle) - sum((a[i][j] for i, j in cycle), F(0))
        for cycle in CYCLES
    )


def pdg_comparator() -> dict[str, object]:
    center = tuple(tuple(value.central for value in row) for row in PDG)
    high = tuple(tuple(value.high for value in row) for row in PDG)
    central_gaps = cycle_gaps(center)
    box_gaps = tuple(
        max(
            PDG[i][j].low
            - sum((PDG[k][ell].high for k, ell in cycle if (k, ell) != (i, j)), F(0))
            for i, j in cycle
        )
        for cycle in CYCLES
    )
    need(central_gaps == (F(".174600"), F(".180028")), "central PDG cycle gaps")
    need(box_gaps == (F(".172940"), F(".178488")), "PDG interval-box cycle gaps")
    central_radius, box_radius = max(central_gaps) / 3, max(box_gaps) / 3
    central_stable = total_offdiagonal(center) + 6 * central_radius
    box_stable = total_offdiagonal(high) + 6 * box_radius
    need(
        central_stable == F(".905188") and box_stable == F(".905308"),
        "exact lock margins with magnitude error",
    )
    need(
        central_stable**2 < 2 and box_stable**2 < 2,
        "determinant lock remains valid throughout excluded radius",
    )
    original_gaps = sorted(central_gaps)
    for rows in permutations(range(3)):
        for columns in permutations(range(3)):
            permuted = tuple(tuple(center[i][j] for j in columns) for i in rows)
            alignments = [
                order
                for order in permutations(range(3))
                if all(permuted[i][order[i]] > F(9, 10) for i in range(3))
            ]
            need(len(alignments) == 1, "unique dominant-entry alignment")
            aligned = tuple(
                tuple(permuted[i][j] for j in alignments[0]) for i in range(3)
            )
            need(
                sorted(cycle_gaps(aligned)) == original_gaps,
                "all label permutations have the same cycle exclusion",
            )
    return {
        "source_url": SOURCE_URL,
        "source_sha256_pin_from_parent_audit": SOURCE_SHA256,
        "location": "PDG 2024 CKM review eq.12.27, p.12",
        "table_central_low_high": [
            [[str(value.central), str(value.low), str(value.high)] for value in row]
            for row in PDG
        ],
        "central_cycle_gaps": [str(value) for value in central_gaps],
        "entrywise_box_cycle_gaps": [str(value) for value in box_gaps],
        "central_sup_magnitude_distance_lower": str(central_radius),
        "central_distance_decimal_display": float(central_radius),
        "box_sup_magnitude_distance_lower": str(box_radius),
        "central_total_offdiagonal": str(total_offdiagonal(center)),
        "box_total_offdiagonal_upper": str(total_offdiagonal(high)),
        "stable_lock_offsum_at_central_radius": str(central_stable),
        "stable_lock_offsum_at_box_radius": str(box_stable),
        "statistical_scope": "historical global-fit comparator; rectangular marginal-range robustness, not a joint confidence region or p-value",
    }


def three_input_control() -> dict[str, str]:
    a_low, a_high, b_high, c_high = F(".20"), F(".25"), F(".06"), F(".01")
    offsum_upper = 2 * a_high + 2 * b_high + a_high * b_high + 4 * c_high
    gap = a_low * (1 - b_high) - b_high - c_high
    need(
        offsum_upper == F(".675") and offsum_upper**2 < 2,
        "three-input cofactors suffice to lock determinant",
    )
    need(gap == F(".118") and gap > 0, "three-input triangle contradiction")
    for value in (PDG[0][1].low, PDG[0][1].high):
        need(a_low <= value <= a_high, "Cabibbo interval contained in coarse box")
    need(
        PDG[1][2].high <= b_high and PDG[0][2].high <= c_high,
        "other input intervals contained in coarse box",
    )
    return {
        "a_interval": "[.20,.25]",
        "b_upper": ".06",
        "c_upper": ".01",
        "cofactor_offsum_upper": str(offsum_upper),
        "a_times_one_minus_b_minus_b_minus_c_lower": str(gap),
        "scope": "only three supplied magnitude intervals plus unitarity; no fitted td input",
    }


def countercontrols() -> dict[str, object]:
    single = run(eye(3), (("T", 0, 1),))
    need(raw_constraints(single) == I, "single raw mixer determinant i")
    need(
        not triangle_squared(tuple(single[i][j].norm2() for i, j in CYCLES[0])),
        "determinant lock is essential",
    )
    isolated = []
    for n in (2, 10, 100, 1000):
        t = F(1, n)
        zeta = g((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))
        projector = (
            (F(1, 2), F(-1, 2), F(0)),
            (F(-1, 2), F(1, 2), F(0)),
            (F(0), F(0), F(0)),
        )
        matrix = tuple(
            tuple(
                (ONE if i == j else ZERO) + (zeta - ONE) * g(projector[i][j])
                for j in range(3)
            )
            for i in range(3)
        )
        need(
            unitary(matrix) and determinant(matrix) == zeta and zeta not in PHASES,
            "continuous-phase escape lies outside mu4",
        )
        need(
            all(sum(row, ZERO) == ONE for row in matrix),
            "continuous escape still fixes uniform vector",
        )
        need(
            matrix[0][1].norm2() == t * t / (1 + t * t)
            and matrix[1][2] == matrix[2][0] == ZERO,
            "arbitrarily small isolated mixing outside determinant stock",
        )
        need(
            not triangle_squared(tuple(matrix[i][j].norm2() for i, j in CYCLES[0])),
            "continuous escape violates triangle",
        )
        isolated.append(str(matrix[0][1].norm2()))
    return {
        "raw_single_mixer_triangle": "fails with determinant i",
        "continuous_phase_isolated_squared_magnitudes": isolated,
        "continuous_escape_scope": "not a native raw word; determinant restriction deliberately removed",
    }


def audit() -> dict[str, object]:
    return {
        "ok": True,
        "native_words": native_controls(),
        "pdg_fixed_comparator": pdg_comparator(),
        "three_input_witness": three_input_control(),
        "countercontrols": countercontrols(),
        "boundary": "one raw aligned three-family carrier only; not paired logical rails, nonaligned embeddings, CP exclusion, or general IDT falsification",
    }


class RawFamilyTests(unittest.TestCase):
    def test_native_words(self) -> None:
        result = native_controls()
        self.assertEqual(result["all_words"], 1093)
        self.assertEqual(result["determinant_one_words"], 82)

    def test_triangle_cross_term(self) -> None:
        self.assertTrue(triangle_squared((F(4), F(1), F(1))))
        self.assertFalse(triangle_squared((F(5), F(1), F(1))))

    def test_fixed_comparator(self) -> None:
        result = pdg_comparator()
        self.assertEqual(result["central_sup_magnitude_distance_lower"], "45007/750000")
        self.assertEqual(result["box_sup_magnitude_distance_lower"], "7437/125000")

    def test_three_inputs(self) -> None:
        self.assertEqual(
            three_input_control()["a_times_one_minus_b_minus_b_minus_c_lower"], "59/500"
        )

    def test_countercontrols(self) -> None:
        values = countercontrols()["continuous_phase_isolated_squared_magnitudes"]
        if not isinstance(values, list):
            raise TypeError("expected countercontrol list")
        self.assertEqual(len(values), 4)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = audit()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(
            "PASS: 1093 finite raw words, both oriented triangles in determinant-one sector."
        )
        print(
            "PDG central sup-magnitude distance lower bound: 45007/750000 (~0.06000933)."
        )
        print("Quoted entrywise-box lower bound: 7437/125000 (0.059496); no p-value.")
        print(
            "Three supplied inputs [.20,.25], b<=.06, c<=.01 violate the necessary inequality by >=.118."
        )
        print(result["boundary"])


if __name__ == "__main__":
    main()
