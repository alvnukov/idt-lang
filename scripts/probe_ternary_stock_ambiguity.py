"""The exact ternary stock ambiguity: quadratic plus an order-two residue.

DOMAIN/PREMISES. R=Z[1/3]; f:R->R is nonnegative and even, with f(0)=0.
Supply separability S(x)=sum_i f(x_i) and invariance on ALL independently
preparable triples R^3, not merely on one accessible fixed-norm orbit. The
selected echo links are signed row/column permutations of H=-I+(2/3)J.
Evenness and coordinatewise identical f make those frame changes harmless.
Signed linear transport, independent preparation, additive stock valuation,
and a common f across resolutions are premises, not actual-event laws.

CLASSIFICATION ARGUMENT. Apply mixed differences in directions (2h,h,0),
(h,2h,0),(h,0,2h) to S(Hx)=S(x). Each output row is killed by one direction;
the other two input components are also killed. Hence Delta_(2h) Delta_h^2
f=0. On each grid h Z, its characteristic polynomial is
 (t^2-1)(t-1)^2=(t-1)^3(t+1)=t^4-2t^3+2t-1.
The full two-sided recurrence has quadratic-polynomial and alternating
solutions. Evenness removes the linear term, and f(0)=0 ties its two constant
terms: f(n/3^k)=A_k n^2+B_k 1_(n odd). Comparing n=2 and n=1 across refinement
gives A_(k+1)=A_k/9 and B_(k+1)=B_k. Thus exactly
 f(x)=A x^2+B epsilon(x),  epsilon(x)=x mod 2 in {0,1}.
Here A=f(2)/4>=0. Nonnegativity on x=3^-k forces B>=0 by the Archimedean
order of the real codomain, WITHOUT assuming continuity of f. Conversely,
H is orthogonal and 3H mod2=I, so every A,B>=0 works. All selected links
reduce modulo2 to permutations, preserving the number of odd coordinates.

DENSITY IS NOT CONTINUITY. The frozen links have dense SO(3) loop closure,
but epsilon is discontinuous on the dense ternary domain. A dense group alone
cannot promote f to a continuous radial valuation. Full-domain preparation
is also stronger than density of one orbit: the mixed-difference argument
uses translated configurations with different amplitudes.

ONE EXACT CONTRAST. For a common unknown tripling gain on the two input
amplitudes 1,2, the gain-free determinant is
 Delta=f(6)f(1)-f(3)f(2)=32 A B.
If f(2)>0, Delta=0 forces B=0 and the gain is9. Without that nonzero response,
pure parity A=0 survives with gain1. The test must probe a generator of the
full ternary module, not only its even submodule. Simultaneous measurement
intervals can exclude zero contrast, but containing zero is only inconclusive;
it cannot establish an exact equality. Under the classified family,
0<=Delta<=d and f(2)>=l>0 imply B<=d/(8l).

OTHER CLOSURES. Merely requiring f(3^-k)->0 kills B; full continuity is stronger
than needed. On D_m=2^-m Z[1/3], however, the classification is
f(x)=A x^2+B epsilon(2^m x). One finite binary refinement forces the OLD-domain
restriction to be quadratic but leaves a possible defect on the new finest
level. A single compatible law on the union Z[1/6] is quadratic everywhere.
No fixed finite refinement proves that global statement. The same contrast
on integer inputs misses the m=1 defect; a contrast at the new generator sees it.

COUNTERCONTROLS/COSTS. The nonseparable invariant ||x||^4 passes the axis
tripling contrast with gain81, but fails component additivity. Separability
therefore cannot be silently dropped. Finite resolution also cannot force
B>=0: A=1,B=-1/100 is nonnegative through denominator9 but fails at1/27.
If 'stock' literally means INTEGER-valued on every ternary input, classification
forces A=0: successive values at3^-k have positive differences tending below1.
A nonzero quadratic valuation already needs fractional resolution or another
stock interpretation. None of these results supplies event selection, the
Born rule, experimental calibration, or a physical detector.

Source controls: the selected six-label root in probe_matching_echo_selector.py
and all120 polar links in probe_matching_transport.py. This is an elementary
classification argument with bounded exact regressions, not a Lean proof.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction as F
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts import probe_balanced_phase_composition as b
from scripts.probe_matching_echo_selector import classify, matching, perm
from scripts.probe_matching_transport import MATCHES, Match, links, loop_generators

Vector = tuple[F, ...]
H = b.add(b.scale(-1, b.identity(3)), b.scale(F(2, 3), b.matrix(((1, 1, 1),) * 3)))


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def apply(a: b.Matrix, x: Vector) -> Vector:
    return tuple(sum((u * v for u, v in zip(row, x, strict=True)), F(0)) for row in a)


def ternary_parity(x: F) -> int:
    denominator = x.denominator
    while denominator % 3 == 0:
        denominator //= 3
    if denominator != 1:
        raise ValueError("input is outside Z[1/3]")
    return x.numerator % 2


def valuation(x: F, a: F, torsion: F, binary_depth: int = 0) -> F:
    if binary_depth < 0:
        raise ValueError("nonnegative binary refinement depth required")
    return a * x * x + torsion * ternary_parity(2**binary_depth * x)


def stock(x: Vector, a: F, torsion: F, binary_depth: int = 0) -> F:
    return sum((valuation(v, a, torsion, binary_depth) for v in x), F(0))


def norm2(x: Vector) -> F:
    return sum((value * value for value in x), F(0))


def pair_basis(m: Match) -> b.Matrix:
    return b.matrix(
        tuple(tuple(int(i == a) - int(i == c) for a, c in m) for i in range(6))
    )


def canonical_signed_form(link: b.Matrix) -> None:
    """Find row/column signs and the column permutation; do not fit f."""
    weak = tuple(
        next(j for j in range(3) if abs(link[i][j]) == F(1, 3)) for i in range(3)
    )
    need(sorted(weak) == [0, 1, 2], "weak-entry permutation")
    aligned = tuple(tuple(row[j] for j in weak) for row in link)
    col_signs = tuple(aligned[0][j] / H[0][j] for j in range(3))
    row_signs = tuple(aligned[i][0] / (H[i][0] * col_signs[0]) for i in range(3))
    need(all(x in (-1, 1) for x in (*row_signs, *col_signs)), "signed frame factors")
    need(
        all(
            aligned[i][j] == row_signs[i] * H[i][j] * col_signs[j]
            for i, j in product(range(3), repeat=2)
        ),
        "selected link is not in the H signed-permutation class",
    )


def link_controls() -> dict[str, object]:
    m, n, rotation, selected = classify()
    base = b.scale(
        F(1, 2),
        b.multiply(
            b.transpose(pair_basis(MATCHES[4])),
            b.multiply(selected, pair_basis(MATCHES[0])),
        ),
    )
    _, minus = links()
    need(base == minus[0, 4], "selected root and frozen polar minus link differ")
    need(
        b.multiply(selected, m) == b.multiply(n, selected), "selected root intertwining"
    )
    need(b.multiply(selected, selected) == rotation, "selected same-device echo")
    tested = 0
    for (i, j), link in minus.items():
        mi, nj = perm(matching(MATCHES[i])), perm(matching(MATCHES[j]))
        r = b.multiply(nj, mi)
        u = b.scale(
            F(1, 3),
            b.add(b.scale(2, b.add(b.identity(6), r)), b.scale(-1, b.multiply(r, r))),
        )
        actual = b.scale(
            F(1, 2),
            b.multiply(
                b.transpose(pair_basis(MATCHES[j])),
                b.multiply(u, pair_basis(MATCHES[i])),
            ),
        )
        need(actual == link, "all-link selected-root comparison")
        canonical_signed_form(link)
        need(
            b.multiply(b.transpose(link), link) == b.identity(3), "quadratic invariance"
        )
        residue = tuple(tuple(ternary_parity(x) for x in row) for row in link)
        need(
            all(sum(row) == 1 for row in residue)
            and all(sum(col) == 1 for col in zip(*residue, strict=True)),
            "mod-two link is not a permutation",
        )
        for integers in product((-1, 0, 1), repeat=3):
            x = tuple(F(value, 9) for value in integers)
            need(
                stock(apply(link, x), F(1), F(2)) == stock(x, F(1), F(2)),
                "ternary quadratic-plus-parity stock",
            )
            tested += 1
    need(len(minus) == 120, "frozen link count")
    loops = dict(loop_generators(minus))
    a, c = loops[(0, 5, 6, 4, 0)], loops[(0, 7, 11, 4, 0)]
    need(
        b.trace(a) == b.trace(c) == F(115, 81) and b.multiply(a, c) != b.multiply(c, a),
        "frozen dense-loop witnesses",
    )
    # These two infinite-order rotations have different axes; the standard
    # SO3 closure argument does not impose continuity on a stock valuation.
    axes = tuple(
        (v[2][1] - v[1][2], v[0][2] - v[2][0], v[1][0] - v[0][1]) for v in (a, c)
    )
    need(
        any(
            axes[0][i] * axes[1][j] != axes[0][j] * axes[1][i]
            for i, j in product(range(3), repeat=2)
        ),
        "loop axes parallel",
    )
    return {
        "selected_links": len(minus),
        "exact_stock_checks": tested,
        "loop_trace": "115/81",
        "parity_survives_dense_closure_generators": True,
    }


def rank(rows: list[list[F]]) -> int:
    matrix = [row[:] for row in rows]
    pivot = 0
    for column in range(len(matrix[0])):
        selected = next(
            (i for i in range(pivot, len(matrix)) if matrix[i][column]), None
        )
        if selected is None:
            continue
        matrix[pivot], matrix[selected] = matrix[selected], matrix[pivot]
        scale = matrix[pivot][column]
        matrix[pivot] = [x / scale for x in matrix[pivot]]
        for i in range(pivot + 1, len(matrix)):
            scale = matrix[i][column]
            if scale:
                matrix[i] = [
                    x - scale * y for x, y in zip(matrix[i], matrix[pivot], strict=True)
                ]
        pivot += 1
    return pivot


def recurrence_controls() -> dict[str, object]:
    directions = ((2, 1, 0), (1, 2, 0), (1, 0, 2))
    for row, direction in zip(H, directions, strict=True):
        need(
            sum(x * y for x, y in zip(row, direction, strict=True)) == 0,
            "annihilating output direction",
        )
    need(
        directions[2][1] == 0 and directions[0][2] == 0,
        "other input components not killed",
    )
    # Difference coefficient convolution for increments2,1,1.
    coefficients = [1]
    for step in (2, 1, 1):
        updated = [0] * (len(coefficients) + step)
        for i, value in enumerate(coefficients):
            updated[i] -= value
            updated[i + step] += value
        coefficients = updated
    need(coefficients == [-1, 2, 0, -2, 1], "recurrence polynomial")
    dimensions = {}
    for radius in (2, 3, 6, 12):
        labels = tuple(range(-radius, radius + 1))
        rows = []
        for start in range(-radius, radius - 3):
            rows.append(
                [
                    F(coefficients[n - start]) if 0 <= n - start <= 4 else F(0)
                    for n in labels
                ]
            )
        for n in range(1, radius + 1):
            rows.append([F(int(j == n) - int(j == -n)) for j in labels])
        rows.append([F(int(j == 0)) for j in labels])
        for values in (
            tuple(F(n * n) for n in labels),
            tuple(F(n % 2) for n in labels),
        ):
            need(
                all(
                    sum((x * y for x, y in zip(row, values, strict=True)), F(0)) == 0
                    for row in rows
                ),
                "classified basis does not satisfy finite recurrence",
            )
        dimensions[str(radius)] = len(labels) - rank(rows)
        need(dimensions[str(radius)] == 2, "additional even recurrence freedom")
    for k in range(5):
        ak, bk = F(2, 9**k), F(3)
        next_a, next_b = ak / 9, bk
        for n in range(-6, 7):
            need(
                ak * n * n + bk * (n % 2)
                == next_a * (3 * n) ** 2 + next_b * ((3 * n) % 2),
                "ternary refinement compatibility",
            )
    return {
        "difference_coefficients": coefficients,
        "even_zero_at_origin_window_dimensions": dimensions,
        "classification": "A*x^2+B*epsilon(x), A,B>=0",
        "classification_scope": "all independent R^3 inputs; not one orbit",
    }


def contrast(a: F, torsion: F, unit: F = F(1), binary_depth: int = 0) -> F:
    f1, f2, f3, f6 = (
        valuation(n * unit, a, torsion, binary_depth) for n in (1, 2, 3, 6)
    )
    return f6 * f1 - f3 * f2


def interval_contrast(bounds: tuple[tuple[F, F], ...]) -> tuple[F, F]:
    if len(bounds) != 4 or any(lo < 0 or lo > hi for lo, hi in bounds):
        raise ValueError(
            "four simultaneous nonnegative intervals for f1,f2,f3,f6 required"
        )
    a, c, d, e = bounds
    return e[0] * a[0] - d[1] * c[1], e[1] * a[1] - d[0] * c[0]


def contrast_controls() -> dict[str, object]:
    for a, torsion in product((F(0), F(1, 3), F(1), F(2)), repeat=2):
        need(contrast(a, torsion) == 32 * a * torsion, "gain-free contrast identity")
    need(
        contrast(F(0), F(1)) == 0 and valuation(F(2), F(0), F(1)) == 0,
        "missing nonzero-scale countercontrol",
    )
    need(contrast(F(1), F(1)) == 32, "positive torsion witness")
    need(contrast(F(1), F(1), F(2)) == 0, "testing only even inputs misses torsion")
    noisy = interval_contrast(
        tuple((F(n) - F(1, 10), F(n) + F(1, 10)) for n in (2, 4, 10, 36))
    )
    compatible = interval_contrast(
        tuple((F(n) - F(1, 10), F(n) + F(1, 10)) for n in (1, 4, 9, 36))
    )
    need(noisy == (F(134, 5), F(186, 5)), "sharp simultaneous interval contrast")
    need(
        compatible == (F(-5), F(5)),
        "noisy quadratic control should remain inconclusive",
    )
    # Under the classified family, an upper contrast d and positive f2 lower
    # bound l yield the conditional exact upper bound B<=d/(8l).
    need(F(32) / (8 * F(4)) == 1, "conditional defect bound")
    return {
        "contrast": "f6*f1-f3*f2=32*A*B",
        "required_nonzero_response": "f2>0",
        "positive_defect_interval": [str(x) for x in noisy],
        "quadratic_interval_inconclusive": [str(x) for x in compatible],
        "conditional_defect_upper_bound": "Delta_upper/(8*f2_lower)",
    }


def closure_and_countercontrols() -> dict[str, object]:
    for m, k in product(range(4), range(3)):
        for ns in product((-1, 0, 1), repeat=3):
            x = tuple(F(n, 2**m * 3**k) for n in ns)
            need(
                stock(apply(H, x), F(1), F(1), m) == stock(x, F(1), F(1), m),
                "finite binary-depth defect invariance",
            )
        generator = F(1, 2**m)
        need(
            valuation(generator, F(1), F(1), m)
            - valuation(generator, F(1), F(1), m + 1)
            == 1,
            "incompatible residual defect across binary refinement",
        )
    need(
        contrast(F(1), F(1), binary_depth=1) == 0,
        "old integer contrast misses finer defect",
    )
    need(contrast(F(1), F(1), F(1, 2), 1) == 8, "finest generator exposes defect")
    for k in range(6):
        value = valuation(F(1, 3**k), F(2), F(3))
        need(value - 3 == F(2, 9**k), "zero-limit defect")
    for k in range(3):
        need(
            all(valuation(F(n, 3**k), F(1), F(-1, 100)) >= 0 for n in range(-12, 13)),
            "finite-resolution positivity countercontrol",
        )
    need(F(1, 81) > F(1, 100), "smallest nonzero odd square through denominator9")
    need(
        valuation(F(1, 27), F(1), F(-1, 100)) < 0,
        "global positivity needs unbounded scope",
    )
    x = (F(1), F(0), F(0))
    y = apply(H, x)
    need(norm2(y) ** 2 == norm2(x) ** 2 == 1, "nonseparable quartic total is invariant")
    need(sum(value**4 for value in y) != 1, "separable quartic is rejected")
    other = (F(0), F(1), F(0))
    combined = tuple(a + c for a, c in zip(x, other, strict=True))
    need(
        norm2(combined) ** 2 != norm2(x) ** 2 + norm2(other) ** 2,
        "nonseparable additivity violation",
    )
    need(
        F(6) ** 4 * F(1) ** 4 - F(3) ** 4 * F(2) ** 4 == 0,
        "axis contrast alone does not select a nonseparable stock",
    )
    # A=1, B=1 already violates integral-valued stock at the first refinement;
    # the general argument uses differences 8A/9^(k+1) tending below one.
    need(
        valuation(F(1, 3), F(1), F(1)).denominator == 9,
        "quadratic stock is not integer-valued at all ternary inputs",
    )
    return {
        "binary_domain": "D_m=2^-m Z[1/3] has defect epsilon(2^m*x)",
        "compatible_unbounded_binary_refinement": "quadratic on Z[1/6]",
        "continuity_needed": "only f(3^-k)->0 suffices",
        "nonseparable_countercontrol": "||x||^4 invariant and axis-contrast zero, but not additive",
        "integer_valued_all_resolution_wall": "A=0",
    }


def main() -> None:
    need(b.multiply(H, H) == b.identity(3), "ternary involution")
    need(
        tuple(tuple(int(3 * x) % 2 for x in row) for row in H)
        == ((1, 0, 0), (0, 1, 0), (0, 0, 1)),
        "3H mod2",
    )
    result = {
        "status": "exact ternary ambiguity and conditional closures; no event-law derivation",
        "link_controls": link_controls(),
        "recurrence": recurrence_controls(),
        "gain_free_contrast": contrast_controls(),
        "closure_boundaries": closure_and_countercontrols(),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
