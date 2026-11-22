"""Conditional five-slot minimality, with exact negative controls.

INPUT FAMILY: the full even exterior carrier E_n = Lambda^even C^n with
the continuous determinant-one block group H=S(U(p) x U(q)), p+q=n.
Two nonabelian blocks means p,q>=2. Chirality here means E_n is not
isomorphic to its complex conjugate, NOT a derived spacetime/Weyl claim.
Interpreting trace cancellations as fermion anomalies supplies left Weyl
fields. The tests cover local linear/cubic traces and the ordinary SU(2)
doublet parity test, not every possible global/bordism anomaly.

ANALYTIC ARGUMENT: complement identifies the dual of E_n with E_n for
even n, and with the odd exterior carrier for odd n. For traceless slot
weights x_i, the exponential trace is
  2^(n-1) [prod cosh(t*x_i/2) + (-1)^n prod sinh(t*x_i/2)].
Thus for odd n the first possible odd trace has degree n and equals
  -n!/2 * prod(x_i).
Primitive block weights (-q/gcd(p,q), p/gcd(p,q)) are all nonzero, so this
is an explicit non-self-conjugacy witness AFTER restriction to H. There
is no hidden folding of the odd carrier into its conjugate on this group.
For n>3, all linear and cubic traces vanish on the full traceless Cartan;
unitary diagonalization and polarization give the full local cubic tensor.
n=3 instead has a nonzero cubic tensor. n=4 is self-conjugate. Therefore
n=5 is the minimum in this SUPPLIED family with two nonabelian blocks and
non-self-conjugate, locally anomaly-canceling representation. Its only
unordered split is 2+3. Larger odd n also work; minimality is a principle,
not an output of the signed-transfer law or a physical measurement.

GLOBAL KERNEL: the product-to-block map is
  (A,B,z) -> diag(z^(-q/d) A, z^(p/d) B), d=gcd(p,q).
Its kernel is cyclic of order L=lcm(p,q). For n>=3, identity on Lambda^2
forces all unitary eigenvalues to be the same +/-1. Odd n excludes -I by
determinant one, so the even action adds no kernel. Even n adds -I: its
total cover kernel is Z_(2L) if p,q are odd, and Z_L x Z_2 if both are
even. For n=2 the even action is entirely trivial, a continuous exception.
These are kernels of supplied actions, not the global gauge group of nature.

COUNTERCONTROLS: remove the invariant vacuum to get dimension 15 instead
of 16 without changing positive-degree traces or chirality at n=5. More
strongly, H=S(U(2)xU(2)) admits the faithful 13-dimensional alternative
carrier (2,2)_0 + (2,1)_1 + (2,1)_(-1) plus five singlets of charges
2*(-9,-5,-1,7,8). It is chiral and cancels the tested anomalies. Its net
chirality lives in the singlet sector; the nonabelian matter is self-dual.
It is NOT a full even exterior carrier. This rules out universal five-slot
minimality across arbitrary carriers, and exposes a spectator-chirality
loophole if a stronger physical criterion is intended.

This file supplies finite exact audits of the analytic arguments, not Lean
proofs, native origins of slots/even parity/groups, gauge redundancy,
dynamics, particle identifications, calibrated fields or invisible sectors.
"""

from __future__ import annotations

import argparse
import json
import unittest
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import combinations_with_replacement, product
from math import comb, factorial, gcd, lcm, prod

CenterPoint = tuple[int, int, int]


def require(condition: bool, message: object) -> None:
    if not condition:
        raise AssertionError(message)


@dataclass(frozen=True)
class ExteriorModel:
    p: int
    q: int

    def __post_init__(self) -> None:
        if min(self.p, self.q) < 1:
            raise ValueError("two positive block sizes required")

    @property
    def n(self) -> int:
        return self.p + self.q

    @property
    def weights(self) -> tuple[int, ...]:
        d = gcd(self.p, self.q)
        return (-self.q // d,) * self.p + (self.p // d,) * self.q

    def charges(self, parity: int = 0) -> Counter[int]:
        if parity not in (0, 1):
            raise ValueError("parity must be zero or one")
        result: Counter[int] = Counter()
        left, right = self.weights[0], self.weights[-1]
        for a, b in product(range(self.p + 1), range(self.q + 1)):
            if (a + b) % 2 == parity:
                result[a * left + b * right] += comb(self.p, a) * comb(self.q, b)
        return result

    def trace(self, degree: int) -> int:
        if degree < 0:
            raise ValueError("nonnegative trace degree required")
        return sum(
            multiplicity * charge**degree
            for charge, multiplicity in self.charges().items()
        )

    def su2_doublet_counts(self) -> tuple[int, ...]:
        return tuple(
            2 ** (other - 1)
            for width, other in ((self.p, self.q), (self.q, self.p))
            if width == 2
        )


@cache
def cubic_cartan_tensor(n: int) -> tuple[tuple[tuple[int, int, int], int], ...]:
    """Every cubic coefficient on diag(e_i-e_last), not one fitted direction."""
    if n < 2:
        raise ValueError("at least two slots required")
    weights = tuple(
        tuple(((mask >> i) & 1) - ((mask >> (n - 1)) & 1) for i in range(n - 1))
        for mask in range(1 << n)
        if mask.bit_count() % 2 == 0
    )
    nonzero: list[tuple[tuple[int, int, int], int]] = []
    for indices in combinations_with_replacement(range(n - 1), 3):
        a, b, c = indices
        coefficient = sum(row[a] * row[b] * row[c] for row in weights)
        if coefficient:
            nonzero.append((indices, coefficient))
    return tuple(nonzero)


def center_kernels(
    p: int, q: int
) -> tuple[frozenset[CenterPoint], frozenset[CenterPoint]]:
    """Exact center residues; z has denominator 2*lcm(p,q).

    Completeness uses the Lambda^2 argument in the module docstring.
    At n=2 the action kernel is continuous, so finite enumeration is invalid.
    """
    if min(p, q) < 1 or p + q < 3:
        raise ValueError("finite action-kernel enumeration requires n>=3")
    d, denominator = gcd(p, q), 2 * lcm(p, q)
    embedding: set[CenterPoint] = set()
    action: set[CenterPoint] = set()
    for a, b, t in product(range(p), range(q), range(denominator)):
        left = Fraction(a, p) - Fraction((q // d) * t, denominator)
        right = Fraction(b, q) + Fraction((p // d) * t, denominator)
        if left.denominator == right.denominator == 1:
            embedding.add((a, b, t))
        pair_phases = [left + right]
        if p >= 2:
            pair_phases.append(2 * left)
        if q >= 2:
            pair_phases.append(2 * right)
        if all(phase.denominator == 1 for phase in pair_phases):
            action.add((a, b, t))
    return frozenset(embedding), frozenset(action)


def center_order(point: CenterPoint, p: int, q: int) -> int:
    denominator = 2 * lcm(p, q)
    return lcm(
        p // gcd(point[0], p),
        q // gcd(point[1], q),
        denominator // gcd(point[2], denominator),
    )


def kernel_audit(p: int, q: int) -> dict[str, object]:
    order = lcm(p, q)
    if p + q == 2:
        return {
            "product_to_block": "Z1",
            "even_action": "entire U(1), continuous",
            "extra_minus_identity": "the finite-kernel argument does not apply",
        }
    embedding, action = center_kernels(p, q)
    require(len(embedding) == order, "product-to-block kernel order")
    require(
        max(center_order(point, p, q) for point in embedding) == order,
        "cyclic embedding kernel",
    )
    if (p + q) % 2:
        require(action == embedding, "odd n adds no action kernel")
        action_name = f"Z{order}"
    else:
        require(len(action) == 2 * order, "even n adds minus identity")
        expected_max = 2 * order if p % 2 else order
        require(
            max(center_order(point, p, q) for point in action) == expected_max,
            "even action kernel exponent",
        )
        action_name = f"Z{2 * order}" if p % 2 else f"Z{order} x Z2"
    return {
        "product_to_block": f"Z{order}",
        "even_action": action_name,
        "extra_minus_identity": (p + q) % 2 == 0,
    }


def alternative_thirteen_control() -> dict[str, object]:
    """A supplied non-exterior carrier on S(U2 x U2), not a particle model."""
    singlets = tuple(2 * charge for charge in (-9, -5, -1, 7, 8))
    charges = Counter(singlets)
    require(
        sum(singlets) == sum(charge**3 for charge in singlets) == 0, "singlet anomalies"
    )
    require(charges != Counter(-charge for charge in singlets), "singlet chirality")
    require(
        sum(charge**5 for charge in singlets) == -403200, "explicit chirality invariant"
    )
    # (2,1)_{+1} and (2,1)_{-1}: each charge occurs twice.
    require(sum(singlets) + 2 * (1 - 1) == 0, "full mixed gravitational trace")
    require(
        sum(charge**3 for charge in singlets) + 2 * (1**3 + (-1) ** 3) == 0,
        "full U1 cubic",
    )
    require(1 + (-1) == 0, "SU2_1 squared U1 trace")
    doublets = (2 + 1 + 1, 2)
    require(all(count % 2 == 0 for count in doublets), "both SU2 parity tests")
    # Identity on (2,2)_0 first forces A=B=+/-I. The charged doublets then
    # force z to be that same sign; these are exactly the embedding kernel.
    kernel = {
        (a, b, t)
        for a, b, t in product(range(2), repeat=3)
        if (a + b) % 2 == (a + t) % 2 == (a - t) % 2 == 0
        and all(charge * t % 2 == 0 for charge in singlets)
    }
    require(kernel == {(0, 0, 0), (1, 1, 1)}, "faithful on determinant-one block group")
    return {
        "dimension": 13,
        "block_sizes": [2, 2],
        "singlet_charges": list(singlets),
        "singlet_fifth_trace": -403200,
        "su2_doublet_counts": list(doublets),
        "faithful_on_block_group": True,
        "boundary": "not full even exterior; net chirality is in singlets; only local traces and ordinary SU2 parity checked",
    }


def audit() -> dict[str, object]:
    rows: list[dict[str, object]] = []
    for n in range(2, 13):
        tensor = cubic_cartan_tensor(n)
        require(bool(tensor) == (n == 3), (n, "local cubic tensor"))
        splits: list[dict[str, object]] = []
        for p in range(1, n // 2 + 1):
            model = ExteriorModel(p, n - p)
            even, odd = model.charges(), model.charges(1)
            conjugate = Counter({-charge: count for charge, count in even.items()})
            require(sum(even.values()) == 2 ** (n - 1), "full even dimension")
            require(sum(model.weights) == model.trace(1) == 0, "traceless linear trace")
            require(conjugate == (even if n % 2 == 0 else odd), "complement conjugacy")
            require(
                (even == conjugate) == (n % 2 == 0), "charge witness self-conjugacy"
            )
            require(
                Counter(even + odd)
                == Counter(conjugate + Counter({-x: c for x, c in odd.items()})),
                "full exterior is self-conjugate",
            )
            if n % 2:
                expected = -factorial(n) * prod(model.weights) // 2
                require(model.trace(n) == expected != 0, "odd-degree chirality witness")
            if n >= 4:
                require(model.trace(3) == 0, "cubic block trace")
                require(
                    all(count % 2 == 0 for count in model.su2_doublet_counts()),
                    "SU2 parity",
                )
            if n >= 3:
                require(
                    model.trace(2) == 2 ** (n - 3) * sum(x * x for x in model.weights),
                    "second trace",
                )
            splits.append(
                {
                    "blocks": [p, n - p],
                    "two_nonabelian": p >= 2,
                    "first_odd_trace": model.trace(n) if n % 2 else None,
                    "su2_doublet_counts": list(model.su2_doublet_counts()),
                    "kernels": kernel_audit(p, n - p),
                }
            )
        rows.append(
            {
                "n": n,
                "dimension": 2 ** (n - 1),
                "self_conjugate": n % 2 == 0,
                "cubic_tensor_nonzero_entries": len(tensor),
                "splits": splits,
            }
        )
    eligible = [
        n for n in range(2, 13) if n >= 4 and n % 2 and not cubic_cartan_tensor(n)
    ]
    require(eligible == [5, 7, 9, 11], "conditional minimal and competing sizes")
    five = ExteriorModel(3, 2)
    reduced = five.charges().copy()
    reduced[0] -= 1
    require(sum(reduced.values()) == 15, "remove invariant vacuum")
    for degree in range(1, 7):
        require(
            sum(count * charge**degree for charge, count in reduced.items())
            == five.trace(degree),
            "vacuum deletion preserves positive-degree traces",
        )
    require(five.trace(5) != 0, "vacuum deletion preserves chirality witness")
    require(kernel_audit(3, 2)["even_action"] == "Z6", "five-slot faithful kernel")
    return {
        "ok": True,
        "rows": rows,
        "eligible_full_even_sizes": eligible,
        "conditional_minimum_slots": 5,
        "conditional_full_even_dimension": 16,
        "vacuum_removed_dimension": 15,
        "alternative_carrier": alternative_thirteen_control(),
        "boundary": "conditional family minimality plus exact finite checks; not a Lean proof, universal carrier minimum, or derivation of a physical gauge group",
    }


class MinimalityTests(unittest.TestCase):
    def test_all_sizes_and_splits(self) -> None:
        self.assertTrue(audit()["ok"])

    def test_three_slot_negative_control(self) -> None:
        model = ExteriorModel(1, 2)
        self.assertEqual(model.trace(3), 6)
        self.assertEqual(model.su2_doublet_counts(), (1,))
        self.assertEqual(cubic_cartan_tensor(3), (((0, 0, 1), 1), ((0, 1, 1), 1)))

    def test_charge_histogram_matches_literal_subsets(self) -> None:
        for n in range(2, 8):
            for p in range(1, n // 2 + 1):
                model = ExteriorModel(p, n - p)
                for parity in (0, 1):
                    literal = Counter(
                        sum(
                            weight
                            for i, weight in enumerate(model.weights)
                            if (mask >> i) & 1
                        )
                        for mask in range(1 << n)
                        if mask.bit_count() % 2 == parity
                    )
                    self.assertEqual(model.charges(parity), literal)

    def test_kernel_distinctions_and_two_slot_exception(self) -> None:
        self.assertEqual(kernel_audit(3, 2)["even_action"], "Z6")
        self.assertEqual(kernel_audit(2, 2)["product_to_block"], "Z2")
        self.assertEqual(kernel_audit(2, 2)["even_action"], "Z2 x Z2")
        self.assertEqual(kernel_audit(3, 3)["even_action"], "Z6")
        self.assertEqual(kernel_audit(3, 3)["product_to_block"], "Z3")
        self.assertEqual(ExteriorModel(1, 1).charges(), Counter({0: 2}))
        with self.assertRaises(ValueError):
            center_kernels(1, 1)

    def test_five_trace_and_vacuum(self) -> None:
        five = ExteriorModel(3, 2)
        self.assertEqual(
            (five.trace(0), five.trace(1), five.trace(3), five.trace(5)),
            (16, 0, 0, 4320),
        )
        self.assertEqual(five.charges()[0], 1)

    def test_smaller_non_exterior_faithful_carrier(self) -> None:
        counter = alternative_thirteen_control()
        self.assertEqual(counter["dimension"], 13)
        self.assertTrue(counter["faithful_on_block_group"])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json", action="store_true", help="include all sizes and kernel cases"
    )
    args = parser.parse_args()
    result = audit()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(
            "PASS: n=2..12, every unordered two-block split, exact traces and center kernels."
        )
        print(
            "Full even exterior: even n is self-conjugate; odd n has a nonzero n-th trace."
        )
        print("n=3 has a cubic anomaly; n>=4 has zero full cubic Cartan tensor.")
        print(
            "With two nonabelian blocks, the minimal chiral member is n=5, split 3+2."
        )
        print(
            "Larger chiral controls: n=7,9,11. Full even dimension 16 becomes 15 after vacuum removal."
        )
        print(
            "Five-slot cover kernel is Z6; even n adds -I; n=2 has a continuous action kernel."
        )
        print(
            "Outside this carrier family: a faithful 13-dimensional countercontrol exists already at 2+2."
        )
        print(result["boundary"])


if __name__ == "__main__":
    main()
