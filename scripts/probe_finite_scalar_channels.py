"""Can a scalar channel on ONE finite even carrier fix the Higgs charge?

Supply V=C^3_color + C^2_weak, the usual exterior action on S=Lambda^even V
and the six left-Weyl labels of probe_packet_charge_pairings. Start without
a U(1) normalization. Enumerate ALL color-singlet weak-doublet operator
types in End(S), not just nearest transitions. The only ones are L<->N^c
and L<->e^c. For mode charges c,w and ANY common vacuum offset s their
charges are ±(3c+w), ±(3c-w). Every component has a four-slot quartic CAR
representative and cannot have smaller CAR degree or touched-slot count.
All change total occupation. Number-preserving exterior lifts and their
linear combinations/products cannot implement any of them. A label in
End(S) does not establish a preparation or an elementary scalar field.

Independently insert the previously tested one-family anomaly+Yukawa
charge plane with quark-doublet character q and unknown scalar character h.
Equivalently s=3q-h, c=-2q, w=h on these labels; that equivalence is not
independent evidence for additivity or interactions. The End charges are
±6q±h. Requiring an H of charge h to occur in THIS End forces q=0 or
h=±3q. No fundamental weights (-2,3) were inserted. On the neutron
probe's q=1 mod 6, h=3 mod 6 oriented lattice with a charged electron,
only h=3q is possible, so that model predicts an exactly neutral neutron.
If the local action has exactly the standard diagonal Z6 kernel in the
specified integer units, h=3q reduces its order 6|q| to 6 only at q=1
with h>0. Mere Z6 compatibility does not fix the common integer scale.

Crucial alternative: for two left-Weyl fields the Lorentz scalar uses the
antisymmetric spin contraction; Fermi exchange makes the internal pair
symmetric. Its internal carrier is Sym^2(S), not End(S). Cross-block
Q u^c, Q d^c, L N^c, L e^c already supply doublets of charges ±h for ALL
q,h. In contrast an ordinary one-conjugate/one-left Weyl field bilinear
is a Lorentz vector, not automatically a scalar. The finite packet has
no Lorentz action establishing the Higgs's realization. The scalar might
also be an independent field. A relative determinant twist between copies
restores h on a cross-copy operator for every q,h; common twists cancel.
These are representation controls, not full new anomaly-free field models.
A resolved nonzero neutron charge would falsify the stated single-End
package, not the other carriers. A null result cannot identify that package.
Run: python3 -B -O -m scripts.probe_finite_scalar_channels
"""

from __future__ import annotations

from collections import Counter
from itertools import combinations_with_replacement, product
from math import gcd

Form = tuple[int, int]
Block = tuple[int, int]
Pair = tuple[Block, Block]
N, U, Q, E, L, D = (0, 0), (2, 0), (1, 1), (0, 2), (3, 1), (2, 2)
BLOCKS = tuple((p, r) for p, r in product(range(4), range(3)) if (p + r) % 2 == 0)
MASKS = tuple(m for m in range(32) if m.bit_count() % 2 == 0)
# Field charges on the full, *symbolic* matched plane, in (q,h) coordinates.
Y: dict[Block, Form] = {
    Q: (1, 0),
    U: (-1, -1),
    D: (-1, 1),
    L: (-3, 0),
    E: (3, 1),
    N: (3, -1),
}
H: Form = (0, 1)


def require(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def add(x: Form, y: Form) -> Form:
    return x[0] + y[0], x[1] + y[1]


def sub(x: Form, y: Form) -> Form:
    return x[0] - y[0], x[1] - y[1]


def evaluate(x: Form, q: int, h: int) -> int:
    return x[0] * q + x[1] * h


def occupation(mask: int) -> Block:
    return (mask & 7).bit_count(), (mask >> 3).bit_count()


def color(b: Block) -> int:
    # Lambda^p 3 has type 1, 3, 3bar, 1. Complex SU(3), not just dimensions.
    return (0, 1, -1, 0)[b[0]]


def census() -> tuple[tuple[Pair, ...], tuple[Pair, ...]]:
    require(set(BLOCKS) == set(Y) == {occupation(m) for m in MASKS}, "wrong carrier")
    # Hom(A,B) has a color singlet iff A,B carry equivalent color irreps.
    # For a tensor pair one instead needs dual color irreps. Each singlet
    # has multiplicity one. Under SU(2), 2x2=1+3 (no doublet), 1x2=2.
    end = tuple(
        (a, b)
        for a, b in product(BLOCKS, repeat=2)
        if color(a) == color(b) and (a[1] == 1) != (b[1] == 1)
    )
    pairs = tuple(
        (a, b)
        for a, b in combinations_with_replacement(BLOCKS, 2)
        if color(a) == -color(b) and (a[1] == 1) != (b[1] == 1)
    )
    require(set(end) == {(L, N), (N, L), (L, E), (E, L)}, "single-End classification")
    require(
        {frozenset(v) for v in pairs}
        == {frozenset(v) for v in ((Q, U), (Q, D), (L, N), (L, E))},
        "Weyl-pair classification",
    )
    return end, pairs


def car_word(mask: int, ops: tuple[tuple[int, bool], ...]) -> tuple[int, int] | None:
    """Apply an ordered sequence of a_j or a_j†, including CAR signs."""
    sign = 1
    for j, create in ops:
        if bool(mask & (1 << j)) == create:
            return None
        if (mask & ((1 << j) - 1)).bit_count() % 2:
            sign = -sign
        mask ^= 1 << j
    return mask, sign


def locality_controls(end: tuple[Pair, ...]) -> None:
    locations: set[tuple[int, int]] = set()
    for a, b in end:
        dp, dr = sub(b, a)
        require(
            abs(dp) == 3 and abs(dr) == 1 and abs(dp + dr) in (2, 4),
            "degree/grade bound",
        )
        touched: set[int] = set()
        for j in (3, 4):
            # The three-color determinant is SU(3)-invariant. The two weak
            # choices span 2 or its dual (equivalent as SU(2) representations).
            ops = tuple((i, dp > 0) for i in range(3)) + ((j, dr > 0),)
            entries = [
                (m, out, sgn)
                for m in MASKS
                if (act := car_word(m, ops)) is not None
                for out, sgn in (act,)
            ]
            require(len(entries) == 1, "expected one matrix unit on the even carrier")
            src, dst, sign = entries[0]
            require(
                (occupation(src), occupation(dst)) == (a, b) and sign in (-1, 1),
                "wrong CAR block",
            )
            # Any shorter word cannot change four distinct occupations;
            # sums of shorter words still have zero in this matrix entry.
            require(
                (src ^ dst).bit_count() == len(ops) == 4,
                "minimum CAR degree not attained",
            )
            touched.update(i for i, _ in ops)
            locations.add((src, dst))
        require(len(touched) == 5, "address support of the two-component doublet")
    require(len(locations) == 8, "four independent doublets")
    # In the full Fock space a weak creation already has charge w and degree
    # one, but it cannot be an End(S) operator: every nonzero image is odd.
    images = [act[0] for m in MASKS if (act := car_word(m, ((3, True),))) is not None]
    require(
        bool(images) and all(n.bit_count() % 2 for n in images),
        "odd escape changes carrier",
    )


def spin_controls() -> None:
    # For two left spinors the epsilon contraction changes sign on spin-index
    # interchange; Grassmann interchange supplies a second minus, making the
    # internal flavor pair symmetric. Under SL(2,C), g^T epsilon g=det(g)epsilon.
    # For the different insertion psi^dagger M psi, even TWO spin transforms
    # exclude any scalar M. Rotation diag(i,-i) keeps only diagonal entries;
    # boost diag(2,1/2) keeps only off-diagonals (use twice the boost below).
    rotation_sign, twice_boost = (1, -1), (4, 1)
    surviving = [
        (i, j)
        for i, j in product(range(2), repeat=2)
        if rotation_sign[i] * rotation_sign[j] == 1
        and twice_boost[i] * twice_boost[j] == 4
    ]
    require(
        not surviving, "mixed-Weyl insertion incorrectly identified with Lorentz scalar"
    )


def symbolic_controls(end: tuple[Pair, ...], pairs: tuple[Pair, ...]) -> None:
    require(
        {sub(b, a) for a, b in end} == set(product((-3, 3), (-1, 1))),
        "mode differences",
    )
    # Cross-check the affine crosswalk AFTER the nonabelian census. Any
    # common offset cancels in End. For a matched family, s=3q-h.
    require(
        all(Y[p, r] == (3 - 2 * p, r - 1) for p, r in BLOCKS), "matched-plane crosswalk"
    )
    end_forms = {sub(Y[b], Y[a]) for a, b in end}
    require(end_forms == set(product((-6, 6), (-1, 1))), "End charges")
    # H occurs iff one of these linear forms vanishes; closed under adjoints,
    # so using +H tests both orientations. These equations yield the full
    # three-line locus over Q, not a search over bounded charges.
    require(
        {sub(z, H) for z in end_forms} == {(-6, 0), (6, 0), (-6, -2), (6, -2)},
        "scalar matching locus",
    )
    require(
        Counter(add(Y[a], Y[b]) for a, b in pairs) == {(0, 1): 2, (0, -1): 2},
        "Sym^2 rival",
    )
    # At the standard point, the two End copies of weight +/-3 are L<->N.
    require(
        {(a, b) for a, b in end if abs(evaluate(sub(Y[b], Y[a]), 1, 3)) == 3}
        == {(L, N), (N, L)},
        "an End Higgs-weight channel is not a quark Yukawa map",
    )
    # The determinant has symbolic weight 3c+2w = -6q+2h. Equal twists
    # on all copies cancel (Hom); adding an identical neutral copy only
    # repeats the same types. With one *relative* det(V) twist, the map
    # from L in copy 1 to the twisted vacuum in copy 2 carries exactly h.
    det = (-6, 2)
    require(
        {sub(add(Y[b], det), add(Y[a], det)) for a, b in end} == end_forms,
        "common twist",
    )
    require(sub(add(Y[N], det), Y[L]) == H, "relative determinant twist")


def neutron_controls(end: tuple[Pair, ...]) -> None:
    def allowed(q: int, h: int) -> bool:
        return any(evaluate(sub(Y[b], Y[a]), q, h) == h for a, b in end)

    require(allowed(0, 1) and allowed(1, 3) and allowed(-1, 3), "three algebraic lines")
    # Nonzero q and charged e remove q=0 and h=-3q, respectively. On the
    # remaining line 3q-h=0; gcd(2h,3q+h)=gcd(6q,6q)=6|q|. Z6 alone
    # is not necessarily the full kernel. Positive h=3q gives positive q.
    require(allowed(7, 21) and gcd(42, 42) == 42, "nonminimal charge normalization")
    # q=7,h=27 is a checked member of the exact-Z6 near-zero sequence
    # h=3q+6 from the earlier neutron probe: ordinary End excludes this
    # assignment, while paired Weyl fields or the relative twist admit it.
    require(not allowed(7, 27) and gcd(54, 48) == 6, "full-kernel alternative")


def main() -> None:
    end, pairs = census()
    locality_controls(end)
    spin_controls()
    symbolic_controls(end, pairs)
    neutron_controls(end)
    print(
        "Single even carrier: four color-singlet weak doublets, charges ±3c±w; minimum four CAR factors per component."
    )
    print(
        "None preserves occupation. A required End Higgs of weight h gives q=0 or h=±3q on the matched plane."
    )
    print(
        "With the neutron probe's charged electron, oriented lattice and exact Z6: q=1,h=3. This is a carrier condition."
    )
    print(
        "Symmetric left-Weyl pairs or a relative determinant twist supply ±h without fixing q/h; no scalar origin derived."
    )


if __name__ == "__main__":
    main()
