"""Inverse charge test for the SUPPLIED chiral multiplets, without an exterior charge law.

Take one left-Weyl Q,u^c,d^c,L,e^c,N^c with the benchmark nonabelian
representations (3,2), (3bar,1), (3bar,1), (1,2), (1,1), (1,1).
The six U(1) charges are initially independent. Use the conventional 4D
local anomaly constraints without inflow or extra chiral fields. The pure
SU(3) anomaly and ordinary SU(2) doublet parity are already fixed by those
representations. Scalars make no chiral contribution. We do not assume a
traceless five-mode generator, affine vacuum charge, or family neutrality.

The three linear anomaly equations give (q,-q-a,-q+a,-3q,3q+b,3q-b).
The cubic coefficient is 18q(b²-a²): over the rationals the full solution
is the union of q=0, b=a and b=-a, including their intersections. Exchanging
equal-representation singlet labels can exchange the last two branches.
Holding the labels fixed, one Higgs doublet H and all four conventional
Yukawa links give a=h=b, leaving span(6Y,3(B-L)); these links are inputs,
not four independent filters. A nonzero *bare* N^c N^c pairing (constant
neutral coefficient, no transforming spurion) cuts this plane to the 6Y
line, including zero, without setting a charge unit or any mass scale.
The number projector N†N makes no such cut. Nor does a neutral apparatus
label on its own identify N^c or supply a pairing of two same-charge fields.
On the existing even exterior labels, complement-centered affine charges
s+p c+r w give q=-c/2 and a=b=w. Thus the earlier affine ansatz and the
matched Yukawa links describe the same rational plane on these labels;
they are not independent evidence for a physical interaction.

Three-copy control: all-generation anomaly cancellation and nonzero
diagonal Yukawa links do not require family-universal charges. A full-rank
symmetric sterile mass support can pair oppositely charged flavors. Connected
quark links, a loop at e and a mu-tau sterile pairing still allow L_mu-L_tau.
Connecting the lepton Yukawa graph removes that direction. These are support
hypotheses, NOT measured mixing, masses, or evidence that neutrinos are
Majorana. Neutrality from assumed mass interactions is familiar physics:
Babu and Mohapatra, https://doi.org/10.1103/PhysRevD.41.271 . The result
here is a diagnostic of the assumptions behind the packet comparison.
No gauge fields, Weyl statistics, Yukawa interaction, or spacetime physics
are derived. This executable uses exact coefficients and ranks, not Lean.
Run: python3 -B -O -m scripts.probe_packet_charge_pairings
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations_with_replacement
from math import prod

Row = tuple[int, ...]
Rows = tuple[Row, ...]
Q, U, D, L, E, N, H = range(7)
DIMS: Row = (6, 3, 3, 2, 1, 1)
LINEAR: Rows = ((2, 1, 1, 0, 0, 0), (3, 0, 0, 1, 0, 0), DIMS)
SM: Row = (1, -4, 2, -3, 6, 0, 3)  # 6Y, including H
BL: Row = (1, -1, -1, -3, 3, 3, 0)  # 3(B-L), including H
# Rows are field charges as linear forms on (q,a,b).
FORMS: Rows = ((1, 0, 0), (-1, -1, 0), (-1, 1, 0), (-3, 0, 0), (3, 0, 1), (3, 0, -1))


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise ArithmeticError(reason)


def dot(x: Row, y: Row) -> int:
    return sum(a * b for a, b in zip(x, y, strict=True))


def rank(rows: Rows) -> int:
    """Rank over Q; inputs need not be square."""
    if not rows:
        return 0
    n = len(rows[0])
    require(all(len(row) == n for row in rows), "ragged matrix")
    matrix = [[Fraction(v) for v in row] for row in rows]
    pivot = 0
    for col in range(n):
        found = next((i for i in range(pivot, len(rows)) if matrix[i][col]), None)
        if found is None:
            continue
        matrix[pivot], matrix[found] = matrix[found], matrix[pivot]
        for i in range(pivot + 1, len(rows)):
            c = matrix[i][col] / matrix[pivot][col]
            if c:
                matrix[i] = [
                    a - c * b for a, b in zip(matrix[i], matrix[pivot], strict=True)
                ]
        pivot += 1
    return pivot


def certificate(equations: Rows, basis: Rows) -> None:
    """Kernel equality via membership, independence, rank and nullity."""
    width = len(equations[0])
    require(all(dot(eq, v) == 0 for v in basis for eq in equations), "not in kernel")
    require(rank(basis) == len(basis) == width - rank(equations), "wrong nullspace")


def transpose(rows: Rows) -> Rows:
    return tuple(tuple(col) for col in zip(*rows, strict=True))


def cubic_coefficients(forms: Rows, dimensions: Row) -> dict[tuple[int, int, int], int]:
    """Expand sum d_i (form_i)^3, collecting all monomials, not sample points."""
    result: dict[tuple[int, int, int], int] = {}
    for monomial in combinations_with_replacement(range(len(forms[0])), 3):
        distinct = len(set(monomial))
        multiplicity = {1: 1, 2: 3, 3: 6}[distinct]
        c = sum(
            d * prod(row[j] for j in monomial)
            for row, d in zip(forms, dimensions, strict=True)
        )
        if c:
            result[monomial] = c * multiplicity
    return result


def anomalies(charges: Row) -> Row:
    return tuple(dot(row, charges) for row in LINEAR) + (
        dot(DIMS, tuple(x**3 for x in charges)),
    )


def one_family_anomalies() -> None:
    require(2 - 1 - 1 == 0 and (3 + 1) % 2 == 0, "nonabelian representation controls")
    certificate(LINEAR, transpose(FORMS))
    require(
        cubic_coefficients(FORMS, DIMS) == {(0, 2, 2): 18, (0, 1, 1): -18}, "factor"
    )
    exceptional = tuple(dot(row, (0, 1, 2)) for row in FORMS)
    require(exceptional == (0, -1, 1, 0, 2, -2), "exceptional witness")
    require(
        anomalies(exceptional) == (0,) * 4
        and abs(exceptional[U]) != abs(exceptional[E]),
        "exceptional witness is not separated",
    )
    # Nonzero q, b=-a: anomaly-free, but not on the *fixed-labeled* Yukawa plane.
    opposite = tuple(dot(row, (1, 2, -2)) for row in FORMS)
    require(
        anomalies(opposite) == (0,) * 4
        and -(opposite[Q] + opposite[U]) != opposite[L] + opposite[E],
        "unmatched branch",
    )
    # With N omitted its contributions are zero. Anomalies alone still allow this.
    unusual = (0, -1, 1, 0, 0, 0)
    require(
        anomalies(unusual) == (0,) * 4
        and unusual[N] == 0
        and rank((unusual, SM[:6])) == 2,
        "exceptional no-sterile control",
    )


def equation(copies: int, terms: tuple[tuple[int, int], ...]) -> Row:
    r = [0] * (6 * copies + 1)
    for i, c in terms:
        r[i] += c
    return tuple(r)


def family_linear(copies: int) -> Rows:
    return tuple(row * copies + (0,) for row in LINEAR)


def link(copies: int, i: int, j: int, doublet: int, singlet: int, hsign: int) -> Row:
    return equation(
        copies, ((6 * i + doublet, 1), (6 * j + singlet, 1), (6 * copies, hsign))
    )


def diagonal_yukawa(copies: int) -> Rows:
    return tuple(
        link(copies, i, i, x, y, sign)
        for i in range(copies)
        for x, y, sign in ((Q, U, 1), (Q, D, -1), (L, E, -1), (L, N, 1))
    )


def majorana(copies: int, i: int, j: int) -> Row:
    return equation(copies, ((6 * i + N, 1), (6 * j + N, 1)))


def one_family_pairings() -> None:
    eqs = family_linear(1) + diagonal_yukawa(1)
    certificate(eqs, (SM, BL))
    # Crosswalk to the supplied even blocks in probe_five_slot_charge, in
    # order Q, u^c, d^c, L, e^c, N^c. Complement-conjugacy fixes 2s=-3c-2w.
    # Work with doubled charges so the two coefficient vectors stay integral.
    occupations = ((1, 1), (2, 0), (2, 2), (3, 1), (0, 2), (0, 0))
    fock = tuple((2 * p - 3, 2 * r - 2) for p, r in occupations)
    require(fock[Q] == (-1, 0) and fock[N] == (-3, -2), "q and affine vacuum")
    # h=w is a parameter identification, NOT an exterior scalar/Higgs construction.
    certificate(eqs, transpose(fock + ((0, 2),)))
    require(
        not cubic_coefficients(transpose((SM[:6], BL[:6])), DIMS),
        "cubic on Yukawa plane",
    )
    self_pair = majorana(1, 0, 0)
    certificate(eqs + (self_pair,), (SM,))
    # Omit N entirely: its charge contributions vanish and its Yukawa link
    # does not exist. Padding N=0 embeds the reduced calculation in these columns.
    certificate(
        family_linear(1) + diagonal_yukawa(1)[:-1] + (equation(1, ((N, 1),)),), (SM,)
    )
    hermitian = equation(1, ((N, -1), (N, 1)))
    certificate(eqs + (hermitian,), (SM, BL))
    variant = tuple(x + y for x, y in zip(SM, BL, strict=True))
    require(
        variant[H] == SM[H] != 0
        and dot(self_pair, variant) == 6
        and dot(hermitian, variant) == 0,
        "same Higgs, charged sterile",
    )


def repeat_charge(row: Row, copies: int) -> Row:
    return row[:6] * copies + (row[H],)


def flavor_pairings() -> None:
    copies = 3
    sm, bl = repeat_charge(SM, copies), repeat_charge(BL, copies)
    diff: Row = (0,) * 6 + (0, 0, 0, 1, -1, -1) + (0, 0, 0, -1, 1, 1) + (0,)
    diag = family_linear(copies) + diagonal_yukawa(copies)
    quark_links = tuple(link(copies, i, i + 1, Q, U, 1) for i in (0, 1))
    lepton_links = tuple(link(copies, i, i + 1, L, N, 1) for i in (0, 1))
    masses = (majorana(copies, 0, 0), majorana(copies, 1, 2))
    # One exact nonsingular realization of the symmetric support; no scales fitted.
    require(rank(((1, 0, 0), (0, 0, 1), (0, 1, 0))) == 3, "mass support is singular")
    partial = diag + quark_links + masses
    certificate(partial, (sm, diff))
    require(
        not cubic_coefficients(transpose((sm[:-1], diff[:-1])), DIMS * copies),
        "global cubic on residual flavor plane",
    )
    require(
        dot(LINEAR[1], diff[6:12]) == 1 and dot(LINEAR[1], diff[12:18]) == -1,
        "flavor cancellation must be allowed across generations",
    )
    certificate(diag + quark_links + lepton_links, (sm, bl))
    certificate(partial + lepton_links, (sm,))


def main() -> None:
    one_family_anomalies()
    one_family_pairings()
    flavor_pairings()
    print(
        "Six free charges: exact anomaly locus q=0 or b=a or b=-a; exceptional (0,-1,1,0,2,-2)."
    )
    print(
        "Four supplied Yukawa links: span(6Y,3(B-L)); N†N leaves both, bare N N leaves only 6Y up to scale."
    )
    print(
        "The old centered-affine exterior ansatz gives that same Yukawa charge plane, not independent evidence."
    )
    print(
        "Three copies: full-rank sterile support may retain L_mu-L_tau; connecting the supplied flavor links cuts it."
    )
    print(
        "Only conditional charge constraints. No native charge, pairing, mass, mixing, or generation count derived."
    )


if __name__ == "__main__":
    main()
