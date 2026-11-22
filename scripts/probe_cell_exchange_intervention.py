"""A fixed-two-occupation intervention on four reciprocal cell tables.

The table in probe_reversible_cell_census acts on actual ingress/egress
sides, a carried bit and a stored bit. It is an unsigned permutation.
Transport direction is encoded oppositely at ingress and egress. Global
direction reversal commutes with the table; its even/odd coherent sectors
can therefore acquire different signs without putting a sign in the table.
Occupancy and this reversal character are distinct: no superposition of
different total occupancies or particle-number parity reference is used.

SUPPLIED apparatus: two untouched binary spectators, preparation of one
occupation per input rail pair, coherent superposition of opposite incident
directions with a chosen relative sign and matched exit paths, addressed
number-preserving balanced mixers (the encoded T of gaussian_dyadic_words)
and its inverse on the *specified physical ports*, and grouped squared-norm
readout. These controls are NOT compiled in the census's classical petal.
Two output mixers must exchange their active-port ownership, not their
spectators: the table actually sends stored occupancy into the carried slot
and carried occupancy into the store. Joint detection is by rail occupations,
not persistent particle labels. No unphased inverse cell is inserted.

Compared with probe_exchange_sign_relator, no lifted word identity or
pre-existing many-body exchange sign is imposed. The invariant of four
amplitudes is unchanged by independent one-rail input/output rephasings;
an arbitrary two-occupation phase can imitate it. In a calibrated basis,
two returning local records coincide certainly or only half the time.
An unknown physical phase on a path changes this particular fringe even
though a mere change of coordinates does not change an observation.

This tests candidate conditional routing in an interferometer, not exchange
statistics. One table has BOTH direction sectors; neither a physical
preference for the odd sector nor an assignment to a particle species is
inferred. The ordinary comparator is an unsigned swap of binary slots,
not a full bosonic occupation space. The binary slot capacity is supplied,
not a derivation of Pauli exclusion.
Run: python3 -B -m scripts.probe_cell_exchange_intervention (also with -O).
"""

from fractions import Fraction as F
from itertools import product

from scripts import gaussian_dyadic_words as w
from scripts.probe_reversible_cell_census import inferred_rule

BITS = (0, 1)
PAIRS = tuple(product(BITS, repeat=2))
INPUT = ((0, 2), (1, 3))   # carrier/spectator A, store/spectator B
OUTPUT = ((1, 2), (0, 3))  # store/spectator A, carrier/spectator B


def need(test, detail):
    if not test:
        raise ArithmeticError(detail)


def add(ket, key, amplitude):
    ket[key] = ket.get(key, w.ZERO) + amplitude
    if ket[key] == w.ZERO:
        del ket[key]


def scatter(table, direction_bit, occ, ports=(0, 1)):
    """direction_bit=0 means moving right; its corresponding EXIT side is 1."""
    i, j = ports
    code = table[4*direction_bit + 2*occ[i] + occ[j]]
    out = list(occ)
    out[i], out[j] = (code // 2) % 2, code % 2
    return 1 - code // 4, tuple(out)


def tick(ket, table):
    moved = {}
    for (u, occ), amp in ket.items():
        add(moved, scatter(table, u, occ), amp)
    return moved


def mix(ket, ports, inverse=False):
    """Lift T only on a pair with exactly one occupation; exterior slots fixed."""
    i, j = ports
    d, z = w.DIAG, w.CROSS
    if inverse:
        d, z = d.star(), z.star()
    out = {}
    for (u, occ), amp in ket.items():
        need(occ[i] + occ[j] == 1 and sum(occ) == 2, "rail is outside the specified code")
        swapped = list(occ)
        swapped[i], swapped[j] = occ[j], occ[i]
        add(out, (u, occ), d * amp)
        add(out, (u, tuple(swapped)), z * amp)
    return out


def analyze(ket):
    for pair in OUTPUT:
        ket = mix(ket, pair, inverse=True)
    weights = {xy: F() for xy in PAIRS}
    for (_u, occ), amp in ket.items():
        weights[occ[1], occ[0]] += amp.norm2()
    return weights


def local_phases(h):
    # Multiplying a local port by an arbitrary unit phase changes h_xy by a
    # row phase times a column phase, so the four phases cancel pairwise.
    # Finite stress control: every fourth-root relative phase in both rails.
    def cross(z):
        return z[0,0] * z[1,1] * (z[0,1] * z[1,0]).star()

    value = cross(h)
    roots = (w.ONE, w.I, w.g(-1), w.g(0, -1))
    for l, r in product(roots, repeat=2):
        z = {(x,y): amp*(l if x else w.ONE)*(r if y else w.ONE)
             for (x,y), amp in h.items()}
        need(cross(z) == value, "local phase changed the four-amplitude invariant")
    return value


def trial(a, c, odd):
    table = inferred_rule(a, c)
    char = -1 if odd else 1
    # Common squared norm 2 avoids irrational 1/sqrt(2); neither direction
    # is postselected. Both excitations start in the two spectator slots.
    bare = (0, 0, 1, 1)
    ket = {(u, bare): w.g(char**u) for u in BITS}
    for pair in INPUT:
        ket = mix(ket, pair)
    raw = tick(ket, table)
    need(len(raw) == 8 and sum(z.norm2() for z in raw.values()) == 2,
         "full raw permutation lost amplitude")
    h = {}
    for x, y in PAIRS:
        orig, dest = (x, y, 1-x, 1-y), (y, x, 1-x, 1-y)
        for u in BITS:
            need(scatter(table, u, orig) == (u ^ (a*(x^y)) ^ (c*x*y), dest),
                 "travel direction/side or actual occupancy transfer changed")
        coeff = char ** (a*(x^y) ^ (c*x*y))
        h[x,y] = w.g(coeff)
        for u in BITS:
            need(raw[u,dest] == h[x,y] * ket[u,orig], "parity reduction failed on raw ket")
    need(local_phases(h) == w.g(char**c), "double-occupation invariant")
    # Fixed-phase interferometer; both output settings read an ACTUAL balanced
    # inverse mixer on the outgoing active slot and its matching spectator.
    prob = {k: v/2 for k, v in analyze(raw).items()}
    need(sum(prob.values()) == 1, "incomplete readout")
    deterministic = (int(odd)*a,) * 2
    uniform = {xy: F(1,4) for xy in PAIRS}
    need(prob == (uniform if odd and c else
                  {xy: F(xy == deterministic) for xy in PAIRS}), "output distribution")
    # Phase-insensitive alternative: trace the matching other rail and both
    # travel sheets. Local marginal purity does not depend on rail phases.
    def amp(u, x, y):
        return raw[u, (y, x, 1-x, 1-y)]
    rho = {(x,z): w.g(F(1,2))*sum((amp(u,x,y)*amp(u,z,y).star()
                                    for u,y in PAIRS), w.ZERO) for x,z in PAIRS}
    purity = sum(z.norm2() for z in rho.values())
    need(purity == (F(1,2) if odd and c else 1), "single output rail purity")
    # Purity is not itself a one-shot detector outcome. Two actual analyzer
    # settings (unchanged or i on output A's active slot before its inverse
    # mixer) give orthogonal marginal fringe quadratures. Test even an
    # unknown physical phase, not a coordinate transformation of all ports.
    # The rational unit phase is a stress case, not a synthesized instruction.
    for drift in (w.ONE, w.I, w.g(F(3,5), F(4,5))):
        contrasts = []
        for setting in (w.ONE, w.I):
            framed = {k: z*(setting*drift if k[1][1] else w.ONE) for k,z in raw.items()}
            out = analyze(framed)
            contrasts.append(sum((1-2*x)*val/2 for (x,_),val in out.items()))
        need(sum(z*z for z in contrasts) == 2*purity-1, "two measured fringe quadratures")
        if drift == w.I:
            need(contrasts[0] == 0, "single calibrated fringe alone is not gauge-robust")
    # Complete which-occupation recording with the record ignored; keep
    # direction amplitudes coherent INSIDE each occupied configuration.
    erased = {xy: F() for xy in PAIRS}
    for x, y in PAIRS:
        branch = {key:z for key,z in raw.items() if key[1][:2] == (y,x)}
        for key, weight in analyze(branch).items():
            erased[key] += weight/2
    need(erased == uniform, "ignored full which-occupation record")
    return prob[0,0] + prob[1,1], purity


def adjacent_controls(a, c):
    # One common direction register, NOT a direction sector per putative
    # particle. This is a supplied multiport embedding, not a petal theorem.
    table = inferred_rule(a,c)
    def walk(state, word):
        for j in word:
            state = scatter(table, *state, (j,j+1))
        return state
    for occ in product(BITS, repeat=4):
        for u in BITS:
            state = (u, occ)
            need(walk(state,(0,0)) == state and walk(state,(0,2)) == walk(state,(2,0))
                 and walk(state,(0,1,0)) == walk(state,(1,0,1)),
                 "adjacent swap relations must not select either c")
            for j in range(3):
                v, dest = walk(state,(j,))
                # Alternating-site choice of one-body phase removes a on an
                # adjacent chain in the odd sector. No claim for all-to-all
                # direct ports or equality of different physical splice paths.
                parity = sum(k*(s-t) for k,(s,t) in enumerate(zip(occ,dest))) % 2
                need(sum(occ) == sum(dest) and
                     (u ^ v ^ (a*parity)) == c*occ[j]*occ[j+1], "one-body gauge")


def main():
    for a,c in PAIRS:
        adjacent_controls(a,c)
        even, odd = (trial(a,c,t) for t in BITS)
        print(f"a={a} c={c}: (P[equal output bits], one-rail purity)"
              f" even={tuple(map(str,even))}, odd={tuple(map(str,odd))}.")
    print("All trials retain two occupations and both exit directions. Odd sheet:"
          " calibrated equal-output probability 1 vs 1/2; even sheet: both 1."
          " No physical particle statistics or preparation is inferred.")


if __name__ == "__main__":
    main()
