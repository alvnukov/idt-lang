"""A six-position fringe using opposite marks and a literal incidence detector.

Choose an oriented completion (a,b,c), one mark from each of three opposite
pairs, and choose its origin q. Let p cycle the three marks and their opposites
in parallel, O take the opposite, r=Op. Then r is a six-cycle and r^3=O.
D={r^{-1}q,q,rq} is itself a completion. Count one bright outcome iff the
single emitted mark belongs to D, dark otherwise. This binary routing is
supplied; merely reading the four compatible vertices is not such a detector.
Start at r^{-1}q and take two independent fair choices of I or r. The four
histories create stock 1:2:1. Counting the same fixed D after n further
pulses gives the six-setting benchmark without a stochastic detector table.

For fixed r,D and a normalized positive source, P(0)=1 forces support on D;
P(3)=0 is redundant since r^3 interchanges D and its complement. If the
masses in order on D are a,b,c, the entire row is (1,a+b,a,0,c,b+c).
The FULL fringe fixes these three masses, the endpoints do not. It does not
fix preparation histories: in order 00,01,10,11 the probabilities may be
(1/4,t,1/2-t,1/4), 0<=t<=1/2. Equal stock alone need not be iid sampling.
The fair source, selected orientation, initial mark, fixed binary detector
and actual actuation are not consequences of opposition alone.

Actuation matters. We exhaust the already specified clock scatterers on
ordered marks, separately holding the spare transparent or flipped. Each
fixed family generates an S4; neither contains any order-six permutation.
Even a fresh draw from one fixed distribution of such words at every pulse
cannot exactly match lengths 0..7 with just the six marks. For its
stochastic matrix T=sum_g w_g P_g, a unit eigenvalue z=exp(i*pi/3) would
force P_g v=zv for each positive-weight g: the convex average of equal-norm
vectors is on that sphere only when all coincide. No member has that
eigenvalue. Conversely, a six-state homogeneous kernel reproducing the
eight centered responses y_n=cos(n*pi/3) must have z as an eigenvalue:
Cayley-Hamilton at offsets 0,1 annihilates both six-step recurrences.
Divide the characteristic polynomial by t^2-t+1; the remainder A+Bt
then obeys A+B/2=0 and A/2-B/2=0. Thus z is a root. Centering the readout
is legitimate because total probability is conserved. This argument is
for one stationary kernel without uncounted memory; it is NOT a finite
bound for arbitrary shared mixtures over different stochastic kernels.

An alternative drawn once per emission and held fixed yields a mixture of
permutation periods 1,2,3,4: their six-phase cosine correlation vanishes
over 12 consecutive equally weighted lengths. This too is a scoped test.
A mixed-law word or an added active O generates the direct six-cycle.
Passive transport of BOTH chart and mark leaves incidence unchanged.

Fixed-law escape: two reusable transparent-spare scatterers on an
alternating shuttle. Its actual state is (mark,site); the site advances
only on an applied pulse. One selected six-state joint orbit has three
consecutive bright and three dark literal marks, even though the mark
alone repeats. A binary switch or two-site wiring and the initial site are
extra. The natural autonomous flag update (u,v)->(v,O(u)) instead reuses
the SAME scatterer and does not select this alternating schedule.
The comparison need not stop at a shared fringe. Align both models to the
same bright completion (0,2,5), prepare a single literal mark 0 before the
two fair choices (omit those choices in this control), and apply three
pulses. The direct rotor gives O(0)=1; the listed shuttle gives mark 4.
The second fixed incidence detector (1,3,5) on the same sheet distinguishes
the two with certainty in these fixtures, if source and analyzer access
are physically available. No intermediate readout or loss filter is used.
Across ALL 96 passing single-gate transparent shuttles, exactly one of
the three (j,j+3) literal pairs is opposite; for the rotor all three are.
Repeatably prepare the singleton and test each of four completion analyzers
on that sheet at lengths 0..5 in separate trials. Each shuttle fails four
of twelve complement identities, the rotor none. This is a further test
of each stable deterministic fixture, not an assertion that averaging
unidentified fixtures preserves mismatches of opposite sign.

For eight independently uniform six-position dials and the counted,
single-forward-channel contract of probe_serial_phase_memory, five
classical symbols have |S| <= (2/3)((4+sqrt(3))/6)^7 < 1/2. Six suffice
on either complete constructed orbit. This is an exact finite capacity
result in that contract, not a measurement, a native arm interferometer,
or an inference about quantum amplitudes, particles or spatial geometry.

Run: python3 -B -O -m scripts.probe_six_mark_phase_origin
"""

import sys
from collections import Counter, deque
from collections.abc import Callable, Hashable, Sequence
from itertools import product
from pathlib import Path
from typing import TypeVar

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_opposition_clock_scatter import FLAGS, G, chart, extend
from scripts.probe_serial_phase_memory import HEX, partition_maximum, positive
from scripts.probe_three_opposition_origin import DUAL, SHEET, WORDS, X, need

Perm = tuple[int, ...]
WordMap = dict[Perm, tuple[int, ...]]
ShuttleState = tuple[int, int]
ShuttleStep = Callable[[ShuttleState], ShuttleState]
ShuttleOrbit = tuple[ShuttleState, ...]
Witness = tuple[int, int, int, tuple[int, ...], ShuttleOrbit, ShuttleStep]
State = TypeVar("State", bound=Hashable)

I = tuple(X)
O = tuple(x ^ 1 for x in X)
W = (0, 2, 4)
P = (2, 3, 4, 5, 0, 1)


def after(g: Perm, h: Perm) -> Perm:
    return tuple(g[t] for t in h)


R = after(O, P)


def orbit(step: Callable[[State], State], start: State) -> tuple[State, ...]:
    states: list[State] = []
    s = start
    while s not in states:
        states.append(s)
        s = step(s)
    need(s == start, "a transient was mistaken for a cycle")
    return tuple(states)


def reach(gens: Sequence[Perm]) -> WordMap:
    """Shortest chronological words, generator indices in lexicographic order."""
    words: WordMap = {I: ()}
    todo = deque([I])
    while todo:
        h = todo.popleft()
        for i, g in enumerate(gens):
            nxt = after(g, h)
            if nxt not in words:
                words[nxt] = words[h] + (i,)
                todo.append(nxt)
    return words


def permutation_order(g: Perm) -> int:
    return len(orbit(lambda h: after(g, h), I))


def group_checks() -> tuple[list[Perm], list[Perm], WordMap]:
    trans, flip = (sorted({extend(u, v, f) for u, v in FLAGS}) for f in (False, True))
    gs, gf = reach(trans), reach(flip)
    for group in (gs, gf):
        orders = Counter(map(permutation_order, group))
        need(orders == {1: 1, 2: 9, 3: 8, 4: 6}, "wrong fixed-law order census")
        # The four completion/complement pairs are relabeled faithfully: S4.
        need(len({chart(g)[1] for g in group}) == 24, "not faithful on four pairs")
        need(len(group[P]) == 2 and R not in group and O not in group, "actuator wall")
        # Tests the once-selected, fixed-per-emission permutation rival for
        # EVERY initial mark and deterministic readout basis, hence all mixtures.
        for g, x in product(group, X):
            response = [0] * 6
            for n in range(12):
                response[x] += HEX[n % 6][0]
                x = g[x]
            need(response == [0] * 6, "nonzero planted sixth harmonic")
    mixed = reach(sorted(set(trans) | set(flip)))
    need(
        set(mixed) == set(G) and len(gs.keys() & gf.keys()) == 12, "group intersection"
    )
    need(len(mixed[R]) == 2 and len(mixed[O]) == 2, "wrong mixed-law word length")
    need(after(extend(5, 0, True), extend(3, 0, False)) == R, "mixed word mismatch")
    need(
        all(extend(v, u ^ 1, False) == extend(u, v, False) for u, v in FLAGS),
        "natural flag already changes the scatterer",
    )
    # Exact scalar checks for the two-offset characteristic-polynomial argument.
    c = [HEX[n % 6][0] for n in range(8)]  # twice the centered harmonic
    need(all(c[j + 2] - c[j + 1] + c[j] == 0 for j in range(6)), "recurrence")
    need(c[0] * c[2] - c[1] ** 2 == -3, "the two remainder constraints are dependent")
    return trans, flip, gf


def direct_checks() -> tuple[Callable[[int], int], int, set[int]]:
    q = W[0]
    d = {R.index(q), q, R[q]}
    need(
        after(P, after(P, P)) == I and tuple(P[x] for x in W) == W[1:] + W[:1],
        "bad oriented completion",
    )
    need(len(orbit(R.__getitem__, q)) == 6 and after(R, after(R, R)) == O, "bad root")
    need(
        tuple(sorted(d)) in SHEET
        and tuple(sorted(O[x] for x in d)) in DUAL
        and {O[x] for x in d} == set(X) - d,
        "bad detector",
    )
    # Relabeling both together never changes a detector bit; actual r^3 does.
    need(q in d and O[q] not in d and O[q] in {O[x] for x in d}, "passive/active")
    # Basis response columns prove the general normalized-source formula,
    # including nonuniform preparations, not just four equally weighted seeds.
    states = orbit(R.__getitem__, R.index(q))
    cols = [tuple(int(states[(j + n) % 6] in d) for n in range(6)) for j in range(3)]
    need(
        cols == [(1, 1, 1, 0, 0, 0), (1, 1, 0, 0, 0, 1), (1, 0, 0, 0, 1, 1)],
        "readout does not identify the three source masses as stated",
    )
    need(len({tuple(g[x] for x in W) for g in G}) == 48, "unintended favored frame")
    # Another allowed completion, W itself, has an alternating incidence word.
    need(tuple(int(s in W) for s in states) == (0, 1, 0, 1, 0, 1), "detector rival")
    return R.__getitem__, R.index(q), d


def shuttle_cycle(g0: Perm, g1: Perm, q: int) -> tuple[ShuttleOrbit, ShuttleStep]:
    def step(s: ShuttleState) -> ShuttleState:
        x, site = s
        return (g0, g1)[site][x], 1 - site

    return orbit(step, (q, 0)), step


def shuttle_witnesses(
    gates: Sequence[Perm], *, test_opposites: bool = False
) -> tuple[int, Witness | None]:
    count = 0
    first: Witness | None = None
    for i, j, q in product(range(len(gates)), range(len(gates)), X):
        states, step = shuttle_cycle(gates[i], gates[j], q)
        if len(states) != 6:
            continue
        for d in WORDS:
            if tuple(int(x in d) for x, _ in states) == (1, 1, 1, 0, 0, 0):
                count += 1
                if test_opposites:
                    pairs = [(states[k][0], states[k + 3][0]) for k in range(3)]
                    sheet = SHEET if d in SHEET else DUAL
                    need(sum(y == (x ^ 1) for x, y in pairs) == 1, "antipodal census")
                    need(
                        sum((x in v) == (y in v) for x, y in pairs for v in sheet) == 4,
                        "changed incidence-only discrimination",
                    )
                if first is None:
                    first = i, j, q, d, states, step
    return count, first


def checksum(
    step: Callable[[State], State],
    start: State,
    bright: Callable[[State], bool],
    k: int = 8,
) -> int:
    """Propagate every choice and preparation history, not a postselected sample."""
    counts: Counter[tuple[int, State]] = Counter()
    for a, b in product(range(2), repeat=2):
        s = start
        for _ in range(a + b):
            s = step(s)
        counts[0, s] += 1
    for _ in range(k):
        following: Counter[tuple[int, State]] = Counter()
        for (t, s), mass in counts.items():
            for x in range(6):
                following[(t + x) % 6, s] += mass
                s = step(s)
        counts = following
    total = sum(counts.values())
    quarters = (4, 3, 1, 0, 1, 3)
    score2 = 0
    for t, expected in enumerate(quarters):
        row = [(s, mass) for (n, s), mass in counts.items() if t == n]
        mass = sum(m for _, m in row)
        plus = sum(m for s, m in row if bright(s))
        need(mass == 4 * 6 ** (k - 1) and 4 * plus == expected * mass, "fringe row")
        score2 += HEX[t][0] * (2 * plus - mass)
    need(total == 4 * 6**k and score2 == total, "lost histories or wrong score")
    return total


def capacity() -> None:
    # Enumerates all 5^6 deterministic extreme assignments; convexity covers
    # stochastic channels under the independence and cut contract stated above.
    need(
        partition_maximum(2) == (4, 0) and partition_maximum(5) == (4, 1),
        "five-symbol or terminal contraction",
    )
    a, b, d = 2, 0, 3
    for k in range(1, 9):
        if k in (7, 8):
            need(
                positive(2 * a - d, 2 * b) == (k == 7), "wrong first separated horizon"
            )
            need((2 * a - d, 2 * b) != (0, 0), "no strict separation")
        a, b, d = 4 * a + 3 * b, a + 4 * b, 6 * d


def main() -> None:
    trans, flip, gf = group_checks()
    step, start, d = direct_checks()
    total = checksum(step, start, d.__contains__)
    n, first = shuttle_witnesses(trans, test_opposites=True)
    if n != 96 or first is None:
        raise ArithmeticError("no fixed transparent-law shuttle")
    i, j, q, det, states, shuttle_step = first
    need(
        (i, j, q, det) == (0, 2, 0, (0, 2, 5))
        and tuple(x for x, _ in states) == (0, 0, 2, 4, 4, 3),
        "shuttle certificate",
    )
    need(
        checksum(shuttle_step, (q, 0), lambda s: s[0] in det) == total,
        "joint-state shuttle failed the shared readout",
    )
    # Align the direct rotor to this exact starting mark AND detector, not
    # just an unrelated phase chart. Both possible direct alignments predict O(q).
    alignments = [
        cycle
        for r in G
        if after(r, after(r, r)) == O
        and len(cycle := orbit(r.__getitem__, q)) == 6
        and tuple(int(x in det) for x in cycle) == (1, 1, 1, 0, 0, 0)
    ]
    probe = (1, 3, 5)
    need(
        det in DUAL and probe in DUAL and len(alignments) == 2, "unaligned tag control"
    )
    need(
        all(cycle[3] == q ^ 1 and cycle[3] in probe for cycle in alignments)
        and states[3][0] not in probe,
        "shared fringe hid a wrong tag prediction",
    )
    need(
        all(
            (cycle[k] in v) != (cycle[k + 3] in v)
            for cycle in alignments
            for k in range(3)
            for v in DUAL
        ),
        "rotor failed its incidence-only antipodal test",
    )
    need(
        shuttle_witnesses(flip) == (0, None), "unexpected flip-spare single-gate orbit"
    )
    need(shuttle_witnesses(sorted(gf)) == (0, None), "unexpected flip-spare word orbit")
    capacity()
    print(
        "Six marks + fixed completion-incidence detector + 1:2:1 preparation: "
        "right quarters = (4,3,1,0,1,3). Endpoints alone leave all three source masses free to sum to one."
    )
    print(
        "Each fixed scatter law generates S4, |G|=24: p costs two, r impossible. "
        "Mixed laws generate 48: r costs two. Active opposition is not a chart change."
    )
    print(
        "Transparent-law two-site shuttle: 96 marked 111000 six-orbits "
        "(ordered gate pair, start at first site, detector); flip law: 0 even for two fixed words."
    )
    print(
        f"Example gates {i},{j}, start {q}, detector {det}, data {tuple(x for x, _ in states)}. "
        "The site is dynamical memory, not a free clock."
    )
    print(
        "Prepared singleton 0, three pulses, detector (1,3,5): direct rotor bright "
        "(mark 1), stated shuttle dark (mark 4). Across all 96 shuttles, "
        "four of twelve antipodal incidence identities fail; direct rotor: none."
    )
    print(
        f"Eight dials: both complete six-state orbits score 1/2 on {total} preparation/word histories; "
        "five-symbol upper bound (2/3)((4+sqrt(3))/6)^7 < 1/2."
    )


if __name__ == "__main__":
    main()
