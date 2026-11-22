"""Compile the unsigned complementary-packet mixer on a three-store petal.

Slots 0..3 are the mobile bit and the three stationary binary stores in
forward order. A packet is a separately prepared two-of-four configuration,
not two arbitrary incident free marks. Start on a fixed hub side. F means
one *first return*, even if unmarked; B means the same with the first store
transparent in both directions. Its bit remains intact. Both retain the
physical outgoing direction: nobody re-aims the mobile between letters.

SYNTHESIS, not a holdout: search for a word mapping all six prepared inputs
to complement after some four-cycle of the addressed slots, with direction
restored. All four cell laws previously survived the unrelated blank timing
census. We give one word and test it on all four. It was selected using the
full six-input table, not discovered from a single port fringe. The physical
edge replay, time-reversed replay and independent marginal check below test
the implementation, not whether this is a law of nature.

Supplied: binary storage, duplicate lanes, single mobile, preparing the
six distinct pairs, a designated bypassable store, and a controller that
advances its externally programmed word on each hub return and installs
the next setting before the mobile reaches that store. Distinguishable hub
lanes and passive repeatable logging are supplied. No physical controller,
finite-speed delivery of settings or local record construction is derived. Physical costs exclude switching, preparation, and detector work.

On N such runs the actual output marginals are N minus the permuted input
marginals. No phase preparation, norm measurement or hidden choice of how
to pair simultaneous free marks occurs. Admissible nonnegative histograms,
two marks per run, are essential. At fixed N the centered marginals are
merely negated and permuted, not split into coherent alternatives. The
four-slot code need not survive an overlapping next gate. One deterministic
run is not a Born trial. Timings can retain distinguishable path information.
The successful cell reflects on double occupation: the distinct integer-load
exchange that always exits the opposite side does NOT supply that route.
Run: python3 -B -O -m scripts.probe_mobile_cell_complement_mixer
"""

from collections import deque
from functools import cache
from itertools import combinations, combinations_with_replacement, permutations, product

from scripts.probe_reversible_cell_census import TablePetal, inferred_rule

EDGES = tuple(combinations(range(4), 2))
STATES = tuple(product((1, -1), EDGES))  # fixed-weight search domain
ALL_PACKETS = tuple(e for k in range(5) for e in combinations(range(4), k))
ALL_STATES = tuple(product((1, -1), ALL_PACKETS))
WORD = "FFBFFFBFBFBFBBFB"
TURN = (2, 3, 1, 0)  # images 0->2->1->3->0; NOT the spatial ring order
HOPS = (216, 256, 240, 264, 224, 320)


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def target(edge, p=TURN):
    return tuple(i for i in range(4) if i not in (p[edge[0]], p[edge[1]]))


class Petal(TablePetal):
    def __init__(self, law, bypass):
        self.bypass = bypass
        super().__init__((4,), law)

    def scatter(self, v, ingress, mask):
        if self.bypass and v in self.cells and self.cells[v][0] == 1:
            _, ports, names = self.cells[v]
            side, lane = names[ingress]
            return ports[-side, lane], mask
        return super().scatter(v, ingress, mask)

    def physical_return(self, direction, edge):
        mask = sum(1 << (i-1) for i in edge if i)
        raw = 0, self.starts[0, direction, int(0 in edge)], mask
        seen = set()
        while raw not in seen:
            # Launch above already advanced one edge out of the hub.
            seen.add(raw)
            prev, here, mask = raw
            if here == 0:
                lane = self.arc[prev, here][1]
                d = next(k for k in (1, -1) if self.starts[0, -k, lane] == prev)
                bits = 2 * mask + lane
                packet = tuple(i for i in range(4) if (bits >> i) & 1)
                return (d, packet), len(seen)
            raw = self.step(raw)
        raise ArithmeticError("did not return to hub")


def logical_return(law, letter, state):
    d, e = state
    pos, mobile, stock = (0 if d == 1 else 4), int(0 in e), set(e) - {0}
    seen = set()
    while (pos, d, mobile, tuple(sorted(stock))) not in seen:
        seen.add((pos, d, mobile, tuple(sorted(stock))))
        pos += d
        if pos in (0, 4):
            return (d, tuple(sorted(stock | ({0} if mobile else set())))), 4 * len(seen)
        if letter == "B" and pos == 1:
            continue
        out = law[4 * (d == -1) + 2 * mobile + (pos in stock)]
        d, mobile = (1 if out & 4 else -1), (out >> 1) & 1
        if out & 1:
            stock.add(pos)
        else:
            stock.discard(pos)
    raise ArithmeticError("logical circuit trapped")


@cache
def tables(a, c):
    law = inferred_rule(a, c)
    data = {}
    for letter in "FB":
        g = Petal(law, letter == "B")
        need((len(g.adj), len(g.arc)//2, len(g.cells)) == (28, 32, 3), "petal resources")
        for s in ALL_STATES:
            got = g.physical_return(*s)
            need(got == logical_return(law, letter, s), "logical/physical calendar")
            data[letter, s] = got
        need({data[letter, s][0] for s in ALL_STATES} == set(ALL_STATES), "return permutation")
    return data


def enact(data, s, word):
    calendar = []
    for letter in word:
        s, hops = data[letter, s]
        calendar.append(hops)
    return s, tuple(calendar)


def physical_word(packet, direction=1, word=WORD, a=0, c=1):
    """Actual petal on any subset of slots. Return ((direction, packet), hop calendar).

    An empty packet is a mobile with no marked lane plus blank stores, not
    removal of the travelling cursor. Binary capacity is unchanged.
    """
    packet = tuple(packet)
    if (direction, packet) not in ALL_STATES or (a, c) not in tuple(product((0, 1), repeat=2)):
        raise ValueError("need sorted distinct slots 0..3, direction +/-1 and bit-valued a,c")
    if any(letter not in "FB" for letter in word):
        raise ValueError("only full-return F and bypass-return B are implemented")
    return enact(tables(a, c), (direction, packet), word)


def bare_control(data):
    # Arbitrary words in actual full first returns F, free hub turn H and
    # mobile-mark-controlled hub turn M. No bypass, other observations or
    # conditionally selected future instruction. Even ignore final direction.
    index = STATES.index
    generators = (
        tuple(index(data["F", s][0]) for s in STATES),
        tuple(index((-d, e)) for d, e in STATES),
        tuple(index((-d if 0 in e else d, e)) for d, e in STATES),
    )
    cycles = [p for p in permutations(range(4)) if len({0,p[0],p[p[0]],p[p[p[0]]]}) == 4]
    goals = {tuple(target(e, p) for e in EDGES) for p in cycles}
    seed = tuple(index((1, e)) for e in EDGES)
    seen, todo = {seed}, deque([seed])
    while todo:
        row = todo.popleft()
        need(tuple(STATES[i][1] for i in row) not in goals, "bare complement hit")
        for gen in generators:
            new = tuple(gen[i] for i in row)
            if new not in seen:
                seen.add(new)
                todo.append(new)
    return len(seen)


def synthesize(data):
    # Closed image-tuple orbit under F and B only. An index >=6 represents
    # negative direction, so the six goals explicitly require direction reset.
    turns = [p for p in permutations(range(4)) if len({0,p[0],p[p[0]],p[p[p[0]]]}) == 4]
    goals = {bytes(EDGES.index(target(e, p)) for e in EDGES) for p in turns}
    maps = {k: bytes([STATES.index(data[k,s][0]) for s in STATES] + list(range(12,256)))
            for k in "FB"}
    seed = bytes(range(6))
    seen, todo, hits = {seed}, deque([(seed, "")]), []
    while todo:
        row, word = todo.popleft()
        if row in goals:
            hits.append(word)
        for k, table in maps.items():
            new = row.translate(table)
            if new not in seen:
                seen.add(new)
                todo.append((new, word + k))
    return len(seen), hits


def prepare_control(data):
    # Reachable *positive-direction* inputs from a single supplied seed.
    seen, todo = {(1, (0, 1))}, deque([(1, (0, 1))])
    while todo:
        s = todo.popleft()
        for k in "FB":
            new = data[k, s][0]
            if new not in seen:
                seen.add(new)
                todo.append(new)
    need({e for d, e in seen if d == 1} == set(EDGES) - {(2, 3)}, "preparation sector")


def hub_record(data, state):
    # B is an active interrogation. Both hub sides are physical; no local
    # or external clock, remote store access, or input-dependent command.
    (d, packet), _ = data["B", state]
    return (int(0 in state[1]), d, int(0 in packet))


def read_packet(data):
    # Calibration from known preparations; B plus eleven further B restores
    # the entire data and direction. This ignores changes to the reader's
    # record: logging and clearing it are NOT part of the reversible petal.
    decoder, lane_only = {}, {}
    for e in EDGES:
        state = (1, e)
        decoder[hub_record(data, state)] = e
        need(enact(data, state, "B" * 12)[0] == state, "reader did not restore packet")
        record = [int(0 in e)]
        for k in "FBF":
            state, _ = data[k, state]
            record.append(int(0 in state[1]))
        lane_only[tuple(record)] = e
    need(len(decoder) == len(lane_only) == 6, "hub cannot distinguish preparations")
    return decoder


def population(outputs):
    # For each single input e and output leg j, check the *incidence*
    # identity. Adding it over runs proves the count formula for any N.
    for e, j in product(EDGES, range(4)):
        need((j in outputs[e]) == (TURN.index(j) not in e), "single-run incidence")
    for n in range(6):
        for packet in combinations_with_replacement(EDGES, n):
            for j in range(4):
                before = sum(TURN.index(j) in e for e in packet)
                after = sum(j in outputs[e] for e in packet)
                need(after == n-before, "repeated prepared trials")


def main():
    calibrated = None
    for a, c in product((0, 1), repeat=2):
        data = tables(a, c)
        bare = bare_control(data)
        orbit, hits = synthesize(data)
        need(orbit == (24,60480,12,3456)[2*a+c], "FB orbit changed")
        need((len(hits) == 2 and hits[0] == WORD) if (a,c) == (0,1) else not hits,
             "FB synthesis controls")
        got = [enact(data, (1, e), WORD) for e in EDGES]
        matched = [out == (1, target(e)) for (out, _), e in zip(got, EDGES, strict=True)]
        need(bare == (96,32,576,1152)[2*a+c], "bare orbit changed")
        need(all(matched) == ((a,c) == (0,1)), "same-word controls")
        print(f"a={a} c={c}: {sum(matched)}/6 exact frozen word outputs; "
              f"{bare} bare six-image tuples (no target even ignoring direction); "
              f"{orbit} FB tuples, {len(hits)} direction-restoring four-cycle targets.")
        if (a,c) == (0,1):
            calibrated = data
    need(calibrated is not None, "missing replay")
    prepare_control(calibrated)
    decoder = read_packet(calibrated)
    outputs = {}
    for e, cost in zip(EDGES, HOPS, strict=True):
        (d, out), cal = enact(calibrated, (1,e), WORD)
        outputs[e] = decoder[hub_record(calibrated, (d,out))]
        need(d == 1 and sum(cal) == cost and outputs[e] == target(e), "hardware replay")
        back, revcal = enact(calibrated, (-d,out), WORD[::-1])
        need(back == (-1,e) and revcal == cal[::-1], "exact return under reversal")
        print(f"{e} -> {outputs[e]} in {sum(cal)} physical hops; calendar {cal}")
    population(outputs)
    for (d, e) in ALL_STATES:
        (_, packet), _ = physical_word(e, direction=d)
        need(len(packet) == len(e), "marks were not conserved")
        if len(e) != 2:
            # Set-complement sends weight k to 4-k. The actual petal cannot
            # be that map on these sectors, independently of final direction.
            complement = tuple(j for j in range(4) if j not in {TURN[i] for i in e})
            need(packet != complement, "complement outside the two-mark sector")
    print("Three stores, 28 vertices, 32 edges, one prepared two-bit packet, "
          "one switched bypass, 16 hub returns. One B decodes from hub lanes and side; "
          "eleven further B restore the data. FBF with lanes alone also decodes. For N prepared runs, "
          "m'[j] = N - m[inverse_turn(j)]; at fixed N, centered counts only negate and permute. "
          "Unequal path times; no coherent mixer, Born clicks or general overlapping-gate closure.")


if __name__ == "__main__":
    main()
