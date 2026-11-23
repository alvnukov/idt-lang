"""First observations, rather than eventual reachability, on the frozen open path.

Integer labels denote raw bit configurations. No probabilities are assigned to
the optional contact offers. Run: python3 -m scripts.probe_staggered_next_event
"""

import argparse
import json
from collections import deque
from itertools import product

BOOK = ((1, 0, 2), (1, 0, 3))  # T, a, b at A and B
TRIPLES = (((0, 1, 3), (1, 2, 3)),
           ((0, 1, 4), (0, 4, 5), (2, 3, 5), (2, 4, 5)))
NATIVE = {"aa": "bb", "bb": "aa", "Ta": "aT", "aT": "Ta"}


def offer(x, mask):
    return x ^ mask if x & mask in (0, mask) else x


def native_next(word):
    return {word[:i] + NATIVE[word[i:i+2]] + word[i+2:]
            for i in range(len(word)-1) if word[i:i+2] in NATIVE}


def backtrack(parent, end):
    path = []
    while end is not None:
        path.append(end)
        end = parent[end]
    return path[::-1]


class Path:
    def __init__(self, n, phase):
        if n < 2 or phase not in (0, 1):
            raise ValueError("open alternating path of length >= 2 required")
        self.n, self.phase = n, phase
        self.moves = tuple(self.mask(e, tri) for e in range(n-1)
                           for tri in TRIPLES[(phase+e) % 2])
        self._clean = None

    def mask(self, edge, triple):
        # Slots on a bare AB edge need no actual helper bits.
        slots = (*range(2*edge, 2*edge+4), 2*self.n+2*edge, 2*self.n+2*edge+1)
        return sum(1 << slots[k] for k in triple)

    def encode(self, word):
        if len(word) != self.n:
            raise ValueError("wrong word length")
        return sum(BOOK[(i+self.phase) % 2]["Tab".index(t)] << (2*i)
                   for i, t in enumerate(word))

    @property
    def clean(self):
        if self._clean is None:
            self._clean = {self.encode(w): "".join(w) for w in product("Tab", repeat=self.n)}
        return self._clean

    def neighbors(self, x):
        return [x ^ m for m in self.moves if x & m in (0, m)]

    def first(self, start):
        """Shortest representatives of all different first clean observations."""
        if start not in self.clean:
            raise ValueError("start must be clean")
        parent, q, ends = {start: None}, deque([start]), {}
        while q:
            x = q.popleft()
            for y in self.neighbors(x):
                if y in parent:
                    continue
                parent[y] = x
                if y in self.clean:
                    ends[self.clean[y]] = backtrack(parent, y)
                else:
                    q.append(y)
        return ends

    def bypass(self, site):
        if not 0 < site < self.n-1:
            raise ValueError("the tested barrier must be interior")
        start = self.encode("T" + "a"*(self.n-1))
        end = self.encode("a"*(self.n-1) + "T")
        parent, q = {start: None}, deque([start])
        while q:
            x = q.popleft()
            if x == end:
                return backtrack(parent, end)
            for y in self.neighbors(x):
                if y not in parent and (y >> (2*site)) & 3 != 1:
                    parent[y] = x
                    q.append(y)
        return None


def event_audit(n, phase):
    g = Path(n, phase)
    missing = extras = total = 0
    best = None
    for x, word in g.clean.items():
        nexts, native = g.first(x), native_next(word)
        missing += len(native - nexts.keys())
        extras += len(nexts.keys() - native)
        total += len(nexts)
        for w in nexts.keys() - native:
            candidate = (len(nexts[w])-1, word, w, nexts[w])
            if best is None or candidate < best:
                best = candidate
    return dict(n=n, phase=phase, different_first_directed=total, missing_directed=missing,
                extra_directed=extras, shortest_extra=best)


def source_twins(g):
    """Use the same offered masks. An unobserved BA helper stores the difference."""
    if g.phase != 1 or g.n < 3:
        raise ValueError("emission requires a BA bond followed by an onward edge")
    moves = [g.mask(0, (2, 4, 5))]
    for e in range(1, g.n-1):
        # The two literal Ta->aT moves of each local generator path.
        route = ((1, 2, 3), (0, 1, 3)) if (e+1) % 2 == 0 else ((2, 4, 5), (0, 4, 5))
        moves.extend(g.mask(e, t) for t in route)
    signal, background = [g.encode("aT" + "a"*(g.n-2))], [0]
    for m in moves:
        signal.append(offer(signal[-1], m))
        background.append(offer(background[-1], m))
    return signal, background, moves


def experiment():
    trials = [event_audit(n, p) for n in (2, 3, 4, 5) for p in (0, 1)]
    bypasses = [
        (n, p, j, Path(n, p).bypass(j))
        for n in (3, 4, 5) for p in (0, 1) for j in range(1, n-1)
    ]
    twins = []
    for n in (3, 4, 7, 12):
        s, b, moves = source_twins(Path(n, 1))
        helpers = 3 << (2*n)
        visible = ~(helpers | (3 << 2))
        twins.append(dict(n=n, offers=len(moves), same_exterior_history=all(
            (x & visible) == (y & visible) for x, y in zip(s, b)),
            final_difference=s[-1] ^ b[-1], compensated_helper=helpers))
    return dict(first_events=trials, bypasses=bypasses, source_twins=twins,
                boundary="Support, not rates. A local pass need not certify where a mark originated.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    print(json.dumps(experiment(), indent=None if args.json else 2, sort_keys=True))
