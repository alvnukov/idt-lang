"""Can one shared bit and four independently addressed cells produce the short echoes?

Supply four comparable ports, a persistent mark on a *full configuration*,
and one identical involution G on (shuttle bit, addressed cell). Every other
cell is untouched. No path relation or endpoint oracle enters the update.

There is a useful all-configuration rigidity argument. Write the update as
G(h,x)=(t(h,x), f_h(x)). Comparing the cell touched first in abc with that
same cell touched last in cba gives f_h(x)=f_{t(t(h,z),y)}(x) for all
h,x,y,z, since the three cells can be initialized independently.

* If f_0=f_1=f, reciprocity gives f²=id. Each t(-,x) permutes the bit,
  and t(-,f(x)) is its inverse. Bit permutations commute; the cell
  updates on disjoint slots commute too. Hence abab closes.
* Otherwise every two-step role walk returns to its starting bit. A bit h
  cannot have both possible successors: if it did, the successor h would
  itself have to send every input to h, a contradiction. The deterministic
  role map therefore squares to the identity. If it fixes both bits, the
  different ports commute again. If it swaps them, G alternates some cell
  permutation f with its inverse. Conversely all three cases give abc=cba.

In the alternating case, traversals apply f on odd steps from role 0 and
its inverse on even steps. A cell cycle of length 1, 2 or 3 supplies an
all-equal initialization on which (ab)^length closes too soon or gives the
wrong six-tick echo. If all cycles have length >=4, no nonzero signed visit
count can wrap on an even word of length <=6 (each sign occurs <=3 times).
The census checks raw gate tables, *including roots of globally bad rules*.

These are configuration orbits, not physical sites established by a detector.
The known 64-site relay identifies additional states; it does not read these
four independent cell values and the shuttle bit as a full configuration.
Short-word agreement of a finite machine does not establish spatial dimension,
unbounded counters, an observer, or physics. The argument is not a Lean proof.
"""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Iterator
from dataclasses import asdict, dataclass
from itertools import pairwise, permutations, product

Word = tuple[int, ...]
Gate = tuple[int, ...]
Ports = tuple[tuple[int, ...], ...]
PORTS = tuple(range(4))
TRIPLES = tuple(permutations(PORTS, 3))
TWO_PORT = tuple((a, b) * 3 for a, b in permutations(PORTS, 2))


def need(ok: bool, msg: str) -> None:
    if not ok:
        raise ArithmeticError(msg)


def words(n: int) -> Iterator[Word]:
    return (w for w in product(PORTS, repeat=n) if all(a != b for a, b in pairwise(w)))


# For reduced paths of length at most three, the expected coincidences are
# identities plus reversal of each length-three path. Splitting a word in two
# tests every return up through tick six, including odd and shorter words.
PREFIXES = tuple(
    (w, min(w, w[::-1]) if n == 3 else w) for n in range(4) for w in words(n)
)


def tables(q: int, gate: Gate) -> Ports:
    """Index a bit and four symbols; a port can only change its own pair."""
    size = q**4

    def step(s: int, stride: int) -> int:
        h, cells = divmod(s, size)
        x = cells // stride % q
        k, y = divmod(gate[h * q + x], q)
        return k * size + cells + (y - x) * stride

    return tuple(tuple(step(s, q**p) for s in range(2 * size)) for p in PORTS)


def walk(ports: Ports, start: int, word: Word) -> int:
    for p in word:
        start = ports[p][start]
    return start


def exact_ball(ports: Ports, root: int) -> bool:
    key_for_site: dict[int, Word] = {}
    site_for_key: dict[Word, int] = {}
    for w, key in PREFIXES:
        end = walk(ports, root, w)
        if (
            key_for_site.setdefault(end, key) != key
            or site_for_key.setdefault(key, end) != end
        ):
            return False
    return True


def root_tests(ports: Ports, root: int) -> tuple[bool, bool, bool]:
    triple = all(walk(ports, root, w) == walk(ports, root, w[::-1]) for w in TRIPLES)
    pair = triple and all(walk(ports, root, w) != root for w in TWO_PORT)
    return triple, pair, pair and exact_ball(ports, root)


def root_classes(q: int) -> tuple[int, ...]:
    # Port relabeling is exact: the same gate acts on *any* selected cell;
    # neither words nor checks distinguish names. Restore all root multiplicities.
    size = q**4
    return tuple(
        (s // size) * size
        + sum(x * q**p for p, x in enumerate(sorted(s // q**p % q for p in PORTS)))
        for s in range(2 * size)
    )


def components(ports: Ports) -> Iterator[set[int]]:
    unseen = set(range(len(ports[0])))
    while unseen:
        root = unseen.pop()
        todo, found = [root], {root}
        while todo:
            s = todo.pop()
            for t in ports:
                end = t[s]
                if end in unseen:
                    unseen.remove(end)
                    found.add(end)
                    todo.append(end)
        yield found


def gate_type(q: int, gate: Gate) -> str:
    f = tuple(s % q for s in gate)
    if f[:q] == f[q:] or all(gate[s] // q == s // q for s in range(2 * q)):
        return "commuting"
    if all(gate[s] // q != s // q for s in range(2 * q)):
        return "alternating"
    return "other"


def cycle_lengths(f: Gate) -> tuple[int, ...]:
    todo, lengths = set(range(len(f))), []
    while todo:
        x = min(todo)
        length = 0
        while x in todo:
            todo.remove(x)
            length += 1
            x = f[x]
        lengths.append(length)
    return tuple(sorted(lengths))


@dataclass
class Census:
    gates: int = 0
    triple_everywhere: int = 0
    commuting: int = 0
    alternating_noncommuting: int = 0
    nominated_everywhere: int = 0
    nominated_somewhere: int = 0
    nominated_root_instances: int = 0
    full_everywhere: int = 0
    full_somewhere: int = 0
    full_root_instances: int = 0
    full_components: int = 0
    full_component_gates: int = 0


def renamed(q: int, gate: Gate, names: Gate) -> Gate:
    change = tuple(h * q + names[x] for h, x in product(range(2), range(q)))
    return tuple(change[gate[change.index(s)]] for s in range(2 * q))


def census(q: int) -> Census:
    report, classes = Census(), root_classes(q)
    mult = Counter(classes)
    full_rules: set[Gate] = set()
    for gate in permutations(range(2 * q)):
        if any(gate[y] != x for x, y in enumerate(gate)):
            continue
        report.gates += 1
        ports = tables(q, gate)
        outcomes = {root: root_tests(ports, root) for root in mult}
        n_triple, n_pair, n_full = (
            sum(mult[r] for r, outcome in outcomes.items() if outcome[i])
            for i in range(3)
        )
        total = len(classes)
        kind = gate_type(q, gate)
        global_triple = n_triple == total
        need(global_triple == (kind != "other"), "global role classification")
        # Under a commuting gate every (ab)^2 fixes every state. Conversely
        # the two even-odd updates differ somewhere for a non-involutive f.
        commute = all(
            walk(ports, r, (0, 1)) == walk(ports, r, (1, 0)) for r in range(total)
        )
        need(commute == (kind == "commuting"), "commuting/factor classification")
        report.triple_everywhere += global_triple
        report.commuting += commute
        report.alternating_noncommuting += kind == "alternating"
        report.nominated_everywhere += n_pair == total
        report.nominated_somewhere += n_pair > 0
        report.nominated_root_instances += n_pair
        report.full_everywhere += n_full == total
        if n_full == total:
            full_rules.add(gate)
        report.full_somewhere += n_full > 0
        report.full_root_instances += n_full
        predicted = (
            kind == "alternating"
            and min(cycle_lengths(tuple(v % q for v in gate[:q]))) >= 4
        )
        need(predicted == (n_full == total), "all-origin minimal-cycle prediction")
        if n_full:
            clean = {s for s, r in enumerate(classes) if outcomes[r][2]}
            good_components = [part for part in components(ports) if part <= clean]
            report.full_components += len(good_components)
            report.full_component_gates += bool(good_components)
    if q == 4:
        need(
            full_rules == {renamed(q, ring(q), p) for p in permutations(range(q))},
            "all full rules are the same gate up to renaming cell symbols",
        )
    return report


def ring(q: int) -> Gate:
    return tuple(q + (x + 1) % q for x in range(q)) + tuple(
        (x - 1) % q for x in range(q)
    )


def controls(q: int) -> dict[str, object]:
    ports = tables(q, ring(q))
    need(all(t[t[r]] == r for t in ports for r in range(len(t))), "local backtracking")
    returns = [{w for w in words(n) if walk(ports, 0, w) == 0} for n in range(1, 7)]
    expected = {w + w for w in TRIPLES}
    need(
        (not any(returns[:-1]) and returns[-1] == expected) == exact_ball(ports, 0),
        "independent literal word check",
    )
    sizes = sorted(len(part) for part in components(ports))
    # Even two-step walks increment any cell and decrement any other, so they
    # generate the zero-sum subgroup of (Z/q)^4; odd walks reach the other role.
    need(sizes == [2 * q**3] * q, "actual connected configuration counts")
    return {
        "component_sizes": sizes,
        "root_returns_ticks_1_to_6": [len(s) for s in returns],
    }


def moved_mark() -> dict[str, object]:
    # Full census witness, not a fitted rule: the symmetric initialization
    # passes the entire return test. Re-marking after just one move refutes it.
    gate = (0, 1, 4, 6, 2, 7, 3, 5)
    ports = tables(4, gate)
    root = 4**4 + sum(2 * 4**p for p in PORTS)  # bit 1, cells (2,2,2,2)
    neighbor = ports[0][root]
    witness = (1, 2, 1, 2, 1)
    expected = {w + w for w in TRIPLES}
    need(
        all(
            (walk(ports, root, w) == root) == (w in expected)
            for n in range(1, 7)
            for w in words(n)
        ),
        "literal false-positive mark",
    )
    need(
        walk(ports, neighbor, witness) == neighbor and not exact_ball(ports, neighbor),
        "five-tick echo from adjacent mark",
    )
    size = next(len(part) for part in components(ports) if root in part)
    need(size == 105, "false-positive orbit size")
    return {
        "gate": gate,
        "component_size": size,
        "remark_via_port": 0,
        "forbidden_echo": witness,
    }


def main() -> None:
    q_values = (1, 2, 3, 4)
    results = [census(q) for q in q_values]
    need([r.gates for r in results] == [2, 10, 76, 764], "involution enumeration")
    need([r.triple_everywhere for r in results] == [2, 8, 34, 180], "triple census")
    need(
        [r.full_everywhere for r in results] == [0, 0, 0, 6],
        "minimum all-configuration alphabet",
    )
    need(
        [r.full_somewhere for r in results] == [0, 0, 0, 102]
        and results[-1].full_root_instances == 3216,
        "best-mark and all-mark outcomes differ",
    )
    need(
        [r.full_component_gates for r in results] == [0, 0, 0, 6]
        and results[-1].full_components == 24,
        "entire components were tested",
    )
    # Strictly disjoint support: no shared bit changes, every selected bit
    # flips. The nominated protocols pass everywhere, but abab closes too.
    independent = tables(2, (1, 0, 3, 2))
    need(
        all(
            root_tests(independent, r) == (True, True, False)
            and walk(independent, r, (0, 1) * 2) == r
            for r in range(32)
        ),
        "four-tick echo from independent toggles",
    )
    # A bit exchanged with the selected bit is reciprocal and shared, but a
    # product of two distinct slot swaps is a 3-cycle, so ababab always closes.
    swap = tables(2, (0, 2, 1, 3))
    need(
        all(walk(swap, r, w) == r for w in TWO_PORT for r in range(32)), "swap control"
    )
    need(
        any(walk(swap, r, (0, 1, 2) * 2) != r for r in range(32)),
        "swap triple contrast",
    )
    print(
        json.dumps(
            {
                "census_by_cell_size": {
                    q: asdict(r) for q, r in zip(q_values, results, strict=True)
                },
                "single_cycle_controls": {q: controls(q) for q in q_values},
                "moved_mark_control": moved_mark(),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
