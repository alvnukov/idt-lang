"""First hits on finite bond-junction fixtures, under a supplied uniform-offer law.

No new motion rule: the transition graph uses the two frozen raw offer kernels.
Coordinates only construct preparations, fixtures and outward-facing gates. The
embedded chain counts active moves, not idle attempts or physical time.
Run: python3 -m scripts.probe_raw_bond_junction_rates
"""

import json
from collections import Counter, deque
from fractions import Fraction as F

if __package__:
    from .probe_bond_carrier_geometry import (
        FreeAlternatives,
        compile_lines,
        wedge_graph,
        wedge_point,
    )
    from .probe_conserved_bond_gait import link, need
else:
    from probe_bond_carrier_geometry import (
        FreeAlternatives,
        compile_lines,
        wedge_graph,
        wedge_point,
    )
    from probe_conserved_bond_gait import link, need


ARMS = ((0, -1), (0, 1), (1, -1), (1, 1))
OUTCOMES = ("0", "1", "2", "3", "jam", "trap")


def phase_a(point, axis, i, h):
    a, b, c = (point(axis, j) for j in (i, i + 2*h, i + 3*h))
    return frozenset((link(a, b), link(b, c)))


def gates(point, center, *, far=False):
    # Corridor IDs always name arcs by their side at junction zero. At the
    # antipodal junction a local positive offset occupies the negative arc.
    result = {}
    for arm, (axis, side) in enumerate(ARMS):
        h = -side if far else side
        for offset in (4, 5):
            result[phase_a(point, axis, center + h*offset, h)] = str(arm)
    need(len(result) == 8, "outward raw phase gates overlap")
    return result


def components(trans):
    """Kosaraju, yielding SCCs downstream first (including absorbing states)."""
    back = {s: [] for s in trans}
    for s, successors in trans.items():
        for t in successors:
            back[t].append(s)
    seen, finish = set(), []
    for root in trans:
        if root in seen:
            continue
        stack = [(root, False)]
        while stack:
            s, closing = stack.pop()
            if closing:
                finish.append(s)
            elif s not in seen:
                seen.add(s)
                stack.append((s, True))
                stack.extend((t, False) for t in back[s] if t not in seen)
    seen.clear()
    for root in reversed(finish):
        if root in seen:
            continue
        block, pending = [], [root]
        seen.add(root)
        while pending:
            s = pending.pop()
            block.append(s)
            for t in trans[s]:
                if t not in seen:
                    pending.append(t)
                    seen.add(t)
        yield block


def add_scaled(row, other, scale):
    for k, v in other.items():
        w = row.get(k, 0) + scale*v
        if w:
            row[k] = w
        else:
            row.pop(k, None)


def solve_block(block, trans, values):
    """Solve degree(s) v_s - sum_{internal moves} v_t = sum_{exits} v_t."""
    ix = {s: i for i, s in enumerate(block)}
    matrix, rhs = [], []
    for i, s in enumerate(block):
        coeff, mass = {i: F(len(trans[s]))}, {}
        for t, count in Counter(trans[s]).items():
            if t in ix:
                add_scaled(coeff, {ix[t]: F(1)}, -count)
            else:
                add_scaled(mass, values[t], count)
        matrix.append(coeff)
        rhs.append(mass)
    for i in range(len(block)):
        # A transient finite irreducible block yields a nonsingular M-matrix.
        pivot = matrix[i][i]
        for j in range(i+1, len(block)):
            if i in matrix[j]:
                scale = -matrix[j][i] / pivot
                add_scaled(matrix[j], matrix[i], scale)
                add_scaled(rhs[j], rhs[i], scale)
    for i in reversed(range(len(block))):
        for j, weight in matrix[i].items():
            if j != i:
                add_scaled(rhs[i], values[block[j]], -weight)
        values[block[i]] = {k: v / matrix[i][i] for k, v in rhs[i].items()}


def first_event(trans, terminals, *, trap_label=None):
    """Full measure; a recorder may label closed classes using its first hit."""
    values = {}
    cyclic, closed = 0, 0
    for block in components(trans):
        s = block[0]
        if s in terminals:
            need(len(block) == 1 and not trans[s], "terminal has transitions")
            values[s] = {terminals[s]: F(1)}
        elif not any(t in values for u in block for t in trans[u]):
            need(all(trans[u] for u in block), "unlabelled dead end")
            for u in block:
                values[u] = {"trap" if trap_label is None else trap_label(u): F(1)}
            closed += 1
        else:
            cyclic += int(len(block) > 1 or s in trans[s])
            solve_block(block, trans, values)
    # Independent substitution into the original, uncompressed, raw-move equations.
    for s, ts in trans.items():
        mass = values[s]
        need(sum(mass.values()) == 1 and all(v >= 0 for v in mass.values()), "lost mass")
        if s in terminals:
            need(mass == {terminals[s]: 1}, "bad terminal value")
        else:
            check = {}
            for t in ts:
                add_scaled(check, values[t], F(1, len(ts)))
            need(check == mass, "raw Bellman residual")
    return values, {"states": len(values), "cyclic_transient_sccs": cyclic, "trap_sccs": closed}


def recorded_trap(key):
    previous, _ = key
    return "trap" if previous is None else f"{previous}:trap"


def event_graph(rule, seeds, first, second):
    """Product with a passive first-hit recorder; it never changes either bond."""
    trans, terminal = {}, {}
    pending = deque((None, seed) for seed in seeds)
    while pending:
        key = pending.popleft()
        if key in trans:
            continue
        previous, state = key
        if previous is None and state in first:
            arm = first[state]
            if second is None:
                terminal[key], trans[key] = arm, ()
            else:
                # Passive bookkeeping only. Continue with the same raw marks.
                trans[key] = ((arm, state),)
        elif previous is not None and state in second:
            terminal[key], trans[key] = previous + ":" + second[state], ()
        else:
            trans[key] = tuple((previous, move.apply(state)) for move in rule.offers(state))
            if not trans[key]:
                terminal[key] = ("jam" if previous is None else previous + ":jam")
        pending.extend(t for t in trans[key] if t not in trans)
    return trans, terminal


def two_crossings(length):
    n = 2*length

    def point(axis, i):
        j = i % n
        return (0 if j in (0, length) else axis, j)

    graph = {}
    for axis in (0, 1):
        for i in range(n):
            ns = graph.setdefault(point(axis, i), set())
            ns.update(point(axis, i+d) for d in (-2, -1, 1, 2))
    return {v: frozenset(ns) for v, ns in graph.items()}, point


def run_fixture(graph, point, *, second=None, **fixture):
    rows = []
    inputs = [(arm, offset, phase_a(point, axis, side*offset, -side))
              for arm, (axis, side) in enumerate(ARMS) for offset in (6, 7)]
    for law, rule in (("free", FreeAlternatives(graph)), ("line", compile_lines(graph))):
        trans, terminal = event_graph(rule, [s for _, _, s in inputs], gates(point, 0), second)
        values, audit = first_event(trans, terminal, trap_label=recorded_trap)
        for arm, offset, state in inputs:
            joint = values[None, state]
            marginal = {}
            for key, v in joint.items():
                last = key.rsplit(":", 1)[-1]
                marginal[last] = marginal.get(last, 0) + v
            row = dict(fixture, input=arm, offset=offset, law=law,
                       mass=[str(marginal.get(o, 0)) for o in OUTCOMES], audit=audit)
            if second is not None:
                row["joint"] = {k: str(v) for k, v in sorted(joint.items())}
            rows.append(row)
    return rows


def multiply(a, b):
    return [[sum(x*y for x, y in zip(row, col, strict=True)) for col in zip(*b, strict=True)]
            for row in a]


def comparison(isolated):
    rows = sorted((r for r in isolated if r["law"] == "free" and r["offset"] == 6
                   and r["sizes"] == (19, 23)), key=lambda r: r["input"])
    p = [list(map(F, row["mass"][:4])) for row in rows]
    c = [[0, 1, 1, 1], [-1, 0, 1, -1], [-1, -1, 0, 1], [-1, 1, -1, 0]]
    gram, square = multiply(c, list(zip(*c))), multiply(c, c)
    for i in range(4):
        for j in range(4):
            need(gram[i][j] == 3*(i == j) and square[i][j] == -3*(i == j),
                 "supplied matrix does not have the specified square/Gram")
            need(F(c[i][j]**2, 3) == p[i][j], "supplied amplitude fails one-stage control")
    return {"supplied_C": c, "independent_reset": [list(map(str, row)) for row in multiply(p, p)],
            "supplied_coherent": [[str(F(x, 3)**2) for x in row] for row in square]}


def report():
    isolated, literal = [], []
    for sizes in ((19, 23), (20, 22)):
        def point(axis, i, sizes=sizes):
            return wedge_point(axis, i, sizes[axis])
        isolated.extend(run_fixture(wedge_graph(*sizes), point, sizes=sizes))
    for length in (14, 15):
        graph, point = two_crossings(length)
        literal.extend(run_fixture(graph, point, second=gates(point, length, far=True), length=length))
    return {"arm_order": ARMS, "outcomes": OUTCOMES, "isolated": isolated, "literal": literal,
            "comparison": comparison(isolated),
            "scope": "Finite supplied uniform choice among raw moves, conditional on an active "
                     "event when offers exist. Reachability alone fixes no branch weights; no "
                     "physical time, native amplitude, or interference inferred. Independent "
                     "reset P squared and externally supplied coherent U squared are controls, "
                     "not literal gluing. Literal rows keep both bonds and use corridor IDs at "
                     "both junctions; a bare jam precedes the first readout."}


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
