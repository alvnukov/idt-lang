"""Exact finite worst-case planning from submitted outcome supports and costs.

Each query uses a fresh preparation. Conditional on a fixed model, every
combination of individually allowed outcomes across the issued queries is
admitted. No shared latent nuisance, phase, likelihood or budget for acquiring
the predictions is inferred. Missing or null predictions allow all outcomes.

A leaf has NO pair with disjoint supports on any available query. This is
pairwise ambiguity, not a partition into equivalence classes. A query whose
one branch retains the whole state cannot improve a minimax optimum: a
positive cost was paid and that branch faces the identical remaining problem.
Conversely a query separating any pair necessarily shrinks all nonempty
branches. Other strict shrinkers may also be useful and are considered.

Only an optimal policy's reachable DAG is serialized. A null child indicates
an observation outside this library, not a claim about nature. State-budget
or output-cap exhaustion returns no usable partial policy or decision.
"""

from __future__ import annotations

from itertools import combinations

SCHEMA = "idt-measurement-design/1"
RESULT_SCHEMA = "idt-measurement-design-result/1"
MAX_POLICY_NODES = 2048


def _keys(x, expected):
    if type(x) is not dict or len(x) != len(expected) or set(x) != expected:
        raise ValueError(f"expected exactly {sorted(expected)}")


def _list(x, lo, hi):
    if type(x) is not list or not lo <= len(x) <= hi:
        raise ValueError(f"expected list of length {lo}..{hi}")
    return x


def _integer(x, lo, hi):
    if type(x) is not int or not lo <= x <= hi:
        raise ValueError(f"expected integer in {lo}..{hi}")
    return x


def _label(x):
    if type(x) is not str or not 1 <= len(x) <= 64 or not x.isascii() or not x.isprintable() or x != x.strip():
        raise ValueError("expected nonempty bounded printable ASCII label with no outer whitespace")
    return x


def _labels(xs, lo, hi):
    labels = tuple(sorted(_label(x) for x in _list(xs, lo, hi)))
    if len(set(labels)) != len(labels):
        raise ValueError("duplicate identifier or outcome")
    return labels


def _validated(spec):
    _keys(spec, {"schema", "models", "tests"})
    if type(spec["schema"]) is not str or spec["schema"] != SCHEMA:
        raise ValueError("unsupported design schema")
    models = _labels(spec["models"], 1, 16)
    menu = []
    ids = set()
    for test in _list(spec["tests"], 0, 24):
        _keys(test, {"id", "cost", "outcomes", "allows"})
        name = _label(test["id"])
        if name in ids:
            raise ValueError("duplicate test id")
        ids.add(name)
        cost = _integer(test["cost"], 1, 10**9)
        outcomes = _labels(test["outcomes"], 2, 4)
        allows = test["allows"]
        if type(allows) is not dict or len(allows) > len(models) or any(_label(m) not in models for m in allows):
            raise ValueError("allows must contain only submitted model IDs")
        masks = dict.fromkeys(outcomes, 0)
        for i, model in enumerate(models):
            raw = allows.get(model)
            choices = outcomes if raw is None else _labels(raw, 1, len(outcomes))
            for outcome in choices:
                if outcome not in masks:
                    raise ValueError("undeclared outcome")
                masks[outcome] |= 1 << i
        menu.append((name, cost, tuple(masks.items())))
    return models, tuple(sorted(menu))


class _CapReached(Exception):
    pass


def plan_design(spec: object, *, state_budget: int = 20000) -> dict[str, object]:
    """Return an exact minimum worst-case additional acquisition cost, or abstain."""
    _integer(state_budget, 0, 65535)
    models, tests = _validated(spec)
    n = len(models)
    full = (1 << n)-1
    separable = [0]*n
    ambiguous = []
    for i, j in combinations(range(n), 2):
        pair = (1 << i) | (1 << j)
        if any(all(mask & pair != pair for _, mask in branches) for _, _, branches in tests):
            separable[j] |= 1 << i
        else:
            ambiguous.append([models[i], models[j]])

    solved = {}
    visited = 0

    def solve(state):
        nonlocal visited
        if state in solved:
            return solved[state][0]
        if visited >= state_budget:
            raise _CapReached("state_budget")
        visited += 1
        if not any(state & (1 << j) and state & lower for j, lower in enumerate(separable)):
            solved[state] = (0, None)
            return 0
        best = chosen = None
        for k, (_, cost, outcomes) in enumerate(tests):  # lexical test id tie-break
            if best is not None and cost >= best:
                continue
            branches = tuple(mask & state for _, mask in outcomes)
            if state in branches:
                continue
            worst = 0
            for child in branches:
                if child:
                    worst = max(worst, solve(child))
                    if best is not None and cost+worst >= best:
                        break
            else:
                best, chosen = cost+worst, k
        if best is None:
            raise ArithmeticError("a robustly separable pair must supply a strict-shrinking query")
        solved[state] = (best, chosen)
        return best

    def key(mask):
        return f"s{mask:x}"

    def result(status, reason, worst, root, nodes):
        return {"schema": RESULT_SCHEMA, "status": status, "models": list(models), "worst_cost": worst,
                "root": root, "nodes": nodes, "unseparable_pairs": ambiguous, "states_examined": visited,
                "state_budget": state_budget, "stop_reason": reason}

    try:
        worst = solve(full)
        selected = {}
        todo = [full]
        while todo:
            state = todo.pop()
            if key(state) in selected:
                continue
            if len(selected) >= MAX_POLICY_NODES:
                raise _CapReached("policy_node_limit")
            remaining, k = solved[state]
            children = {}
            if k is not None:
                for label, mask in tests[k][2]:
                    child = mask & state
                    children[label] = key(child) if child else None
                    if child:
                        todo.append(child)
            selected[key(state)] = {"survivors": [m for i, m in enumerate(models) if state & (1 << i)],
                                    "test": None if k is None else tests[k][0], "children": children,
                                    "worst_cost": remaining}
    except _CapReached as exc:
        return result("budget_exhausted", str(exc), None, None, {})
    return result("optimal", "exact_minimax", worst, key(full), selected)
