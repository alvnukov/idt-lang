"""Compare fresh vs one forward, nondestructively readable ternary-network preparation.

Each shared gate costs one unit once, each queried port costs one more;
one can read both ports at a tick but cannot revisit an earlier tick.
Timing/cost and nondisturbance are assumptions. The target is FIXED:
separate every pair disjoint on at least one test in the ORIGINAL menu.
Skipping its last distinguishing tick does not turn a pair into a valid leaf.

Set-valued supports are rectangular over different named reads: for a
fixed model no extra temporal constraint restricts jointly allowed answers.
This is exact for deterministic modeled flags, conservative for unknown
histories, not a general solution for persistent correlated hidden states.
Repeated reads at a tick are unnecessary: the previous answer still retains
all remaining models, and once time advances the old query is unavailable.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction as F
from functools import cache
from itertools import combinations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.probe_active_readout_panels import fixed_panel, network_design
from theory_experiments.discrimination_design import plan_design


def need(ok, message):
    if not ok:
        raise ArithmeticError(message)


def support(t, m):
    raw = t["allows"].get(m)
    return set(t["outcomes"] if raw is None else raw)


def solver(menu, times):
    models = tuple(sorted(menu["models"]))
    tests = sorted(menu["tests"], key=lambda t: t["id"])
    rows = []
    for t in tests:
        name = t["id"]
        rows.append((name, times[name], tuple((v, sum(1 << i for i, m in enumerate(models) if v in support(t, m)))
                                             for v in t["outcomes"])))
    pairs = []
    for i, j in combinations(range(len(models)), 2):
        pair = (1 << i) | (1 << j)
        last = max((tick for _, tick, outs in rows if all(mask & pair != pair for _, mask in outs)), default=None)
        if last is not None:
            pairs.append((pair, last))

    @cache
    def solve(state, now):
        obligations = [last for pair, last in pairs if state & pair == pair]
        if not obligations:
            return 0, None
        if min(obligations) < now:
            return None, None
        best = chosen = None
        for idx, (_, tick, outs) in enumerate(rows):
            if tick < now or tick > min(obligations):
                continue
            children = [state & mask for _, mask in outs if state & mask]
            if state in children:
                continue
            remaining = [solve(c, tick)[0] for c in children]
            if None in remaining:
                continue
            cost = tick-now+1+max(remaining)
            if best is None or cost < best:
                best, chosen = cost, idx
        return best, chosen

    return models, rows, pairs, solve


def fixed_exhaustive(rows, pairs):
    # Independent enumeration of all subsets that could attain the incumbent.
    # Same-tick port observations each cost one; no resetting after a read.
    cover = [sum(1 << j for j, (pair, _) in enumerate(pairs) if all(m & pair != pair for _, m in outs))
             for _, _, outs in rows]
    full = (1 << len(pairs))-1
    if not full:
        return 0, ()
    best = None
    for k in range(1, len(rows)+1):
        if best is not None and k > best[0]:
            break
        for subset in combinations(range(len(rows)), k):
            cost = k+max(rows[i][1] for i in subset)
            if best is not None and cost > best[0]:
                continue
            mask = 0
            for i in subset:
                mask |= cover[i]
            if mask == full:
                candidate = cost, tuple(rows[i][0] for i in subset)
                if best is None or candidate < best:
                    best = candidate
    need(best is not None, "full fixed panel should be feasible from start")
    return best


def tiny_oracle():
    def make(supports):
        return {"models": ["A", "B", "C"], "tests": [
            {"id": str(i), "outcomes": [0, 1], "allows": dict(zip("ABC", vals, strict=True))}
            for i, vals in enumerate(supports)]}

    def brute(menu, time, names, now, done):
        # Exhaust whole chronological decision trees including nonshrinking
        # queries. Terminal test always consults the FULL original menu.
        tests = menu["tests"]
        goal = all(not any(support(t, a).isdisjoint(support(t, b)) for t in tests) for a, b in combinations(names, 2))
        if goal:
            return 0
        best = None
        for i, t in enumerate(tests):
            tick = time[t["id"]]
            if i in done or tick < now:
                continue
            branches = [tuple(m for m in names if o in support(t, m)) for o in t["outcomes"]]
            sub = [brute(menu, time, left, tick, (*done, i)) for left in branches if left]
            if None not in sub:
                value = tick-now+1+max(sub)
                best = value if best is None else min(best, value)
        return best

    options = tuple(product(((0,), (1,), (0, 1)), repeat=3))
    total = 0
    for supports in product(options, repeat=2):
        menu = make(supports)
        for second in (1, 2):
            times = {"0": 1, "1": second}
            models, _, _, solve = solver(menu, times)
            for now in (0, 2):
                need(solve(7, now)[0] == brute(menu, times, models, now, ()), "chronological oracle disagreement")
                total += 1
    return total


def disturbing_read():
    # Countermodel: assume a qutrit state, reflection H, Born weights and
    # a binary Lüders measurement on port 0. The unobserved result destroys
    # only the coherence between port 0 and its orthogonal complement.
    def h(x):
        return tuple(F(2, 3)*sum(x)-v for v in x)
    x = (F(1), F(0), F(0))
    p = h(x)
    keep = (p[0], F(0), F(0))
    rest = (F(0), p[1], p[2])
    original = h(p)[0]**2
    dephased = h(keep)[0]**2 + h(rest)[0]**2
    need((original, dephased) == (1, F(65, 81)), "basis/read disturbance control")
    return {"unread_return_probability": "1", "unconditioned_binary_projective_read_return_probability": str(dephased)}


def probe():
    menu = network_design()
    times = {f"block{k:02d}_port{j}": 2*k for k, j in product(range(1, 10), (0, 3))}
    need({t["id"] for t in menu["tests"]} == set(times)
         and all(t["cost"] == times[t["id"]]+1 for t in menu["tests"]), "fresh panel/timing drift")
    models, rows, pairs, solve = solver(menu, times)
    full = (1 << len(models))-1
    worst, root = solve(full, 0)
    need(worst is not None and root is not None, "initial forward plan infeasible")
    paths = []
    def walk(state, now, path):
        value, idx = solve(state, now)
        need(value is not None, "selected dead end")
        if idx is None:
            need(not any(state & pair == pair for pair, _ in pairs), "missed original distinction")
            survivors = [m for i, m in enumerate(models) if state & (1 << i)]
            need("unmodeled" in survivors, "wildcard was filtered")
            paths.append({"reads": path, "survivors": survivors, "total_cost": now+len(path)})
            return
        name, tick, outs = rows[idx]
        need(tick >= now and all(n != name for n, _ in path), "rewind or repeated read")
        for outcome, mask in outs:
            if state & mask:
                walk(state & mask, tick, [*path, (name, outcome)])
    walk(full, 0, [])
    need(max(x["total_cost"] for x in paths) == worst and solve(full, 18)[0] is None, "path cost/late start")
    fixed, queries = fixed_exhaustive(rows, pairs)
    # A separate history-tree feasibility oracle for the actual panel at
    # the sharp boundary. Do not prune nonshrinking reads or consult DP.
    def within(names, now, used, limit):
        if not any(any(support(t, a).isdisjoint(support(t, b)) for t in menu["tests"])
                   for a, b in combinations(names, 2)):
            return True
        for t in menu["tests"]:
            name = t["id"]
            when = times[name]
            if name in used or when < now or when+len(used)+1 > limit:
                continue
            children = [[m for m in names if value in support(t, m)] for value in t["outcomes"]]
            if all(within(child, when, (*used, name), limit) for child in children if child):
                return True
        return False
    need(worst == fixed == 10 and not within(models, 0, (), 9) and within(models, 0, (), 10),
         "independent actual-panel feasibility at costs 9 and 10")
    candidate = {"block01_port3", "block03_port3", "block04_port3"}
    need(all(any(name in candidate and all(mask & pair != pair for _, mask in outs) for name, _, outs in rows)
             for pair, _ in pairs), "proposed 11-cost fixed triple is insufficient")
    fresh = plan_design(menu)
    need(fresh["status"] == "optimal", "fresh planner budget")
    # Models with unknown but persistent bits: margins alone cannot
    # distinguish them; a joint relation distinguishes equal vs opposite
    # outcomes on one run. No such relation is supplied for the wildcard.
    same, opposite = {(0, 0), (1, 1)}, {(0, 1), (1, 0)}
    need(same.isdisjoint(opposite) and all({z[i] for z in same} == {z[i] for z in opposite} == {0, 1}
                                          for i in (0, 1)), "persistent nuisance control")
    return {"status": "finite_cost_comparison_for_declared_nondisturbing_network_flags",
            "global_separable_pairs": len(pairs), "fresh_adaptive": fresh["worst_cost"], "fresh_fixed": fixed_panel(menu)[0],
            "one_run_adaptive": worst, "one_run_root": rows[root][0], "one_run_fixed": fixed,
            "one_run_fixed_panel": queries, "adaptive_paths": paths,
            "independent_actual_panel_feasibility": {"cost_9": False, "cost_10": True},
            "tiny_history_oracle_cases": tiny_oracle(), "projective_countermodel": disturbing_read(),
            "nuisance_boundary": "equal vs opposite two-read words have identical marginal supports; relation only "
            "available if persistence/calibration is supplied. Synthetic dark flags are not one-shot projective measurements."}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
