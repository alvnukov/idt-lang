"""Minimum number of one-offer toggle readings to separate a stipulated menu.

The outside-degree statistic, symmetric predicate and guard are supplied, as
are the addressed graph, offer and reliable fresh re-preparation for each bit.
An optional bypass guard *requires* a path of length at most 2 or 3, with
the offered edge ignored. Graph labels are not spatial coordinates. Relative
to this menu only, 0/1 errors means at most that many flipped toggle readings
over the entire interrogation. Unknown mechanisms can mimic every transcript.

Run: python3 -m scripts.probe_link_rule_separation [--full]
To consult the strategy: --answers '' asks for the first preparation; replace
the empty string with the observed bits in order, e.g. --answers 10. This
reports compatibility, not empirical observations or a closed-world inference.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from collections.abc import Iterable, Sequence
from functools import cache
from itertools import combinations, product
from typing import Literal, TypedDict

from scripts.probe_loopless_link_quartet import LooplessGraph

Feature = tuple[int, int, int]
Rule = tuple[str, int, int | None]


class Specimen(TypedDict):
    feature: Feature
    vertices: int
    edge_mask: int


class Leaf(TypedDict):
    kind: Literal["end"]
    signature: int | None


class Question(TypedDict):
    kind: Literal["test"]
    feature: int
    children: list[Leaf | Question]


Node = Leaf | Question


class AdaptivePlan(TypedDict):
    cost: int
    feasible_depths: list[tuple[int, bool]]
    states_checked: int
    tree: Node
    replay: dict[str, int]


class CleanPanel(TypedDict):
    cost: int
    optimal_panels: list[tuple[int, ...]]


class RobustPanel(TypedDict):
    cost: int
    panel: list[int]
    forced_triplets: list[int]
    extra_disjoint_differences: list[list[int]]


class AdaptiveLower(TypedDict):
    base_signature: int
    rival_signatures: list[int]
    lower_bound: int


class Experiment(TypedDict):
    scope: str
    out_of_menu_not_excluded: bool
    feature_order: list[str]
    observable_classes_by_size: dict[int, int]
    preparations: list[Specimen]
    aliases: dict[int, list[str]]
    fixed_clean: CleanPanel
    fixed_one_error: RobustPanel
    adaptive_clean: AdaptivePlan
    adaptive_one_error: AdaptivePlan
    adaptive_one_error_lower_certificate: AdaptiveLower


class FollowResult(TypedDict):
    status: str
    compatible_labels: list[str]
    next_feature: int | None
    next_preparation: Specimen | None
    out_of_menu_not_excluded: bool


def row(a: int, b: int) -> int:
    return 4 if a != b else 2 if a else 1


def preparations(n: int) -> dict[Feature, int]:
    """One reproducible raw mask per attainable test; offer lexicographic 01."""
    graph = LooplessGraph(n)
    incident = [
        sum(1 << i for i, e in enumerate(graph.edges) if k in e) for k in (0, 1)
    ]
    result: dict[Feature, int] = {}
    for state in range(0, graph.state_count, 2):
        a, b = ((state & m).bit_count() for m in incident)
        bypass = next((r for r in (2, 3) if graph.has_bypass(state, 0, r)), 4)
        result.setdefault(
            (row(a & 1, b & 1), row(int(a > 0), int(b > 0)), bypass), state
        )
    return result


def predict(rule: Rule, feature: Feature) -> bool:
    kind, code, radius = rule
    return bool(code & feature[0 if kind == "parity" else 1]) and (
        radius is None or feature[2] <= radius
    )


def aliases(features: Sequence[Feature]) -> dict[int, list[str]]:
    groups: dict[int, list[str]] = defaultdict(list)
    for kind, code, radius in product(("parity", "occupied"), range(8), (None, 2, 3)):
        signature = sum(
            predict((kind, code, radius), f) << i for i, f in enumerate(features)
        )
        groups[signature].append(f"{kind}:{code}:bypass={radius or 'off'}")
    return dict(sorted(groups.items()))


def decode(
    panel: Sequence[int], bits: Sequence[int], signatures: Iterable[int], errors: int
) -> list[int]:
    """Return every compatible menu class (never infer that the menu is true)."""
    if (
        len(panel) != len(bits)
        or any(b not in (0, 1) for b in bits)
        or errors not in (0, 1)
    ):
        raise ValueError("need one binary response per test and error budget 0 or 1")
    return [
        s
        for s in signatures
        if sum((s >> i & 1) != b for i, b in zip(panel, bits, strict=True)) <= errors
    ]


def fixed_plans(words: tuple[int, ...], width: int) -> tuple[CleanPanel, RobustPanel]:
    diffs = {a ^ b for a, b in combinations(words, 2)}
    for cost in range(width + 1):
        panels = []
        for p in combinations(range(width), cost):
            mask = sum(1 << i for i in p)
            if all(mask & d for d in diffs):
                panels.append(p)
        if panels:
            break
    forced = [i for i in range(width) if 1 << i in diffs]
    # Singleton differences require >=3 copies EACH; one further pair avoiding
    # all those tests requires >=3 more. Triple the clean panel for sufficiency.
    forced_mask = sum(1 << i for i in forced)
    independent = sorted(d for d in diffs if not d & forced_mask)
    if not independent:
        raise RuntimeError("no independent lower-bound certificate")
    lower = 3 * (len(forced) + 1)
    repeated = sorted(panels[0] * 3)
    if len(repeated) != lower or any(
        sum(d >> i & 1 for i in repeated) < 3 for d in diffs
    ):
        raise RuntimeError("fixed one-error lower and upper certificates do not meet")
    return {"cost": cost, "optimal_panels": panels}, {
        "cost": lower,
        "panel": repeated,
        "forced_triplets": forced,
        "extra_disjoint_differences": [
            [i for i in range(width) if d >> i & 1] for d in independent
        ],
    }


def last_answer_bound(words: tuple[int, ...]) -> AdaptiveLower:
    """An independent adversary certificate; no reliance on failed search depths.

    On the all-zero truthful path, each disjoint rival support must be hit
    twice: a rival could otherwise mimic zero with <=1 lie. If the worst cost
    were exactly 2k for k disjoint supports, every support would be hit exactly
    twice on that path. Now flip the last zero: the rival for its support
    needs just one lie (the earlier hit), giving a collision at the deadline.
    The greedy selection need not maximize k to certify this lower bound.
    """
    if 0 not in words:
        raise ValueError("zero reference class required")
    covered = 0
    rivals = []
    for r in sorted(words, key=lambda s: (s.bit_count(), s)):
        if r and not r & covered:
            rivals.append(r)
            covered |= r
    if not rivals:
        raise ValueError("at least one rival required")
    return {
        "base_signature": 0,
        "rival_signatures": rivals,
        "lower_bound": 2 * len(rivals) + 1,
    }


def adaptive(words: tuple[int, ...], width: int, errors: int) -> AdaptivePlan:
    """Exact minimax binary interrogation, restricted to the available columns."""
    full = (1 << len(words)) - 1
    masks = [
        sum(((s >> i) & 1) << j for j, s in enumerate(words)) for i in range(width)
    ]
    choices: dict[tuple[int, int, int], int] = {}

    def child(a: int, b: int, m: int) -> tuple[int, int]:
        return a & m, (b & m) | (a & ~m)

    @cache
    def possible(a: int, b: int, q: int) -> bool:
        # a has not used its error; b has none left. Disjoint because each
        # submitted class gives a deterministic response along the transcript.
        if (a | b).bit_count() <= 1:
            return True
        # In a tree padded to q questions, each a needs one clean leaf and
        # one distinct leaf per possible lie position; each b needs one.
        if (q + 1) * a.bit_count() + b.bit_count() > 1 << q:
            return False
        options = []
        for i, m in enumerate(masks):
            if not ((a | b) & m and (a | b) & ~m):
                # An uninformative test can be omitted: the common truthful
                # branch preserves (a,b), and q strictly decreases.
                continue
            kids = [child(a, b, m), child(a, b, ~m)]
            kids.sort(
                key=lambda x: q * x[0].bit_count() + x[1].bit_count(), reverse=True
            )
            weight = q * kids[0][0].bit_count() + kids[0][1].bit_count()
            if weight <= 1 << (q - 1):
                options.append((weight, i, kids))
        for _, i, kids in sorted(options):
            if all(possible(aa, bb, q - 1) for aa, bb in kids):
                choices[a, b, q] = i
                return True
        return False

    root = (full, 0) if errors else (0, full)
    checked = []
    for q in range(1, 16):
        ok = possible(*root, q)
        checked.append((q, ok))
        if ok:
            break
    else:
        raise RuntimeError("adaptive cost not established within constructive bound")

    def tree(a: int, b: int, depth: int) -> Node:
        if (a | b).bit_count() <= 1:
            return {
                "kind": "end",
                "signature": words[(a | b).bit_length() - 1] if a | b else None,
            }
        i = choices[a, b, depth]
        return {
            "kind": "test",
            "feature": i,
            "children": [
                tree(*child(a, b, m), depth - 1) for m in (~masks[i], masks[i])
            ],
        }

    strategy = tree(*root, q)
    visited = possible.cache_info().currsize
    possible.cache_clear()
    return {
        "cost": q,
        "feasible_depths": checked,
        "states_checked": visited,
        "tree": strategy,
        "replay": replay(strategy, words, errors),
    }


def replay(strategy: Node, words: tuple[int, ...], errors: int) -> dict[str, int]:
    """Follow all realizable transcripts, independently of planner-state updates."""
    counts = [0, 0]
    worst = 0
    for word in words:
        stack = [(strategy, 0, 0)]
        while stack:
            node, spent, depth = stack.pop()
            if node["kind"] == "end":
                if node["signature"] != word:
                    raise RuntimeError("a valid transcript lost its generating class")
                counts[spent] += 1
                worst = max(worst, depth)
                continue
            answer = word >> node["feature"] & 1
            stack.append((node["children"][answer], spent, depth + 1))
            if spent < errors:
                stack.append((node["children"][1 - answer], spent + 1, depth + 1))
    return {"clean": counts[0], "one_wrong": counts[1], "worst": worst}


def experiment() -> Experiment:
    samples = {n: preparations(n) for n in range(3, 7)}
    features = sorted(samples[6])
    # Both empty: parity 00. One occupied: parity 00/mixed. Neither
    # permits a bypass. With both occupied there are 3 parity x 3 bypass
    # categories. This bound applies to every finite simple graph, any size.
    bound = {(1, 1, 4), (1, 4, 4), (4, 4, 4)} | {
        (p, 2, b) for p in (1, 2, 4) for b in (2, 3, 4)
    }
    if set(features) != bound:
        raise RuntimeError("size six has not saturated the universal feature bound")
    specimens: list[Specimen] = []
    for f in features:
        n = next(n for n, sample in samples.items() if f in sample)
        specimens.append({"feature": f, "vertices": n, "edge_mask": samples[n][f]})
    groups = aliases(features)
    words = tuple(groups)
    fixed_clean, fixed_noisy = fixed_plans(words, len(features))
    lower = last_answer_bound(words)
    robust = adaptive(words, len(features), 1)
    if lower["lower_bound"] != robust["cost"]:
        raise RuntimeError(
            "last-answer lower bound and constructive strategy do not meet"
        )
    return {
        "scope": "synthetic addressed fresh graph preparations; offer 01, initially absent; "
        "edge-mask bit j denotes lexicographic unordered pair j (zero-based), and bit i "
        "of a class signature predicts the toggle on preparation i; costs count toggle "
        "bits only. Class identification conditional on submitted deterministic menu and "
        "error budget; an out-of-menu mechanism can match a returned class.",
        "out_of_menu_not_excluded": True,
        "feature_order": [
            "parity_row_bit",
            "occupied_row_bit",
            "bypass_category_2_3_or_4_for_longer_or_absent",
        ],
        "observable_classes_by_size": {
            n: len(aliases(sorted(s))) for n, s in samples.items()
        },
        "preparations": specimens,
        "aliases": groups,
        "fixed_clean": fixed_clean,
        "fixed_one_error": fixed_noisy,
        "adaptive_clean": adaptive(words, len(features), 0),
        "adaptive_one_error": robust,
        "adaptive_one_error_lower_certificate": lower,
    }


def follow(
    result: Experiment, answers: str, errors: int, *, fixed: bool
) -> FollowResult:
    """Consult a plan without treating compatibility as physical identification."""
    if errors not in (0, 1) or any(c not in "01" for c in answers):
        raise ValueError("require binary toggle readings and error budget 0 or 1")
    bits = tuple(map(int, answers))
    panel: Sequence[int]
    next_feature: int | None
    if fixed:
        plan = (
            result["fixed_one_error"]["panel"]
            if errors
            else result["fixed_clean"]["optimal_panels"][0]
        )
        if len(bits) > len(plan):
            raise ValueError("too many responses for fixed panel")
        panel = plan[: len(bits)]
        next_feature = plan[len(bits)] if len(bits) < len(plan) else None
    else:
        node = (result["adaptive_one_error"] if errors else result["adaptive_clean"])[
            "tree"
        ]
        visited = []
        for bit in bits:
            if node["kind"] == "end":
                raise ValueError("adaptive strategy has already stopped")
            visited.append(node["feature"])
            node = node["children"][bit]
        panel = visited
        next_feature = node["feature"] if node["kind"] == "test" else None
    survivors = decode(panel, bits, result["aliases"], errors)
    if not survivors:
        next_feature = None
        status = "no_compatible_submitted_class"
    elif next_feature is None:
        if len(survivors) != 1:
            raise RuntimeError("completed plan did not separate the surviving classes")
        status = "compatible_submitted_class"
    else:
        status = "awaiting_toggle"
    return {
        "status": status,
        "compatible_labels": [
            label for s in survivors for label in result["aliases"][s]
        ],
        "next_feature": next_feature,
        "next_preparation": result["preparations"][next_feature]
        if next_feature is not None
        else None,
        "out_of_menu_not_excluded": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--full", action="store_true", help="include replayable decision trees"
    )
    parser.add_argument(
        "--answers", help="follow an ordered prefix of binary toggle readings"
    )
    parser.add_argument(
        "--errors",
        type=int,
        choices=(0, 1),
        default=1,
        help="total incorrect readings allowed when following",
    )
    parser.add_argument(
        "--fixed",
        action="store_true",
        help="follow the fixed panel instead of an adaptive strategy",
    )
    args = parser.parse_args()
    result = experiment()
    if args.answers is not None:
        try:
            current = follow(result, args.answers, args.errors, fixed=args.fixed)
        except ValueError as exc:
            parser.error(str(exc))
        print(json.dumps(current, sort_keys=True))
        return
    output: dict[str, object] = dict(result)
    if not args.full:
        for key, plan in (
            ("adaptive_clean", result["adaptive_clean"]),
            ("adaptive_one_error", result["adaptive_one_error"]),
        ):
            output[key] = {k: v for k, v in plan.items() if k != "tree"}
    print(json.dumps(output, sort_keys=True))


if __name__ == "__main__":
    main()
