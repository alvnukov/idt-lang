"""Anonymous tree refinement does not alone erase branch or origin records.

Use a complete unordered rooted ternary tree cut at height h. Names in
this finite verifier are only for enumerating permutations and records.
A signed node expands to the sum of its actual descendant leaves. The
parent/three-children identity then holds in the free integer group on
cut leaves, with no assigned amplitudes. Three unrelated leaves at the
same depth need not be the three children of any parent.

For a leaf-permutation group, fixed vectors have one orbit SUM as a
basis element per orbit. Passing to the trivial-action quotient instead
identifies each orbit's leaves. The natural map sends each orbit sum to
|orbit| times its basic class. Here the unmarked root sum maps to 3^h
times one leaf class; the invariant space never supplies an integral
uniform representative of that class. Declaring these two constructions
equivalent or treating normalized averaging as an integer operation
would silently add an instrument.

The extra discriminators are sibling reunion, spectator-preserving local
exchange, and a shared cross-origin null. They need comparable prepared
marks, a retained parent/arrival record or an explicit common subtractor.
No experimental, physical-carrier, or amplitude-readout claim follows.
"""

from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product

ARMS = range(3)
Word = tuple[int, ...]


def need(condition, reason):
    if not condition:
        raise ArithmeticError(reason)


def nodes(depth):
    return tuple(product(ARMS, repeat=depth))


def ancestor(x, y):
    return next(
        (i for i, (a, b) in enumerate(zip(x, y, strict=False)) if a != b),
        min(len(x), len(y)),
    )


def children(w):
    return tuple((*w, i) for i in ARMS)


def leaf_record(height, signed_nodes):
    return tuple(
        sum(s for w, s in signed_nodes if z[: len(w)] == w) for z in nodes(height)
    )


def by_orbit(record, classes, rank):
    return tuple(
        sum(x for x, a in zip(record, classes, strict=True) if a == i)
        for i in range(rank)
    )


def act(word, local_perms):
    return tuple(local_perms[word[:i]][k] for i, k in enumerate(word))


def all_automorphisms(height):
    need(0 <= height <= 2, "full group enumeration deliberately bounded")
    internals = tuple(x for i in range(height) for x in nodes(i))
    for local in product(tuple(permutations(ARMS)), repeat=len(internals)):
        perm = dict(zip(internals, local, strict=True))
        yield tuple(act(x, perm) for x in nodes(height))


def group_controls():
    leaves = nodes(2)
    position = {x: i for i, x in enumerate(leaves)}
    group = tuple(all_automorphisms(2))
    need(
        len(group) == len(set(group)) == 1296,
        "wrong ternary wreath-product action inventory",
    )
    point = leaves[0]
    stabilizer = tuple(p for p in group if p[0] == point)
    need(
        len(stabilizer) == 144 and len({p[0] for p in group}) == 9,
        "point action not transitive",
    )
    mins = {}
    for p in group:
        moved = sum(a != b for a, b in zip(leaves, p, strict=True))
        for x, y in zip(leaves, p, strict=True):
            mins[x, y] = min(moved, mins.get((x, y), len(leaves)))
        need(
            all(
                ancestor(a, b) == ancestor(p[position[a]], p[position[b]])
                for a, b in combinations(leaves, 2)
            ),
            "unrooted permutation admitted as tree automorphism",
        )
    for x in leaves:
        orbit = {p[position[x]] for p in stabilizer}
        need(
            orbit == {y for y in leaves if ancestor(point, x) == ancestor(point, y)},
            "wrong marked stabilizer orbit",
        )
        for y in leaves:
            if x != y:
                need(
                    mins[x, y] == 2 * 3 ** (1 - ancestor(x, y)),
                    "least exchange support violated",
                )
    return {
        "height_two_automorphisms": len(group),
        "observer_leaf_stabilizer": len(stabilizer),
        "height_two_min_moved_leaves_sibling_vs_nonsibling": [
            mins[(0, 0), (0, 1)],
            mins[(0, 0), (1, 0)],
        ],
    }


def minimum_exchange(x, y, z):
    """Swap the two divergent subtrees, with inverse suffix relabelings."""
    level = ancestor(x, y)
    need(level < len(x), "exchange requires distinct leaves")
    left, right = x[: level + 1], y[: level + 1]
    if z[: level + 1] == left:
        prefix = right
    elif z[: level + 1] == right:
        prefix = left
    else:
        return z
    suffix = tuple(
        b if i == a else a if i == b else i
        for i, a, b in zip(z[level + 1 :], x[level + 1 :], y[level + 1 :], strict=True)
    )
    return (*prefix, *suffix)


def orbit_and_exchange_relations():
    data = {}
    for h in range(1, 5):
        cut = nodes(h)
        mark = (0,) * h
        classes = tuple(ancestor(x, mark) for x in cut)
        class_sizes = tuple(classes.count(i) for i in range(h + 1))
        need(
            class_sizes == (*(2 * 3 ** (h - i - 1) for i in range(h)), 1),
            "wrong orbit cardinalities",
        )
        root_record = leaf_record(h, (((), 1),))
        need(sum(root_record) == 3**h, "unexpected rank-one inclusion")
        for i in range(h + 1):
            orb_sum = tuple(int(j == i) for j in classes)
            need(
                by_orbit(orb_sum, classes, h + 1)
                == tuple(int(j == i) * class_sizes[i] for j in range(h + 1)),
                "invariants/coinvariant index",
            )

        for j, x in enumerate(cut):
            for k in range(j + 1, len(cut)):
                y = cut[k]
                if classes[j] == classes[k]:
                    need(
                        minimum_exchange(x, y, mark) == mark
                        and minimum_exchange(x, y, x) == y,
                        "constructed equivalence disturbs marked history",
                    )

        witness = []
        for i in range(h):
            on = (0,) * (i + 1)
            off = (*on[:-1], 1)
            expected = by_orbit(leaf_record(h, ((off, 2), (on, -2))), classes, h + 1)
            discrepancy = leaf_record(h, ((on[:-1], 1), (on, -3)))
            actual = by_orbit(discrepancy, classes, h + 1)
            need(
                actual == expected and any(actual) and not sum(actual),
                "marked child was equated to two side children",
            )
            witness.append(actual)
            p = minimum_exchange(mark, (*off, *((0,) * (h - i - 1))), cut[0])
            need(p[: i + 1] == off, "minimizer did not exchange selected leaf")

        for a, b in ((mark, (1,) * h), (mark, (*mark[:-1], 1))):
            perm = tuple(minimum_exchange(a, b, z) for z in cut)
            need(
                len(set(perm)) == len(cut)
                and sum(x != y for x, y in zip(cut, perm, strict=True))
                == 2 * 3 ** (h - ancestor(a, b) - 1),
                "incorrect exact subtree support",
            )
            need(
                all(
                    ancestor(cut[i], cut[j]) == ancestor(perm[i], perm[j])
                    for i, j in combinations(range(len(cut)), 2)
                ),
                "explicit exchange is not a tree automorphism",
            )
        data[h] = {
            "root_to_unmarked_leaf_units": sum(root_record),
            "marked_observer_coinvariant_rank": h + 1,
            "marked_per_orbit_inclusion_factors": class_sizes,
            "marked_parent_minus_three_path_children": witness,
        }

    x, y, spectator = (0, 0), (1, 0), (0, 1)
    moved = minimum_exchange(x, y, spectator)
    need(
        moved != spectator and ancestor(x, spectator) == ancestor(y, moved),
        "coherent subtree move should preserve spectator relation",
    )
    need(
        ancestor(x, spectator) == 1 and ancestor(y, spectator) == 0,
        "fixed spectator does not notice false standalone exchange",
    )
    return {
        "height_examples": data,
        "fixed_spectator_meeting_depth_before_after_illegal_single_exchange": [1, 0],
    }


def branch_contact_observable():
    height = 2
    p = (0,)
    all_leaves = nodes(height)
    hist = Counter()
    for triple in combinations(all_leaves, 3):
        sibling_pairs = sum(a[:-1] == b[:-1] for a, b in combinations(triple, 2))
        hist[sibling_pairs] += 1
        word = tuple((w, 1) for w in triple) + ((p, -1),)
        record = leaf_record(height, word)
        need(
            (not any(record)) == (set(triple) == set(children(p))) and not sum(record),
            "null relation or depth quotient",
        )
    need(hist == {3: 3, 1: 54, 0: 27}, "incorrect symmetric sibling comparator counts")
    mixed = ((0, 0), (0, 1), (1, 0))
    m = leaf_record(height, (*((x, 1) for x in mixed), (p, -1)))
    need(
        {x: a for x, a in zip(all_leaves, m, strict=True) if a}
        == {(0, 2): -1, (1, 0): 1},
        "wrong signed mixed-branch residual",
    )
    same_leaf_repeated = leaf_record(1, (((0,), 3), ((), -1)))
    need(
        same_leaf_repeated == (2, -1, -1) and not sum(same_leaf_repeated),
        "co-located multiplicity control",
    )
    return {
        "distinct_depth_two_triples": sum(hist.values()),
        "counts_by_number_of_sibling_pairs": dict(sorted(hist.items())),
        "nulls_against_one_retained_parent_in_leaf_record": 1,
        "nulls_against_that_parent_if_all_equal_depth_leaves_are_identified": 84,
        "depth_one_three_marks_on_same_leaf_minus_parent": same_leaf_repeated,
        "mixed_signed_residual_nonzero_and_net_zero": True,
        "symmetric_instrument": "compare first parent reunions of three leaves; no names or chosen sibling ordering",
    }


def compatible_cuts():
    rows = []
    for h in range(5):
        cut = nodes(h)
        root = leaf_record(h, (((), 1),))
        deeper_root = leaf_record(h + 1, (((), 1),))
        expand = tuple(a for a in root for _ in ARMS)
        need(
            expand == deeper_root and sum(expand) == 3 * sum(root),
            "root fixed, quotient generator triple",
        )
        for w in cut:
            a = leaf_record(h, ((w, 1),))
            b = leaf_record(h + 1, ((w, 1),))
            c = leaf_record(h + 1, tuple((child, 1) for child in children(w)))
            need(
                b == c == tuple(x for x in a for _ in ARMS) and sum(b) == 3,
                "leaf refinement is not an actual disjoint partition",
            )
        rows.append(
            {
                "from_cut": h,
                "unmarked_invariant_root_sum_to_next_root_sum_coefficient": 1,
                "unmarked_coinvariant_generator_to_next_leaf_coefficient": 3,
            }
        )
    return {
        "cut_maps": rows,
        "coherent_all_depths_fixed_orbit_sum_direct_limit": "Z",
        "coherent_all_depths_leaf_coinvariant_direct_limit": "Z[1/3] only after erasing ancestry at every cut",
        "external_root_unit_chart": "[n leaves at cut h] -> n/3^h; this chart is not an operation on the anonymous tree",
        "finite_quotient_boundary": "nonzero moduli coprime to 3 also respect every depth relation; any prescribed finite set of nonzero rational scores can survive reduction modulo a sufficiently large prime not equal to 3",
    }


def origin_registration():
    h = 2
    # Two source identities are retained; use first/second copies as a
    # bookkeeping device, not as an assumption of calibrated addresses.
    a = leaf_record(h, (((), 1),))
    b = leaf_record(h, (((), -1),))
    raw_difference = (*a, *b)
    separate_classes = (0,) * len(a) + (1,) * len(b)
    separated = by_orbit(raw_difference, separate_classes, 2)
    merged = by_orbit(raw_difference, (0,) * len(raw_difference), 1)
    need(
        separated == (9, -9) and merged == (0,),
        "local identity vs supplied whole-source exchange quotient",
    )

    # Hold A root as the unit. Theta is B root/A root in an EXTERNAL
    # common null comparator; neither the trees nor the local laws use it.
    # Same-depth and offset cases have no amplitude prediction otherwise.
    alternatives = {}
    offsets = ((0, 0), (0, 1), (1, 0))

    def calibrated_difference(theta, da, db):
        return F(1, 3**da) - theta * F(1, 3**db)

    for theta in (F(1), F(3), F(1, 3), F(2)):
        residual = tuple(calibrated_difference(theta, a, b) for a, b in offsets)
        need(
            all(
                (r == 0) == (theta == F(3) ** (b - a))
                for r, (a, b) in zip(residual, offsets, strict=True)
            ),
            "null did not bind exact relative root scale",
        )
        need(
            all(
                calibrated_difference(theta, a + 1, b + 1) == r / 3
                for r, (a, b) in zip(residual, offsets, strict=True)
            ),
            "synchronized refinement changed relation",
        )
        alternatives[str(theta)] = tuple(map(str, residual))
    need(
        len(set(alternatives.values())) == len(alternatives),
        "registered bridge control not separating signed scores",
    )
    return {
        "root_difference_in_two_leaf_orbit_units": separated,
        "only_after_declaring_component_exchange_a_gauge": merged,
        "bridged_common_null_settings_A_depth_B_depth": offsets,
        "signed_null_comparator_by_candidate_B_to_A_root_scale": alternatives,
        "minimal_cross_origin_check": "one full signed cancellation A_r−B_s fixes theta=3^(s−r) in the stated common additive meter; all local parent/child nulls are unchanged by independent scale factors",
        "observable_limit": "reunion after following parent links tests shared ancestry, not equal amplitudes. Without a joint subtraction/honest cancellation operation, equal depth and synchronized clocks do not identify origin scale or sign.",
    }


def probe():
    return {
        "scope": "unordered finite ternary refinement of signed records, no imported wave amplitude or physical branching law",
        "full_height_two_group_check": group_controls(),
        "fixed_vs_coinvariant_and_local_exchange": orbit_and_exchange_relations(),
        "observable_sibling_only_vs_arbitrary_equal_depth_merge": branch_contact_observable(),
        "compatible_cut_calibration": compatible_cuts(),
        "separate_origins_vs_registered_cross_null": origin_registration(),
        "distinctions": {
            "local_parent_relation": "parent is the sum of its three actual signed child subtrees without assigning a numeric scale; a branch-aware observer can still distinguish the subtrees",
            "observer_effect": "fixing a path does not cause equal-depth quotient; side-branch orbit remains independent of marked branch, and parent-minus-three-marked is twice their difference",
            "least_exchange_support": "moving x to y forces both divergent sibling blocks at their lowest common ancestor to move, and their explicit transposition attains the bound. This is a count of affected addresses, not a traversal or energetic cost.",
            "why_a_global_scalar_is_extra": "a linear additive readout with genuinely trivial full automorphism action factors through leaf coinvariants. Invariance of an apparatus under relabeling does not stop it reading nonlinear sibling reunions, or retaining ancestry when it compares branches.",
            "not_a_physics_primitive": "tree structure, signed summation, comparable leaf preparations, permission to retain or erase parent history, and a shared cross-origin comparator are resources, not outputs of integer algebra",
        },
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
