"""Addressed K4 Boolean logic from an available neighboring link.

An offer toggles its edge exactly once if another occupied edge touches it.
The carrier, bit assignment, work preparation, target and offer word are
supplied. This finite permutation probe supplies no endogenous scheduler,
universal physical dynamics or quantum derivation.

Run: python3 -m scripts.probe_available_link_logic
"""

from __future__ import annotations

import json
from collections.abc import Iterable
from itertools import combinations, permutations
from math import lcm, perm

from scripts.probe_loopless_link_quartet import (
    BLANK_OR,
    Edge,
    LooplessGraph,
    Permutation,
    is_affine,
    nontrivial_cycles,
    quartet_target,
    transpositions,
)
from scripts.probe_loopless_matching_ports import addresses, cnot_word

K4 = tuple(combinations(range(4), 2))
FROZEN = "3130301020301012013020101201302010120130230201030313"
# Full permutations built from conjugates of a lone 3-cycle, replayed below.
MIN_DIRTY = (
    "31021301010101312021030210101010203012134104"
    "03131010101031304012421320301010101302312424"
)
UNIFORM = (
    "250321321010101023123013532025101010105202353154313202010101012023"
    "134243102031010101030201513532025010101015202353103213201010101231"
    "230534543121030201010101203012021310101010312013431020301010101302"
    "013535313203101010103023135102130101010131202103021010101020301213"
)
Tables = tuple[Permutation, ...]


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise RuntimeError(reason)


def witness_masks(edges: tuple[Edge, ...]) -> tuple[int, ...]:
    """Outside incidence masks; slot i itself is never a witness."""
    return tuple(
        sum(
            1 << j
            for j, other in enumerate(edges)
            if j != i and (a in other or b in other)
        )
        for i, (a, b) in enumerate(edges)
    )


def offer_tables(edges: tuple[Edge, ...]) -> Tables:
    return tuple(
        tuple(s ^ (1 << i) if s & mask else s for s in range(1 << len(edges)))
        for i, mask in enumerate(witness_masks(edges))
    )


def replay(state: int, word: Iterable[int], tables: Tables) -> int:
    for edge in word:
        state = tables[edge][state]
    return state


def compile_word(word: tuple[int, ...], tables: Tables) -> Permutation:
    return tuple(replay(s, word, tables) for s in range(len(tables[0])))


def saturation_word(state: int, tables: Tables) -> tuple[int, ...]:
    """Prefer the first enabled addition; all such offers can be undone."""
    if not 0 < state < len(tables[0]):
        raise ValueError("saturation starts at a nonempty carrier state")
    word = []
    while state != len(tables[0]) - 1:
        for i, offer in enumerate(tables):
            if offer[state] > state:
                word.append(i)
                state = offer[state]
                break
        else:
            raise ValueError("non-full saturated state on this carrier")
    return tuple(word)


def group_certificate(edges: tuple[Edge, ...]) -> dict:
    """Conjugate a lone 3-cycle; exhaust its ordered triple orbit.

    Reaching all ordered triples gives every 3-cycle, hence generates at
    least the alternating group. The sign of the single offers then decides
    whether odd permutations are present too. Zero is fixed throughout.
    Masks in each certificate use local edge slots (not K4 edge indices).
    """
    tables = offer_tables(edges)
    swaps = [len(transpositions(p)) for p in tables]
    require(all(p[0] == 0 for p in tables), "blank moved")
    # Use an incident pair in this layout, not always the first two slots.
    a, b = next(
        (a, b)
        for a, b in combinations(range(len(edges)), 2)
        if set(edges[a]) & set(edges[b])
    )
    cycles = nontrivial_cycles(compile_word((a, b) * 4, tables))
    require(len(cycles) == 1 and len(cycles[0]) == 3, "expected a lone 3-cycle")
    seed = cycles[0]
    seen = {seed}
    todo = [seed]
    while todo:
        x, y, z = todo.pop()
        for p in tables:
            nxt = (p[x], p[y], p[z])
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    n = len(tables[0]) - 1
    require(len(seen) == perm(n, 3), "triple orbit does not certify all 3-cycles")
    name = "Sym" if any(k % 2 for k in swaps) else "Alt"
    return {
        "offer_swaps": swaps,
        "seed_pair_fourth_power": [a, b],
        "seed_cycle": list(seed),
        "ordered_triples": len(seen),
        "group": f"{name}({n})",
    }


def repeated_sweeps(tables: Tables, offered: tuple[int, ...]) -> dict:
    """All powers of a *single* fixed sweep, scored on complete clean states."""
    best = {"orders": 0, "best_clean_matches": -1, "best_order": [], "best_power": 0}
    for order in permutations(offered):
        best["orders"] += 1
        p = compile_word(order, tables)
        constraints = []
        period = 1
        for start in range(16):
            target = quartet_target(start)
            end, length, residue = start, 0, None
            while True:
                if end == target:
                    residue = length
                end, length = p[end], length + 1
                if end == start:
                    break
            if residue is not None:
                constraints.append((length, residue))
                period = lcm(period, length)
        # Inputs with inaccessible targets score zero at every power. The
        # score of all remaining inputs repeats with this common period.
        scores = [0] * period
        for length, residue in constraints:
            for k in range(residue, period, length):
                scores[k] += 1
        score = max(scores)
        if score > best["best_clean_matches"]:
            best.update(
                best_clean_matches=score,
                best_order=list(order),
                best_power=scores.index(score) or period,
            )
    return best


def old_word_controls(tables: Tables) -> dict:
    graph = LooplessGraph(4)
    old = BLANK_OR
    require(
        graph.edges == K4
        and old.layout.data_edges == (0, 1, 2, 3)
        and old.layout.work_state == 0,
        "parity reference layout changed",
    )
    control, target = (0, 1), (2, 3)
    c, t = addresses(graph, (control, target))
    controlled = addresses(graph, cnot_word(control, target))
    cases = [
        (x << c | y << t, x << c | (x ^ y) << t) for x in range(2) for y in range(2)
    ]
    require(
        all(graph.replay(s, controlled, old.code) == goal for s, goal in cases),
        "old controlled XOR does not pass its reference rule",
    )
    require(
        all(
            graph.replay(s, old.word, old.code) == quartet_target(s) for s in range(16)
        ),
        "old quartet does not pass its reference rule",
    )
    return {
        "quartet_length": len(old.word),
        "quartet_matches": sum(
            replay(s, old.word, tables) == quartet_target(s) for s in range(16)
        ),
        "cnot_length": len(controlled),
        "cnot_matches": sum(replay(s, controlled, tables) == goal for s, goal in cases),
    }


def extension_certificates(full: dict, tables: Tables) -> dict:
    """Match group membership and explicit, not necessarily shortest, programs."""
    clean = tuple(map(quartet_target, range(16)))
    clean_swaps = len(transpositions(clean))
    require(clean_swaps % 2 == 1 and full["group"] == "Alt(63)", "parity premise lost")
    # Every full permutation realizing the clean action leaves dirty states
    # invariant AS A SET. To cancel odd clean sign it must move at least two.
    # Swapping two dirty states attains the bound by full group membership.
    minimal = list(clean) + list(range(16, 64))
    minimal[16], minimal[17] = minimal[17], minimal[16]
    require(
        minimal[0] == 0 and len(transpositions(tuple(minimal))) % 2 == 0,
        "minimal dirty extension is not even and vacuum-fixing",
    )
    uniform = tuple((s & 48) | clean[s & 15] for s in range(64))
    uniform_even = len(transpositions(uniform)) % 2 == 0
    require(
        uniform_even and uniform[0] == 0,
        "four-copy extension is not even and vacuum-fixing",
    )
    certificates = []
    for label, word, target in (
        ("minimal_dirty_disturbance", MIN_DIRTY, tuple(minimal)),
        ("uniform_quartet_preserving_work", UNIFORM, uniform),
    ):
        actual = compile_word(tuple(map(int, word)), tables)
        require(actual == target, f"{label}: full permutation replay mismatch")
        certificates.append({"target": label, "word": word, "matches": len(actual)})
    return {
        "clean_target_swaps": clean_swaps,
        "identity_outside_min_dirty_moved": sum(minimal[i] != i for i in range(16, 64)),
        "four_copy_target_even": uniform_even,
        "four_copy_reachable_with_all_six_offers": True,
        "word_certificates": certificates,
        "construction": "closed K4; work edges may be offered; no shortest-length claim",
    }


def ambient_control() -> dict:
    """Held occupied leaves covering the internal edges; only K4 offers allowed."""
    leaves = ((0, 4), (1, 5), (2, 6))
    tables = offer_tables(K4 + leaves)
    cover = 7 << len(K4)
    unconditional = sum(
        all(tables[i][cover | s] == ((cover | s) ^ (1 << i)) for s in range(64))
        for i in range(6)
    )
    require(unconditional == 6, "held exterior witnesses did not cover every offer")
    # Thus every internal word is a constant XOR translation of the entire
    # K4 mask. Conversely each of the 64 translations is made by offering
    # its set bits once. This rules out a uniform internal word even when
    # initially blank internal work edges may be temporarily toggled.
    return {
        "persistent_leaves": leaves,
        "unconditional_internal_offers": unconditional,
        "whole_internal_inputs_checked": 64,
        "best_clean_matches_any_internal_word": max(
            sum((s ^ delta) == quartet_target(s) for s in range(16))
            for delta in range(64)
        ),
    }


def experiment() -> dict:
    tables = offer_tables(K4)
    for s in range(1, 64):
        path = saturation_word(s, tables)
        require(
            replay(s, path, tables) == 63 and replay(63, reversed(path), tables) == s,
            "saturation/reversal certificate failed",
        )
    word = tuple(map(int, FROZEN))
    require(
        len(word) == 52 and set(word) == set(range(4)), "wrong clean witness addresses"
    )
    mapped = compile_word(word, tables)
    matches = [
        sum(mapped[work | s] == (work | quartet_target(s)) for s in range(16))
        for work in (0, 16, 32, 48)
    ]
    # With both workers occupied, each data edge has a permanent witness.
    # Any data-only word then XORs a constant data mask, not a nonlinear map.
    unconditional = [
        all(tables[i][s] == s ^ (1 << i) for s in range(48, 64)) for i in range(4)
    ]
    layouts = []
    for ids in combinations(range(6), 4):
        support = tuple(K4[i] for i in ids)
        degrees = sorted(sum(v in e for e in support) for v in range(4))
        require(degrees in ([2] * 4, [1, 2, 2, 3]), "unexpected four-edge K4 support")
        cert = group_certificate(support)
        layouts.append(
            {
                "data_edge_indices": list(ids),
                "shape": "four_cycle"
                if degrees == [2] * 4
                else "triangle_with_pendant",
                # The clean quartet fixes zero and is three transpositions.
                "quartet_reachable": cert["group"] == "Sym(15)",
                **cert,
            }
        )
    full = group_certificate(K4)
    mask = witness_masks(K4)[0]
    witness_count = (6 & mask).bit_count()
    serial = tuple(s ^ ((s & mask).bit_count() % 2) for s in range(64))
    return {
        "scope": "finite native permutation certificates; addressed external scheduler, "
        "no minimal word claim, no physical law or quantum derivation",
        "edge_order": K4,
        "state_orbits": [1, 63],
        "multiple_witness": {
            "state": 6,
            "offered_edge": 0,
            "count": witness_count,
            "single_toggle": tables[0][6],
            "serial_xor": serial[6],
            "serial_xor_linear": serial[0] == 0 and is_affine(serial),
            "available_affine": is_affine(tables[0]),
        },
        "witness": {
            "word": FROZEN,
            "whole_state_matches_by_work": matches,
            "dirty_states_moved": sum(mapped[s] != s for s in range(16, 64)),
        },
        "old_words": old_word_controls(tables),
        "occupied_pair_unconditional_data_offers": unconditional,
        "full_group": full,
        "clean_data_layouts": layouts,
        "extensions": extension_certificates(full, tables),
        "ambient_control": ambient_control(),
        "repeated_sweeps": [repeated_sweeps(tables, tuple(range(k))) for k in (4, 6)],
    }


if __name__ == "__main__":
    print(json.dumps(experiment(), sort_keys=True))
