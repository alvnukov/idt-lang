"""Finite scheduled four-setting Gray comparator built only from the mobile-blank contact.

Supplied: clean stocks, three independent fair source shades, two arms, local
zero references, chronological contact words, controlled shutters, and a final
number meter. No intermediate label selects a contact. This classical witness
is not a spontaneous clock, a Born/quantum readout, or an empirical result.
"""

import argparse
from collections import Counter
from dataclasses import dataclass
from functools import cache
from itertools import product
import json

from scripts.probe_mobile_blank_interferometer import contact


STOCKS = tuple(product((1, 2), repeat=3))
MASKS = tuple(product((False, True), repeat=2))
SETTINGS = tuple(product(range(4), repeat=2))
SHUTTERS = ("upstream_full", "upstream_token_only", "return")
ARMS = tuple(tuple(f"{side}_{s}" for s in "abm") for side in "LR")
# A and B denote the first and second internal edges; X/Y/Z are zero leaves.
# B in these words is the edge called C in the conjugation Q=C P C.
ENCODE = "B"
STEP = "XA" * 3
PLATE = ENCODE + STEP + ENCODE
CLONE, ROUTE, FOLD, COMPARE = "ZAYBZA", "YZBAYBY", "YAB", "XBAYBYAXB"


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def word(stage, sites, letters):
    a, b, m = sites
    edges = {"A": (a, b), "B": (b, m),
             "X": ("zero_" + stage + "_a", a), "Y": ("zero_" + stage + "_b", b),
             "Z": ("zero_" + stage + "_m", m)}
    return tuple(edges[s] for s in letters)


def replay(cells, schedule):
    """Execute the supplied edge sequence, retaining all source/dump/history cells."""
    for a, b in schedule:
        old = cells[a], cells[b]
        new = contact(old)
        require(old.count(3) == new.count(3), "token count changed at a raw contact")
        require((old[0] == 0) == (new[0] == 0) and (old[1] == 0) == (new[1] == 0),
                "zero reference moved or changed")
        cells[a], cells[b] = new


def local(triple, letters):
    sites = ("a", "b", "m")
    cells = dict(zip(sites, triple, strict=True))
    schedule = word("local", sites, letters)
    cells.update({u: 0 for edge in schedule for u in edge if u.startswith("zero_")})
    replay(cells, schedule)
    return tuple(cells[s] for s in sites)


def cycles(states, permutation):
    require(set(permutation) == set(states) and len(set(states)) == len(states), "not a permutation")
    mapping = dict(zip(states, permutation, strict=True))
    unseen = set(states)
    lengths = []
    while unseen:
        state = next(iter(unseen))
        length = 0
        while state in unseen:
            unseen.remove(state)
            state = mapping[state]
            length += 1
        lengths.append(length)
    return tuple(sorted(lengths))


def plate_cycles():
    profiles = []
    for tokens in (0, 1):
        states = tuple(s for s in product((1, 2, 3), repeat=3) if s.count(3) == tokens)
        profiles.append(cycles(states, tuple(local(s, PLATE) for s in states)))
    return tuple(profiles)


def two_cell_wall():
    """Exact joint permutation group, restricted to two sites and A,X,Y only."""
    states = tuple(sorted((s for s in product((1, 2, 3), repeat=2) if s.count(3) <= 1),
                          key=lambda s: s.count(3)))
    gens = [tuple(states.index(local((*s, 1), letter)[:2]) for s in states) for letter in "AXY"]
    identity = tuple(range(len(states)))
    group, todo = {identity}, [identity]
    while todo:
        perm = todo.pop()
        for gen in gens:
            updated = tuple(gen[i] for i in perm)
            if updated not in group:
                group.add(updated)
                todo.append(updated)
    simultaneous = sum(cycles(identity[:4], p[:4]) == (4,) and cycles(identity[4:], p[4:]) == (4,)
                       for p in group)
    return len(group), simultaneous


@cache
def schedule(shutter, opened, settings, independent, right_prep_steps):
    """Compile independently of stock values; each stage/arm owns its zero leaves."""
    left, right = ARMS
    ml, mr = left[2], right[2]
    edges = []
    if not independent:
        for i in range(2):
            edges.extend(word("source_clone_" + str(i), (ml, left[i], right[i]), CLONE))
    edges.extend(word("source_offset", right, STEP * right_prep_steps))
    edges.extend(word("source_route", (ml, mr, "coin"), ROUTE))
    for side, sites, is_open, power in zip("LR", ARMS, opened, settings, strict=True):
        if not is_open and shutter.startswith("upstream_"):
            intercepted = sites if shutter == "upstream_full" else sites[2:]
            edges.extend((s, "dump_" + s) for s in intercepted)
        edges.extend(word("encode_" + side, sites, ENCODE))
        edges.extend(word("plate_" + side, sites, PLATE * power))
        edges.extend(word("decode_" + side, sites, ENCODE))
        if not is_open and shutter == "return":
            edges.extend((s, "dump_" + s) for s in sites[1:])
    edges.extend(word("fold", (ml, mr, "history"), FOLD))
    for side, sites in zip("LR", ARMS, strict=True):
        edges.extend(word("compare_" + side, (ml, mr, sites[1]), COMPARE))
    return tuple(edges)


@dataclass
class Trial:
    outcome: int  # 0, 1, 2 = left, right, isolated dump
    final: dict[str, int]
    contacts: int


def trial(shutter, opened, settings, stock, *, independent_right=None, right_prep_steps=0):
    require(shutter in SHUTTERS and opened in MASKS and settings in SETTINGS and stock in STOCKS,
            "unsupported shutter, switches, settings or source stock")
    require(right_prep_steps in range(4) and independent_right in (None, (1, 1), (1, 2), (2, 1), (2, 2)),
            "unsupported supplementary source")
    edges = schedule(shutter, opened, settings, independent_right is not None, right_prep_steps)
    cells = {s: 0 if s.startswith("zero_") else 1 for edge in edges for s in edge}
    # Include every arm cell even when it does not occur in the active word.
    for sites in ARMS:
        for s in sites:
            cells.setdefault(s, 1)
    cells.update(L_a=stock[0], L_b=stock[1], L_m=3, coin=stock[2])
    if independent_right is not None:
        cells["R_a"], cells["R_b"] = independent_right
    replay(cells, edges)
    readings = (int(cells["L_m"] == 3), int(cells["R_m"] == 3),
                sum(v == 3 for s, v in cells.items() if s.startswith("dump_")))
    require(sum(readings) == 1 and list(cells.values()).count(3) == 1, "unaccounted final token")
    return Trial(readings.index(1), cells, len(edges))


def verify():
    profiles, wall = plate_cycles(), two_cell_wall()
    require(profiles == ((4, 4), (1,) * 8 + (4,)), "three-cell plate closure changed")
    require(wall == (96, 0), "restricted two-cell group changed")
    tables = {}
    launches = contacts = 0
    for shutter, opened in product(SHUTTERS, MASKS):
        table = []
        for x, y in SETTINGS:
            counts = [0, 0, 0]
            for stock in STOCKS:
                row = trial(shutter, opened, (x, y), stock)
                counts[row.outcome] += 1
                contacts += row.contacts
                launches += 1
            k = (8, 4, 0, 4)[(x - y) % 4]
            if all(opened):
                expected = [k, 8 - k, 0]
            elif not any(opened):
                expected = [0, 0, 8]
            elif shutter == "upstream_token_only":
                expected = [k // 2, (8 - k) // 2, 4]
            else:
                expected = [2, 2, 4]
            require(counts == expected, f"unexpected counts {counts}: {shutter=} {opened=} {x=} {y=}")
            table.append(counts)
        tables[shutter + "/" + "".join("1" if o else "0" for o in opened)] = table
    supplemental = Counter()
    for x, y in SETTINGS:
        flat = Counter(trial("upstream_full", (True, True), (x, y), s, independent_right=r).outcome
                       for s, r in product(STOCKS, product((1, 2), repeat=2)))
        shift = Counter(trial("upstream_full", (True, True), (x, y), s, right_prep_steps=1).outcome
                        for s in STOCKS)
        k = (8, 4, 0, 4)[(x - y - 1) % 4]
        require(flat == {0: 16, 1: 16} and (shift[0], shift[1]) == (k, 8 - k),
                "supplementary source control mismatch")
        supplemental.update(independent_right=sum(flat.values()), right_one_step=sum(shift.values()))
    return {"scope": __doc__, "main_trials": launches, "main_contacts": contacts,
            "blank_and_one_token_Q_cycle_lengths": profiles, "two_cell_AXY_group_size_and_hits": wall,
            "supplementary_trials": dict(supplemental), "settings_order": SETTINGS,
            "per_eight_unconditional_D0_D1_dump": tables}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    if parser.parse_args().json:
        print(json.dumps(verify(), sort_keys=True))
    else:
        report = verify()
        print(f"{report['main_trials']} main launches; {report['main_contacts']} raw contacts.")
        print("D0 by relative setting: 1, 1/2, 0, 1/2. One full or return shutter: 1/4, 1/4, 1/2.")
        print("Token-only shutter preserves the surviving fringe. Finite scheduled classical fixture.")
