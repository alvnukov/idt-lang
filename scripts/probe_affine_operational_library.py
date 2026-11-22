"""Closed native macro libraries for the frozen six-stock F5 apparatus.

The six P_k and detector D are exactly the center-defect four-ticket
preparations and terminal equality-OR reader of the neighboring probes.
For M_k=(P_k+P_(k+3))/2, distinguish two supplied comparison requirements:
E: all three M_k rates are equal for every accessible effect;
H: all are one half for every accessible reversible rank-one qubit analyzer.
H is stronger; E alone permits a zero effect. Neither comparison certifies
that these finite stocks actually are antipodal pure qubit states.

Enumerate all subgroups containing W in the native GL2(5) action. A finite
composition-closed reversible library containing identity is a subgroup:
each inverse is a positive power. No inverse pulse is therefore free here.
The enumeration rejects a branch on its first forbidden element and adds
every remaining permissible generator, so it exhausts admissible groups,
not merely individually passing gates. Independent old-analyzer shifts
give a second certificate of the unique maximal permissible sets.

Libraries contain completed macros, with D only at their end. The gate
letters used inside a macro are not separately accessible analyzers in
this restricted stance. Allowing every native prefix restores all 480
maps and fails. The largest H library is noncommuting but supplies no new
detector row on these six stocks beyond the original six dials. Source,
reference, fair tickets, equality/OR detector, and restriction to chosen
macros remain supplied. No empirical data, contextuality conclusion,
universal proof, physical exclusion, or QM derivation is asserted.

This does not classify stochastic channels with cancellation between
individually failing components, adaptive/intermediate measurements,
different sources/readers, ancillas, or larger native systems.

Run: python3 -B -O -m scripts.probe_affine_operational_library
"""

from __future__ import annotations

import json
from collections import Counter
from itertools import product

from scripts.probe_affine_contact_fringe import Six, act
from scripts.probe_affine_contact_fringe import detector as raw_detector
from scripts.probe_affine_preparation_mixtures import TARGET
from scripts.probe_affine_pulse_holdouts import (
    IDENT,
    TAGS,
    Perm,
    contacts,
    encode,
    gates,
    measure,
    need,
    plane_matrix,
    power,
    then,
)

Matrix = tuple[int, int, int, int]
Group = frozenset[int]
Table = list[list[int]]


def matrix_then(first: Matrix, second: Matrix) -> Matrix:
    """Column coordinates: chronological first,second means second * first."""
    a, b, c, d = first
    e, f, g, h = second
    return (
        (e * a + f * c) % 5,
        (e * b + f * d) % 5,
        (g * a + h * c) % 5,
        (g * b + h * d) % 5,
    )


def generated(
    table: Table, generators: tuple[int, ...], allowed: Group
) -> Group | None:
    """Breadth-first positive words; None is an actual forbidden-word witness."""
    if 0 not in allowed:
        return None
    queue = [0]
    seen = {0}
    for x in queue:
        for g in generators:
            y = table[x][g]
            if y not in allowed:
                return None
            if y not in seen:
                seen.add(y)
                queue.append(y)
    return frozenset(seen)


def admissible_subgroups(table: Table, base: Group, allowed: Group) -> list[Group]:
    need(base <= allowed, "base violates the requested criterion")
    found = [base]
    seen = {base}
    for group in found:
        for g in sorted(allowed - group):
            extension = generated(table, tuple(sorted(group)) + (g,), allowed)
            if extension is not None and extension not in seen:
                seen.add(extension)
                found.append(extension)
    return sorted(found, key=lambda g: (len(g), tuple(sorted(g))))


def first_bad_word(
    table: Table, generators: tuple[int, ...], allowed: Group
) -> tuple[int, ...]:
    """Shortest completed-macro word, not shortest expanded contact word."""
    queue = [0]
    paths: dict[int, tuple[int, ...]] = {0: ()}
    for x in queue:
        if x not in allowed:
            return paths[x]
        for i, g in enumerate(generators):
            y = table[x][g]
            if y not in paths:
                paths[y] = paths[x] + (i,)
                queue.append(y)
    raise ValueError("no forbidden word exists")


def run() -> dict[str, object]:
    w, maps = gates()
    left, right = contacts()
    matrices = [plane_matrix(g) for g in maps]
    index = {m: i for i, m in enumerate(matrices)}
    full = frozenset(range(len(maps)))
    need(maps[0] == IDENT and len(index) == 480, "faithful native action")
    need(
        set(matrices)
        == {
            (a, b, c, d)
            for a, b, c, d in product(range(5), repeat=4)
            if (a * d - b * c) % 5
        },
        "not all GL2(5)",
    )
    table = [[index[matrix_then(a, b)] for b in matrices] for a in matrices]
    # Full permutation composition independently checks the column convention.
    # Basis vectors suffice for every pair after plane_matrix checked all125.
    basis = (encode(1, 0, 4), encode(0, 1, 4))
    for i, p in enumerate(maps):
        for j, second_map in enumerate(maps):
            need(
                all(maps[table[i][j]][x] == second_map[p[x]] for x in basis),
                "matrix product reversed or incorrect",
            )
        for contact in (left, right):
            j = index[plane_matrix(contact)]
            need(maps[table[i][j]] == then(p, contact), "full125 composition")
    need(then(left, right) != then(right, left), "noncommuting convention control")
    need(w == tuple(encode(*act(s, Six)) for s in TAGS), "raw chronological W")

    dial = [power(w, k) for k in range(6)]
    wi = index[plane_matrix(w)]
    cyclic = frozenset(index[plane_matrix(g)] for g in dial)
    bright = frozenset(i for i, s in enumerate(TAGS) if raw_detector(s, 0))
    need(
        bright
        == frozenset(i for i in IDENT if TAGS[i][0] == 0 or TAGS[dial[5][i]][0] == 0),
        "independent terminal reader replay",
    )
    orbit = tuple(g[encode(0, 1, 0)] for g in dial)
    stocks = [tuple(orbit[(k + j) % 6] for j in (0, 1, 1, 2)) for k in range(6)]
    mixtures = [stocks[k] + stocks[k + 3] for k in range(3)]
    solo = [tuple(measure(s, bright, g) for s in stocks) for g in maps]
    rows = [tuple(measure(s, bright, g) for s in mixtures) for g in maps]
    need(
        solo[0] == TARGET and all(rows[g] == (4, 4, 4) for g in cyclic),
        "frozen source and old analyzers",
    )
    equal = frozenset(i for i, r in enumerate(rows) if len(set(r)) == 1)
    half = frozenset(i for i, r in enumerate(rows) if r == (4, 4, 4))
    need(len(equal) == 96 and len(half) == 72, "one-setting census")
    groups = admissible_subgroups(table, cyclic, equal)
    half_groups = admissible_subgroups(table, cyclic, half)
    need(Counter(map(len, groups)) == {6: 1, 12: 3, 24: 1}, "complete equality lattice")
    need(Counter(map(len, half_groups)) == {6: 1, 12: 1}, "complete half lattice")
    maximal, half_maximal = groups[-1], half_groups[-1]
    need(all(g <= maximal for g in groups), "unique equality maximum")
    need(
        half_groups == [g for g in groups if g <= half],
        "independent stronger enumeration",
    )

    # A pre- and post-pulse dial are both available in any group containing W.
    # Exhausting post-shifts alone finds exactly the same closed maxima.
    shifted_equal = frozenset(
        g for g in full if all(table[g][h] in equal for h in cyclic)
    )
    shifted_half = frozenset(
        g for g in full if all(table[g][h] in half for h in cyclic)
    )
    need(
        shifted_equal == maximal and shifted_half == half_maximal,
        "all old analyzer shifts certificate",
    )
    for h in cyclic:
        for g in full:
            need(
                sorted(rows[table[h][g]]) == sorted(rows[g]),
                "source shift reindexes mixtures",
            )
    for group in groups:
        need(
            all(table[a][b] in group for a in group for b in group), "group not closed"
        )
        need(
            all(any(table[a][b] == table[b][a] == 0 for b in group) for a in group),
            "missing inverse",
        )
    for g in equal - maximal:
        need(generated(table, (wi, g), equal) is None, "missed forbidden extension")

    def word(text: str) -> int:
        out = IDENT
        for letter in text:
            need(letter in "LR", "unknown primitive")
            out = then(out, left if letter == "L" else right)
        return index[plane_matrix(out)]

    def order(g: int) -> int:
        current = 0
        for n in range(1, 481):
            current = table[current][g]
            if current == 0:
                return n
        raise ValueError("finite group order missing")

    c, t, q = word("LR"), word("RRLRLL"), word("LLLRLRRR")
    need(order(c) == 12 and table[c][c] == wi, "cyclic12 square root")
    need(
        order(t) == 2 and table[table[t][wi]][t] == word("LRLR" * 5),
        "dihedral12 reflection",
    )
    need(table[table[t][c]][t] == word("LR" * 5), "semidirect action c -> c^5")
    need(order(q) == 4 and table[q][q] == word("LRLR" * 3), "dicyclic12 square")
    qi = word("LLLRLRRR" * 3)
    need(table[table[q][wi]][qi] == word("LRLR" * 5), "dicyclic conjugation")
    named: dict[str, Group] = {}
    for label, generators in (
        ("C6", (wi,)),
        ("C12", (c,)),
        ("dihedral_order12", (wi, t)),
        ("dicyclic_order12", (wi, q)),
        ("C12_semidirect5_C2", (c, t)),
    ):
        named_group = generated(table, generators, full)
        if named_group is None:
            raise ValueError("unrestricted closure failed")
        named[label] = named_group
    need(
        set(named.values()) == set(groups)
        and named["dihedral_order12"] == half_maximal,
        "presentations do not identify exact lattice",
    )
    need(
        len({solo[g] for g in half_maximal}) == 6
        and {solo[g] for g in half_maximal} == {solo[g] for g in cyclic},
        "restricted survivor unexpectedly adds a six-stock effect",
    )
    need(
        all(maps[t][orbit[k]] == orbit[(5 - k) % 6] for k in range(6)),
        "surviving reflection on the six raw states",
    )
    for g in half_maximal:
        need(
            all(
                tuple(sorted(maps[g][x] for x in stock))
                in {tuple(sorted(s)) for s in stocks}
                for stock in stocks
            ),
            "surviving library does not close the six preparations",
        )
    need(
        Counter(rows[g] for g in maximal) == {(4, 4, 4): 12, (0, 0, 0): 12},
        "equal versus half distinction",
    )

    swap = word("RR")
    need(maps[swap] == tuple(encode(x, z, y) for x, y, z in TAGS), "literal right swap")
    need(swap in half and swap not in maximal, "superficially safe extension")
    witness = first_bad_word(table, (wi, swap), equal)
    need(
        witness == first_bad_word(table, (wi, swap), half) == (1, 0),
        "shortest macro witness (G then W)",
    )
    need(rows[table[swap][wi]] == (5, 5, 6), "bad composition row")
    extended = generated(table, (wi, swap), full)
    need(extended is not None and len(extended) == 240, "swap extension size")
    need(
        word("L") not in equal and word("R") not in equal,
        "one-contact failures / shortest superficial extension",
    )
    need(
        rows[word("L")] == (3, 2, 3) and rows[word("R")] == (4, 3, 5),
        "elementary negative controls",
    )
    need(
        Counter(x for k in (0, 2, 4) for x in stocks[k])
        == Counter(x for k in (1, 3, 5) for x in stocks[k]),
        "genuinely equal uniform-triad stocks",
    )
    # Supplied frame changes must move the reference too. No refitting.
    for u, v in product(range(1, 5), range(5)):
        relabel: Perm = tuple(encode(*((u * x + v) % 5 for x in s)) for s in TAGS)
        transported = frozenset(relabel[i] for i in bright)
        need(
            transported
            == frozenset(i for i, s in enumerate(TAGS) if raw_detector(s, v)),
            "reference transport",
        )
        moved = [tuple(relabel[i] for i in s) for s in mixtures]
        for i, frame_map in enumerate(maps):
            need(
                then(frame_map, relabel) == then(relabel, frame_map),
                "native affine covariance",
            )
            need(
                tuple(measure(s, transported, frame_map) for s in moved) == rows[i],
                "frame-dependent rate or classification",
            )
    # All fail-loud guards remain active in python -O.
    try:
        need(False, "intentional guard control")
    except ValueError as error:
        need(str(error) == "intentional guard control", "unexpected guard error")
    else:
        raise ValueError("guard disabled")

    return {
        "status": "finite_executable_classification_not_formal_proof",
        "native_maps": len(full),
        "individual_equal": len(equal),
        "individual_half": len(half),
        "all_old_analyzer_shifts_equal": len(shifted_equal),
        "all_old_analyzer_shifts_half": len(shifted_half),
        "subgroups": [
            {
                "name": label,
                "size": len(group),
                "all_half": group <= half,
                "orders": dict(sorted(Counter(order(g) for g in group).items())),
                "contained_in": [
                    name for name, other in named.items() if group < other
                ],
            }
            for label, group in named.items()
        ],
        "presentation_generators": {
            "W": "LRLR",
            "c": "LR",
            "t": "RRLRLL",
            "q": "LLLRLRRR",
        },
        "maximal_equal_half_zero_counts": [12, 12],
        "maximal_half_distinct_six_stock_effects": 6,
        "maximal_half_closes_six_preparations": True,
        "surviving_reflection_raw_phase": "k -> 5-k mod6",
        "shortest_superficial_extension": {
            "G": "RR",
            "matrix": matrices[swap],
            "alone_counts_over8": rows[swap],
            "shortest_bad_macro_word": "GW",
            "expanded_contacts": "RRLRLR",
            "bad_counts_over8": rows[table[swap][wi]],
            "generated_maps": 240,
            "minimality": "two W/G macros; G also shortest unsafe extension in L/R letters",
        },
        "frame_relabelings_checked": 20,
        "boundary": "fixed six stocks, fixed terminal reader, deterministic completed macros only",
    }


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True, separators=(",", ":")))
