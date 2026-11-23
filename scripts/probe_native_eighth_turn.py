"""Two finite native contact circuits for an eight-setting *classical* triangle.

Supplied: chronological words and clocks, arm graph, clean ordinary stocks, one
token, three independent fair source shades, one independent fair route shade,
shutters/refills, and a final token-number meter. The four-label B version uses
pinned zeros. The ternary CS version has no zero: it pays for restored ordinary
triangle catalysts, potentially dirty local parity balancers, and a fifth
ordinary clock cell per arm. Both clocks advance ordinary rails irrespective of
token route. Neither a natural oscillator, a Born rule nor an empirical test.
Run: python3 -m scripts.probe_native_eighth_turn [--json].
"""

import argparse
import json
from collections import Counter
from collections.abc import Callable, Mapping
from functools import cache, lru_cache
from itertools import pairwise, permutations, product
from typing import TypedDict

from scripts import probe_native_four_phase_gray as gray
from scripts import probe_ternary_active_readout as ternary
from scripts.probe_mobile_blank_interferometer import contact as b_contact

Edge = tuple[str, str]
Word = tuple[Edge, ...]
Stages = tuple[tuple[str, Word], ...]
Sites = tuple[str, ...]
Cells = dict[str, int]
Compiled = tuple[Sites, dict[str, int], tuple[tuple[int, int], ...], tuple[int, ...]]
raw_word: Callable[[str, tuple[str, str, str], str], Word] = gray.word
require: Callable[[bool, str], None] = gray.require
cs_contact: Callable[[str, str], tuple[str, str]] = ternary.contact


class Report(TypedDict):
    scope: str
    main_launches_per_backend: int
    raw_contacts: dict[str, int]
    max_touched_cells_per_launch: dict[str, int]
    D0_per_16_by_difference: list[int]
    shared_stock_removed_checks: int
    independent_source_B_launches: int
    restricted_walls: tuple[tuple[int, int], tuple[int, int]]
    marker_encoding: str
    one_arm_full_or_return_D0_D1_dump_per_16: tuple[int, int, int]
    one_arm_token_only: str

ARMS = tuple(tuple(f"{side}_q{i}" for i in range(4)) for side in "LR")
WRITE = "AXAXYAYA"
STOCKS = tuple(product((1, 2), repeat=4))
# Encode a,b,T as 1,2,3; no CS pair table is defined on label 0.
ABC = "abT"
CS = {i + 1: {j + 1: tuple(ABC.index(c) + 1 for c in cs_contact(x, y))
              for j, y in enumerate(ABC)} for i, x in enumerate(ABC)}
B = {i: {j: b_contact((i, j)) for j in range(4)} for i in range(4)}


def plate(q: Sites, side: str) -> Word:
    """Ordinary B swaps rotate last to first; the one zero leaf changes its sign."""
    a, b, c, d = q
    return ((c, d), (b, c), (a, b), ("zero_plate_" + side, a))


def cs_blank_plate(q: Sites, balancer: str) -> Word:
    """Five raw CS contacts, no T, clean reference or reset between steps needed."""
    s = (*q, balancer)
    return tuple((s[i], s[j]) for i, j in ((0, 2), (0, 3), (1, 4), (1, 2), (2, 4)))


def write_if_all(controls: Sites, targets: Sites) -> Word:
    """Move T along controls equal to shade 1, write on contact with T, undo route."""
    path = ("L_m", *controls)
    forward = tuple(pairwise(path))
    writes = tuple(edge for q in targets for edge in
                   raw_word("write_" + path[-1] + "_" + q, (path[-1], q, "unused"), WRITE))
    return forward + writes + forward[::-1]


def prepare(q: Sites, controls: Sites) -> Word:
    """Initialize (u OR v, u, u AND v, 0) XOR g on four clean rails."""
    g, u, v = controls
    a, b, c, _ = q
    return (write_if_all((u,), (a, b)) + write_if_all((v,), (a,))
            + write_if_all((u, v), (a, c)) + write_if_all((g,), q))


@cache
def source(independent: bool = False) -> Stages:
    left, right = ARMS
    stages = [("source_left", prepare(left, ("g", "u", "v")))]
    if independent:
        stages.append(("source_right", prepare(right, ("rg", "ru", "rv"))))
    else:
        clones = tuple(edge for i in range(4) for edge in
                       raw_word(f"clone_{i}", ("L_m", left[i], right[i]), gray.CLONE))
        stages.append(("source_clone", clones))
    return tuple(stages)


def schedule(shutter: str, opened: tuple[bool, ...], settings: tuple[int, ...],
             backend: str, independent: bool = False) -> Stages:
    require(shutter in gray.SHUTTERS and opened in gray.MASKS and len(settings) == 2
            and all(type(x) is int and 0 <= x < 8 for x in settings) and backend in ("B", "CS"),
            "unsupported shutter, settings, mask or native contact")
    stages = list(source(independent))
    stages.append(("route", raw_word("route", ("L_m", "R_m", "coin"), gray.ROUTE)))
    for q, side, is_open, power in zip(ARMS, "LR", opened, settings, strict=True):
        m = side + "_m"
        if not is_open and shutter != "return":
            take = (*q, m) if shutter == "upstream_full" else (m,)
            stages.append(("up_" + side, tuple((s, "dump_" + s) for s in take)))
        if backend == "CS":
            stages.append(("rawCS_plate_" + side, cs_blank_plate(q, side + "_parity") * power))
        else:
            stages.append(("plate_" + side, plate(q, side) * power))
        if not is_open and shutter == "return":
            stages.append(("return_" + side, tuple((s, "dump_" + s) for s in (q[0], m))))
    stages.append(("fold", raw_word("fold", ("L_m", "R_m", "history"), gray.FOLD)))
    for side, q in zip("LR", ARMS, strict=True):
        name = "compare_" + side
        stages.append((name, raw_word(name, ("L_m", "R_m", q[0]), gray.COMPARE)))
    return tuple(stages)


def translate(stage: str, edge: Edge) -> Word:
    """Ordinary B = 9-contact vacancy. A B zero leaf additionally needs raw CS.

    CS(x,r) then vacancy(x,r) flips both ordinary shades but fixes a mixed pair.
    The balancer r is local to the former zero leaf and may carry parity history.
    Only the separate vacancy compiler's ordinary catalyst is restored per call.
    """
    x, y = edge
    is_leaf = x.startswith("zero_") or y.startswith("zero_")
    if is_leaf:
        x, y = (y, "bal_" + x) if x.startswith("zero_") else (x, "bal_" + y)
    sites = (x, y, "cat_" + stage)
    vacancy = tuple((sites[i], sites[j]) for i, j in ternary.VACANCY)
    return (((x, y),) if is_leaf else ()) + vacancy


@lru_cache(maxsize=24)
def compile_stages(stages: Stages, backend: str) -> Compiled:
    require(backend in ("B", "CS", "CS_raw"), "unknown native contact")
    edges: list[Edge] = []
    for stage, segment in stages:
        for edge in segment:
            if backend == "CS" and not stage.startswith("rawCS_"):
                edges.extend(translate(stage, edge))
            else:
                edges.append(edge)
    sites = tuple(dict.fromkeys(s for edge in edges for s in edge))
    indices = {s: i for i, s in enumerate(sites)}
    word = tuple((indices[i], indices[j]) for i, j in edges)
    clean = tuple(0 if s.startswith("zero_") else 1 for s in sites)
    return sites, indices, word, clean


def execute(stages: Stages, backend: str, initial: Cells) -> Cells:
    sites, indices, word, clean = compile_stages(stages, backend)
    cells = list(clean)
    for s, val in initial.items():
        if s in indices:
            cells[indices[s]] = val
    table: Mapping[int, Mapping[int, tuple[int, ...]]] = B if backend == "B" else CS
    for i, j in word:
        cells[i], cells[j] = table[cells[i]][cells[j]]
    return initial | dict(zip(sites, cells, strict=True))


def detector(state: Cells) -> int:
    t = (int(state.get("L_m") == 3), int(state.get("R_m") == 3),
         sum(v == 3 for s, v in state.items() if s.startswith("dump_")))
    require(sum(t) == 1 and sum(v == 3 for v in state.values()) == 1, "unaccounted token")
    return t.index(1)


def signed_wall(n: int, even: bool) -> tuple[int, int]:
    """Enumerate signed-coordinate maps and count (map, point) pairs of period eight.

    On blank B rails arbitrary swaps and pinned-zero flips can only permute or
    complement coordinates. Blank CS swaps and complements both inputs, hence
    preserves the parity of sign changes. Smaller systems embed with fixed rails.
    Nothing here bounds token-involved words, variable clocks, or larger stocks.
    """
    points = tuple(product(range(2), repeat=n))
    total = hits = 0
    for p, signs in product(permutations(range(n)), points):
        if even and sum(signs) % 2:
            continue
        total += 1
        f = {x: tuple(x[i] ^ s for i, s in zip(p, signs, strict=True)) for x in points}
        for start in points:
            x = start
            for power in range(1, 9):
                x = f[x]
                if x == start:
                    hits += int(power == 8)
                    break
    return total, hits


def marker_orbit() -> tuple[str, ...]:
    """Optional B encoding E swaps the last shade and marker when permitted.

    E Q E on the E-coded sector moves the token between marker and a phase site.
    This is a conjugate of a spectator token, not token back-reaction or a new
    detector. Shutters in the actual two-arm fixture act on the decoded wires.
    """
    q = ARMS[0]
    e = ((q[-1], "L_m"),)
    current = execute((("enter", e),), "B", {s: 1 for s in q} | {"L_m": 3})
    initial = tuple(current[s] for s in (*q, "L_m"))
    orbit: list[tuple[int, ...]] = []
    for _ in range(8):
        raw = tuple(current[s] for s in (*q, "L_m"))
        require(raw not in orbit, "encoded cycle returned too early")
        orbit.append(raw)
        current = execute((("pulse", e + plate(q, "L") + e),), "B", current)
    require(tuple(current[s] for s in (*q, "L_m")) == initial, "encoded cycle did not close")
    return tuple("q" if row[3] == 3 else "m" for row in orbit)


def audit_letters() -> None:
    for x, y in product((1, 2, 3), repeat=2):
        ref = B[x][y]
        state = execute((("letter", (("x", "y"),)),), "CS", {"x": x, "y": y})
        require((state["x"], state["y"], state["cat_letter"]) == (*ref, 1), "bad vacancy")
    for x, r in product((1, 2, 3), (1, 2)):
        state = execute((("leaf", (("zero_f", "x"),)),), "CS", {"x": x, "bal_zero_f": r})
        require((state["x"], state["bal_zero_f"], state["cat_leaf"]) ==
                     (B[0][x][1], 3 - r if x != 3 else r, 1), "bad balance leaf")


def verify() -> Report:
    audit_letters()
    walls = (signed_wall(3, False), signed_wall(4, True))
    require(walls == ((48, 0), (192, 0)), "unexpected restricted eighth-period point")
    require(marker_orbit() == ("q",) * 4 + ("m",) * 4, "encoded marker changed")
    fringe = [16 - 4 * min(d, 8 - d) for d in range(8)]
    contacts: Counter[str] = Counter()
    launches = 0
    peak_cells: Counter[str] = Counter()
    for shutter, opened, (x, y) in product(gray.SHUTTERS, gray.MASKS, product(range(8), repeat=2)):
        outcomes = {}
        for backend in ("B", "CS"):
            stages = schedule(shutter, opened, (x, y), backend)
            sites, _, word, _ = compile_stages(stages, backend)
            peak_cells[backend] = max(peak_cells[backend], len(sites))
            outcomes[backend] = tuple(detector(execute(stages, backend,
                dict(zip(("g", "u", "v", "coin"), stock, strict=True)) | {"L_m": 3}))
                for stock in STOCKS)
            contacts[backend] += len(word) * len(STOCKS)
        require(outcomes["B"] == outcomes["CS"], "native raw trajectories differ at the meter")
        counts = Counter(outcomes["B"])
        hits = fringe[(x - y) % 8]
        if all(opened):
            expected = (hits, 16 - hits, 0)
        elif not any(opened):
            expected = (0, 0, 16)
        elif shutter == "upstream_token_only":
            expected = (hits // 2, (16 - hits) // 2, 8)
        else:
            expected = (4, 4, 8)
        require(tuple(counts[i] for i in range(3)) == expected, "unconditional table mismatch")
        launches += len(STOCKS)
    # Separate, actual B launches. Three fresh right controls replace the four clone words.
    for x, y in product(range(8), repeat=2):
        stages = schedule("upstream_full", (True, True), (x, y), "B", independent=True)
        counts = Counter(detector(execute(stages, "B", {"L_m": 3} |
            dict(zip(("g", "u", "v", "coin", "rg", "ru", "rv"), stock, strict=True))))
            for stock in product((1, 2), repeat=7))
        require(counts == {0: 64, 1: 64}, "independent-source fringe did not disappear")
    return {"scope": __doc__ or "", "main_launches_per_backend": launches,
            "raw_contacts": dict(contacts), "max_touched_cells_per_launch": dict(peak_cells),
            "D0_per_16_by_difference": fringe, "shared_stock_removed_checks": 64,
            "independent_source_B_launches": 64 * 128, "restricted_walls": walls,
            "marker_encoding": "invertible conjugate of spectator register",
            "one_arm_full_or_return_D0_D1_dump_per_16": (4, 4, 8),
            "one_arm_token_only": "half of both open counts at each setting; 8 in dump"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = verify()
    if args.json:
        print(json.dumps(report, sort_keys=True))
    else:
        print("D0 per 16 launches:", report["D0_per_16_by_difference"])
        print("Main launches per backend:", report["main_launches_per_backend"],
              "; raw contacts:", report["raw_contacts"])
        print("Supplied fair stock, chronological settings, shutter topology and token meter.")
        print("Classical triangle: adjacent settings give 3/4, not the cosine-squared target.")
