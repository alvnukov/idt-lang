"""Conditional selection among anonymous reversible involutive ternary contacts.

Each experiment supplies its own finite sites, graph, ordinary initial stock
and finite word of contacts. Within that experiment the word, stock (apart
from the specified input or control), physical ports and observation time are
identical across trials. The three experiments need not use the same fixture.

Route: start one T at a fixed site. Can varying one separately prepared
ordinary control change its final physical port? Transfer: with *no T
anywhere*, can changing one ordinary source change another site's raw shade?
Record: with private input x=a,b,T and otherwise common ordinary stock, can
we restore x and leave ordinary flags identical on both misses and different
on the hit? Our positive witnesses even restore scratch stock, protect both
flags from T throughout, and erase by the reversed word; the exclusion needs
only ordinary flags at final read time.

Every exclusion below is a checked one-contact identity that composes on any
fixed word; it is not a failure to find a short working word. These are
post-hoc operational requirements suggested by a known candidate, not a
prediction or an empirical requirement. The supplied alphabet, conserved T,
pair arity, anonymity, involution and experimental resources are assumptions.
No universal minimality, autonomous detector, emergent geometry, or physics
claim follows. Run: python3 -m scripts.probe_ternary_operational_selection.
"""

import argparse
import json
from itertools import permutations, product


PAIRS = tuple(map("".join, product("abT", repeat=2)))
INDEX = {pair: i for i, pair in enumerate(PAIRS)}
FLIP = str.maketrans("ab", "ba")  # fixes T
EDGE = ((0, 1),)
# Slots 0 = private input, 1 and 2 = ordinary flags; optional slot 3 = catalyst.
CS_METER = ((0, 3), (0, 1), (0, 3), (2, 3), (1, 2))
C_METER = ((0, 1), (0, 2), (1, 2))
PARKED_METER = ((0, 1), (0, 2)) * 3


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def enumerate_laws():
    """Start from all 9! raw permutations, not preclassified sectors."""
    reverse = tuple(INDEX[p[::-1]] for p in PAIRS)
    count = tuple(p.count("T") for p in PAIRS)
    checked, accepted = 0, []
    for im in permutations(range(len(PAIRS))):
        checked += 1
        if im[INDEX["TT"]] != INDEX["TT"]:
            continue
        if all(count[i] == count[j] and im[j] == i and im[reverse[i]] == reverse[j]
               for i, j in enumerate(im)):
            accepted.append(tuple(PAIRS[j] for j in im))
    return checked, accepted


def replay(images, state, word):
    raw = list(state)
    trace = [state]
    for i, j in word:
        raw[i], raw[j] = images[INDEX[raw[i] + raw[j]]]
        trace.append("".join(raw))
    return trace


def name_law(table):
    blank = {tuple(p for p in ("aa", "ab", "ba", "bb")): "identity",
             ("aa", "ba", "ab", "bb"): "swap",
             ("bb", "ba", "ab", "aa"): "complement",
             ("bb", "ab", "ba", "aa"): "complement-swap"}
    zero = blank[tuple(table[p] for p in ("aa", "ab", "ba", "bb"))]
    moving = "".join(c for c in "ab" if table["T" + c][1] == "T")
    if "b" in table["Ta"]:
        mode = "exchange/move" if moving else "exchange/hold"
    else:
        mode = moving or "hold"
    return f"{zero}/{mode}"


def routing(images, table):
    # Same input port and word; only the separate ordinary control changes.
    ports = [replay(images, "T" + c, EDGE)[-1].index("T") for c in "ab"]
    if ports[0] != ports[1]:
        return "witness"
    # Therefore, on each scheduled edge the occupancy either always swaps
    # or always stays. Composition cannot see the ordinary controls.
    moves = ports[0] == 1
    for p, q in table.items():
        src = p[::-1] if moves else p
        require([c == "T" for c in src] == [c == "T" for c in q],
                "missing single-edge T-occupancy certificate")
    return "always_move" if moves else "always_hold"


def transfer(images, table):
    received = [replay(images, c + "a", EDGE)[-1][1] for c in "ab"]
    if received[0] != received[1]:
        return "witness"
    # Each output is its own input, possibly toggled. On arbitrary common
    # stock the final value depends only on that site's initial shade and
    # its fixed contact-count parity, not another site's initial shade.
    flips = received[0] == "b"
    for p in ("aa", "ab", "ba", "bb"):
        require(table[p] == (p.translate(FLIP) if flips else p),
                "missing blank-only site-local certificate")
    return "self_complement" if flips else "self_only"


def dye_obstruction(table, dye):
    # The indicator for the passable shade is permuted by the word itself.
    # T and the nonpassable ordinary shade have identical indicator vectors
    # when substituted for the private input, for *any* common ordinary
    # stock. Final flags restricted to ordinary shades are determined by that
    # indicator; they cannot differ between the T row and this miss row.
    for p, q in table.items():
        require([c == dye for c in q] == [c == dye for c in p[::-1]],
                "missing passive-dye obstruction")


def record_witness(images, stock, word):
    finals = []
    for x in "abT":
        initial = x + stock
        trace = replay(images, initial, word)
        flags = stock[:2].translate(FLIP) if x == "T" else stock[:2]
        require(trace[-1] == x + flags + stock[2:], "record or restoration failed")
        require(all("T" not in step[1:3] for step in trace), "exposed flag")
        require(replay(images, trace[-1], reversed(word)) == trace[::-1], "erasure failed")
        finals.append(trace[-1])
    return {"stock": stock, "word": word, "finals": finals}


def verify():
    checked, laws = enumerate_laws()
    rows = {}
    for im in laws:
        table = dict(zip(PAIRS, im, strict=True))
        name = name_law(table)
        row = {"law": name, "images": im, "route": routing(im, table),
               "transfer": transfer(im, table), "record": "not_evaluated"}
        require(name not in rows, "law name collision")
        if row["route"] == row["transfer"] == "witness":
            dye = name.rsplit("/", 1)[-1]
            require(dye in ("a", "b"), "unexpected selective mixed sector")
            if name.startswith("swap/"):
                dye_obstruction(table, dye)
                row.update(record="passive_dye", dye=dye)
            else:
                stock = "bba" if dye == "a" else "aab"
                row.update(record="witness", record_witness=record_witness(im, stock, CS_METER))
        elif name in ("complement/a", "swap/exchange/hold"):
            # Drop-one controls. In the star word the blank transpositions
            # form a 3-cycle repeated three times; parked T instead flips
            # each of its ordinary neighbors three times.
            word = C_METER if name == "complement/a" else PARKED_METER
            row.update(record="witness", record_witness=record_witness(im, "bb", word))
        rows[name] = row

    required = ("route", "transfer", "record")
    surviving = list(rows)
    counts = [len(surviving)]
    for cap in required:
        surviving = [k for k in surviving if rows[k][cap] == "witness"]
        counts.append(len(surviving))
    require(checked == 362880 and counts == [24, 8, 4, 2], "unexpected census")
    one, other = [rows[k]["images"] for k in sorted(surviving)]
    require(all(one[INDEX[p.translate(FLIP)]].translate(FLIP) == q
                for p, q in zip(PAIRS, other, strict=True)), "not one shade-relabeling orbit")
    drop = {"route": "swap/exchange/hold", "transfer": "complement/a", "record": "swap/a"}
    for omitted, name in drop.items():
        failed = {cap for cap in required if rows[name][cap] != "witness"}
        require(failed == {omitted} and rows[name][omitted] != "not_evaluated",
                "drop-one control is not separated")
    return {"permutations_checked": checked, "pair_order": PAIRS, "successive_counts": counts,
            "filter_order": required, "survivor_orbit": sorted(surviving), "drop_one": drop,
            "rows": [rows[k] for k in sorted(rows)],
            "scope": "Post-hoc fixed-word all-stock capabilities in the specified ternary class only.",
            "not_evaluable": "Hidden auxiliary tokens, adaptive schedules, other arities or laws, "
                             "and differently encoded inputs or composite flags are outside this test."}


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true")
    if parser.parse_args().json:
        print(json.dumps(verify(), sort_keys=True))
    else:
        result = verify()
        print("Raw laws -> route -> blank transfer -> record:", *result["successive_counts"])
        print("One shade-relabeling orbit:", ", ".join(result["survivor_orbit"]))
        print(result["scope"])


if __name__ == "__main__":
    main()
