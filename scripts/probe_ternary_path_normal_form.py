"""Exact reachability for the supplied CS rule on a fixed, labelled open path.

Run: python3 -m scripts.probe_ternary_path_normal_form --json

The only changes are aa <-> bb and Ta <-> aT. Write z for the physical
pair aa = bb. It commutes with each cell: aaa needs no change, baa -> bbb
-> aab, Taa -> aTa -> aaT. Modulo these parked pairs an ordinary b is an
involution and each {a,T} factor is a^e T^m (e = 0 or 1). Read left to
right, storing alternating b and nonidentity {a,T} factors. Reading either
ordinary letter twice restores any stack; reading a then T acts exactly as
T then a, including when a removes the top factor. Thus every native contact
preserves the final stack in every prefix/suffix context.

Conversely, maintain a raw prefix z^k followed by its reduced stack in word
form. On a new a, move it left over trailing Ts; an exposed aa is parked at
the front. On a new b, an exposed bb is changed to aa and parked. Otherwise
append the factor; T never cancels. This induction uses only physical edges
and ends at z^k times the skeleton, with 2k = length - skeleton length. Hence
the skeleton and length distinguish components in both directions. A skeleton
avoids aa, bb and Ta, so has three choices initially and two at each further
site; summing lengths of the required parity gives 2^(n+1)-1 components.

This is a combinatorial argument plus an executable check, not a Lean proof
or an inferred physical law. The path, rule and freedom to choose contacts
are supplied. Accessibility is neither a specified dynamics nor a rate.
"""

import argparse
import json
from collections import deque
from dataclasses import dataclass
from itertools import product

from scripts.probe_ternary_active_readout import contact, replay as native_replay


@dataclass(frozen=True)
class NormalForm:
    pairs: int
    skeleton: str

    def representative(self):
        return "aa" * self.pairs + self.skeleton


def normal_form(word, counts=None):
    """Linear number of word/stack operations; no search or physical replay."""
    stack = []  # None = b, (bit, number of Ts) = nontrivial {a,T} factor.
    for x in word:
        if counts is not None:
            counts["symbol_reads"] = counts.get("symbol_reads", 0) + 1
        if x == "b":
            if stack and stack[-1] is None:
                stack.pop()
            else:
                stack.append(None)
        elif x == "a" or x == "T":
            e, m = stack.pop() if stack and stack[-1] is not None else (0, 0)
            if x == "a":
                e ^= 1
            else:
                m += 1
            if e or m:
                stack.append((e, m))
        else:
            raise ValueError(f"not a CS cell: {x!r}")
    s = "".join("b" if f is None else "a" * f[0] + "T" * f[1] for f in stack)
    return NormalForm((len(word) - len(s)) // 2, s)


def reachable(source, target):
    return normal_form(source) == normal_form(target)


def reduction_trace(word):
    """Native changing edge indices to the representative (not a shortest path)."""
    state = list(word)
    trace = []
    parked = 0  # number of prefix sites, not number of pairs

    def fire(i):
        old = state[i], state[i + 1]
        new = contact(*old)
        if new == old:
            raise AssertionError(("inactive contact", i))
        state[i], state[i + 1] = new
        trace.append(i)

    for end, x in enumerate(word):
        i = end
        if x == "a":
            while i > parked and state[i - 1] == "T":
                fire(i - 1)
                i -= 1
        elif x not in ("b", "T"):
            raise ValueError(f"not a CS cell: {x!r}")
        if x == "T" or i == parked or state[i - 1] != x:
            continue
        i -= 1
        if x == "b":
            fire(i)  # bb -> aa
        while i > parked:
            left = state[i - 1]
            if left == "T":
                fire(i - 1)
                fire(i)
            elif left == "b":
                fire(i)
                fire(i - 1)
            # In aaa, reinterpret the identical aa one site to the left.
            i -= 1
        parked += 2
    return tuple(trace)


def witness(source, target):
    """None for different components; otherwise a reversible native contact word."""
    if not reachable(source, target):
        return None
    return reduction_trace(source) + reduction_trace(target)[::-1]


def tag_intervals(word):
    """All reachable sites per T in its unchanging left-to-right order.

    For A factor a^e T^m between skeleton pieces P and Q, split any raw
    representative at T number j in this block (j starts at zero). This T
    cannot cancel: reducing the two sides can merge their terminal/initial
    A factors into its A factor, but never cancels a b across it. Thus the
    raw left side must supply P and j earlier Ts, the right Q and m-1-j
    later Ts. Both bounds are attained: put all 2k parked as and the e
    optional a at either end of the block; moving them through its Ts
    realizes every intermediate site. Marginal ranges, NOT joint independence.
    """
    nf = normal_form(word)
    s = nf.skeleton
    intervals = []
    i = 0
    while i < len(s):
        if s[i] != "T":
            i += 1
            continue
        e = int(i > 0 and s[i - 1] == "a")
        while i < len(s) and s[i] == "T":
            intervals.append((i - e, i + 2 * nf.pairs))
            i += 1
    return tuple(intervals)


def raw_search(start, target=None):
    """Independent literal edge BFS. Count actual offered edges, including idle."""
    seen = {start}
    queue = deque([start])
    offers = 0
    while queue:
        s = queue.popleft()
        if s == target:
            break
        for i in range(len(s) - 1):
            offers += 1
            u, v = contact(s[i], s[i + 1])
            if u == s[i] and v == s[i + 1]:
                continue
            t = s[:i] + u + v + s[i + 2:]
            if t not in seen:
                seen.add(t)
                queue.append(t)
    return seen, offers


def census(n):
    """Check full partition AND per-rank T site masks against raw components."""
    if n < 0:
        raise ValueError("path length must be nonnegative")
    visited, keys = set(), set()
    offers, counts = 0, {}
    for word in map("".join, product("abT", repeat=n)):
        if word in visited:
            continue
        component, probes = raw_search(word)
        offers += probes
        key = None
        masks = [0] * word.count("T")
        for s in component:
            nf = normal_form(s, counts)
            if key is None:
                key = nf
            if nf != key:
                raise AssertionError(("native component split", word, s))
            j = 0
            for i, x in enumerate(s):
                if x == "T":
                    masks[j] |= 1 << i
                    j += 1
        if key in keys:
            raise AssertionError(("different components merged", key))
        keys.add(key)
        visited.update(component)
        ranges = [((1 << (hi - lo + 1)) - 1) << lo for lo, hi in tag_intervals(word)]
        if ranges != masks:
            raise AssertionError(("incorrect rank interval", word, ranges, masks))
    if len(keys) != 2 ** (n + 1) - 1 or len(visited) != 3 ** n:
        raise AssertionError(("incorrect census", n, len(keys), len(visited)))
    return {"length": n, "raw_states": len(visited), "components": len(keys),
            "bfs_edge_offers": offers, "classifier_symbol_reads": counts.get("symbol_reads", 0),
            "partition_and_tag_ranges_match": True}


def caging_control():
    """Same initial T site, full composition and staggered b charge; fixed site 0."""
    rows = []
    for word in ("bbTaa", "baTba"):
        component, _ = raw_search(word)
        sites = sorted({s.index("T") for s in component})
        lo, hi = tag_intervals(word)[0]
        if sites != list(range(lo, hi + 1)):
            raise AssertionError(("cage mismatch", word))
        rows.append({"initial": word, "skeleton": normal_form(word).skeleton,
                     "initial_T_site": word.index("T"), "counts_abT": list(map(word.count, "abT")),
                     "staggered_b": word[::2].count("b") - word[1::2].count("b"),
                     "component_size": len(component), "reachable_sites": sites,
                     "fixed_site_zero_accessible": 0 in sites})
    return rows


def schedule_control():
    """A changing loop can postpone a possible hit indefinitely (no fairness imposed)."""
    word = "bbTaa"
    loop, hit = (0, 0), (0, 1, 0)
    def history(indices):
        return native_replay(word, [(i, i + 1) for i in indices])

    cycle = history(loop)
    sites = [s.index("T") for s in cycle]
    if (cycle[0] != cycle[-1] or cycle[0] == cycle[1]
            or 0 in sites or history(hit)[-1][0] != "T"):
        raise AssertionError("active-loop versus hit control failed")
    return {"initial": word, "detector_site": 0, "repeating_edges": loop,
            "loop_tag_sites": sites, "hit_edges": hit}


def query_workloads():
    """Predefined positive/negative pair per size, same scan order in every BFS."""
    rows = []
    for h in (1, 2, 3):
        src = "bb" * h + "T" + "aa" * h
        for dst in ("T" + "a" * (4 * h), "baTba" + "aa" * (2 * h - 2)):
            counts = {}
            result = normal_form(src, counts) == normal_form(dst, counts)
            seen, offers = raw_search(src, dst)
            if result != (dst in seen):
                raise AssertionError(("query disagreement", src, dst))
            rows.append({"source": src, "target": dst, "length": len(src), "reachable": result,
                         "classifier_symbol_reads": counts["symbol_reads"],
                         "bfs_result": dst in seen, "bfs_discovered": len(seen),
                         "bfs_edge_offers": offers})
    return rows


def verify(max_length=9):
    if not 0 <= max_length <= 10:
        raise ValueError("exhaustive census supports lengths 0 through 10")
    # The last-to-first edge changes Tba -> abT in one native ring contact.
    if contact("a", "T") != ("T", "a") or reachable("Tba", "abT"):
        raise AssertionError("open-vs-wrap control failed")
    return {"census": [census(n) for n in range(max_length + 1)],
            "caging": caging_control(), "query_workloads": query_workloads(),
            "schedule_control": schedule_control(),
            "control": "Tba -> abT in one wrap contact; impossible on the fixed open path",
            "scope": "Supplied CS rule, open path and free choice of native edges; exact access, "
                     "not a prescribed wait, rate, shortest path, spatial reconstruction or Lean proof."}


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    cli.add_argument("--max-length", type=int, default=9, choices=range(11))
    cli.add_argument("--json", action="store_true")
    args = cli.parse_args()
    report = verify(args.max_length)
    print(json.dumps(report, indent=2 if args.json else None))
