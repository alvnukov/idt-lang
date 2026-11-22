"""Check exact supplied contact populations, not sampled counts or fitted data.

Input schema idt-contact-tomogram/1: rails is an ordered list of 2..8 unique
names; edges and each measurements row's pair use increasing rail-list order.
Each unordered pair needs exactly one {"pair":[name,name],"h":"p/q"} row.
Integers are allowed; floats and booleans are not. Programs use deterministic
sorted-neighbor shortest paths from probe_connected_contact_tomography.

Compatibility means one centered trace-one real PSD second moment fits these
supplied exact populations under the calibrated contact/stock contract. It
does not certify physical devices, drift-free sampling, a unique ensemble,
imaginary moments, topology, absolute scale, or a generic candidate verdict.
CLI exits: 0 compatible, 1 incompatible exact table, 2 malformed input.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import re
import sys

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_connected_contact_tomography import connected, path_between

SCHEMA = "idt-contact-tomogram/1"
BOUNDARY = ("exact_supplied_populations_not_sampled_counts; one_path_compatible_only; "
            "calibrated_contacts_stock_and_reproducibility_assumed; "
            "no_unique_physics_ensemble_or_imaginary_moment; no_empirical_candidate_verdict")


def fields(value, keys):
    if type(value) is not dict or set(value) != set(keys):
        raise ValueError("unexpected object fields")
    return value


def rational(value):
    if type(value) is int:
        if len(str(value)) > 256:
            raise ValueError("rational integer too large")
        return F(value)
    if type(value) is not str or len(value) > 513 or not re.fullmatch(r"-?[0-9]+(?:/[1-9][0-9]*)?", value):
        raise ValueError("h must be an exact integer or rational string with positive denominator")
    return F(value)


def psd_rank(matrix):
    """Exact symmetric Schur elimination, including singular zero pivots.

    Returns (PSD, rank) with rank None when the matrix is not PSD.
    A zero diagonal with a nonzero off-diagonal violates PSD, not a pivot
    to divide by or silently skip.
    """
    a = [list(map(F, row)) for row in matrix]
    n = len(a)
    if any(len(row) != n for row in a) or any(a[i][j] != a[j][i] for i in range(n) for j in range(n)):
        raise ValueError("PSD check needs a symmetric square matrix")
    rank = 0
    for k in range(n):
        pivot = a[k][k]
        if pivot < 0:
            return False, None
        if pivot == 0:
            if any(a[k][j] for j in range(k+1, n)):
                return False, None
            continue
        rank += 1
        for i in range(k+1, n):
            for j in range(i, n):
                a[i][j] -= a[i][k]*a[k][j]/pivot
                a[j][i] = a[i][j]
    return True, rank


def algebraic_rank(matrix):
    a = [list(row) for row in matrix]
    rank = 0
    for j in range(len(a)):
        pivot = next((i for i in range(rank, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        for i in range(rank+1, len(a)):
            ratio = a[i][j]/a[rank][j]
            a[i] = [x-ratio*y for x, y in zip(a[i], a[rank], strict=True)]
        rank += 1
    return rank


def check_tomogram(value):
    row = fields(value, ("schema", "rails", "edges", "measurements"))
    if row["schema"] != SCHEMA:
        raise ValueError("wrong contact tomogram schema")
    rails = row["rails"]
    if (type(rails) is not list or not 2 <= len(rails) <= 8
            or any(type(x) is not str or not x or len(x) > 64 for x in rails)
            or len(set(rails)) != len(rails)):
        raise ValueError("rails must be 2..8 unique nonempty names")
    n = len(rails)
    index = {name: i for i, name in enumerate(rails)}

    def pair(value):
        if type(value) is not list or len(value) != 2 or any(type(x) is not str or x not in index for x in value):
            raise ValueError("pair must name two declared rails")
        i, j = map(index.__getitem__, value)
        if i >= j:
            raise ValueError("pair must use strictly increasing declared rail order")
        return i, j

    if type(row["edges"]) is not list:
        raise ValueError("edges must be an array")
    edges = [pair(p) for p in row["edges"]]
    if len(set(edges)) != len(edges):
        raise ValueError("duplicate edge")
    graph = connected(n, edges)
    # The frozen constructor sorts every neighbor list; its BFS therefore
    # fixes shortest-path ties independently of edge input order.
    paths = [path_between(graph, i, j) for i in range(n) for j in range(i+1, n)]
    paths.sort(key=lambda p: (len(p), p[0], p[-1]))
    if type(row["measurements"]) is not list:
        raise ValueError("measurements must be an array")
    observed = {}
    for entry in row["measurements"]:
        entry = fields(entry, ("pair", "h"))
        key, h = pair(entry["pair"]), rational(entry["h"])
        if key in observed:
            raise ValueError("duplicate measurement pair")
        if not 0 <= h <= 1:
            raise ValueError("population h must lie in [0,1]")
        observed[key] = h
    if len(observed) != n*(n-1)//2:
        raise ValueError("one measurement required for every unordered pair")
    d = [[F(0)]*n for _ in range(n)]
    for path in paths:
        i, j = path[0], path[-1]
        steps = len(path)-2
        stopped = sum((d[i][path[r]] / 2**(r+1) for r in range(1, steps+1)), F(0))
        d[i][j] = d[j][i] = 2**(steps+1)*(observed[i, j]-stopped)
    means = [sum(r)/n for r in d]
    mean = sum(means)/n
    moment = [[-(d[i][j]-means[i]-means[j]+mean)/2 for j in range(n)] for i in range(n)]
    trace = sum(moment[i][i] for i in range(n))
    psd, rank = psd_rank(moment)
    if not psd:
        rank = algebraic_rank(moment)
    centered = all(sum(r) == 0 for r in moment)
    # Forward replay independently uses the reconstructed moment distances.
    replay = []
    for path in paths:
        i, j = path[0], path[-1]
        steps = len(path)-2
        distance = lambda b: moment[i][i]+moment[b][b]-2*moment[i][b]
        predicted = sum((distance(path[r])/2**(r+1) for r in range(1, steps+1)), F(0))
        predicted += distance(j)/2**(steps+1)
        replay.append(predicted == observed[i, j])
    consistent = all(replay)
    return {"schema": SCHEMA, "compatible": psd and trace == 1 and centered and consistent,
            "trace": str(trace), "positive_semidefinite": psd, "rank": rank,
            "centered": centered, "all_input_consistent": consistent,
            "moment": [[str(x) for x in r] for r in moment],
            "programs": [{"pair": [rails[p[0]], rails[p[-1]]], "path": [rails[i] for i in p]}
                         for p in paths], "scope": BOUNDARY}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path, help="JSON exact population table")
    args = parser.parse_args(argv)
    try:
        if args.table.stat().st_size > 1_000_000:
            raise ValueError("table exceeds one megabyte")
        def unique_object(items):
            result = {}
            for key, value in items:
                if key in result:
                    raise ValueError("duplicate JSON object key")
                result[key] = value
            return result
        result = check_tomogram(json.loads(args.table.read_text(), object_pairs_hook=unique_object))
        print(json.dumps(result, sort_keys=True))
        return 0 if result["compatible"] else 1
    except (OSError, ValueError, TypeError, KeyError) as exc:
        print(json.dumps({"error": str(exc), "scope": BOUNDARY}), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
