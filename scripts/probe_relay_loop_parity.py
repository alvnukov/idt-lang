"""Exact Z2 connections on supplied finite relays; signs are not amplitudes.

A static bit is attached to each undirected edge. Crossing it XORs that bit
into a carried bit. Native relay endpoints and distances are unchanged.
Require odd parity on every rooted abcabc circuit with distinct port names.
This tests an additional connection rule, not interference, clicks or Born.
"""

from __future__ import annotations

import hashlib
import json
import sys
from itertools import permutations, product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.probe_minimal_signal_relay import (
    Relay,
    cyclic_26,
    quotient_4,
)

Edge = tuple[int, int]
Face = tuple[int, tuple[int, ...]]
Row = tuple[int, int, int]
PORTS = tuple(range(4))
TRIPLES = tuple(permutations(PORTS, 3))
SOURCE = ROOT / "scripts/probe_minimal_signal_relay.py"


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def add_basis(vector: int, basis: dict[int, int]) -> bool:
    while vector:
        pivot = (vector & -vector).bit_length() - 1
        if pivot not in basis:
            basis[pivot] = vector
            return True
        vector ^= basis[pivot]
    return False


def eliminate(masks: list[int]) -> tuple[dict[int, Row], int | None]:
    basis: dict[int, Row] = {}
    contradiction = None
    for i, mask in enumerate(masks):
        rhs, provenance = 1, 1 << i
        while mask:
            pivot = (mask & -mask).bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (mask, rhs, provenance)
                break
            row, value, origin = basis[pivot]
            mask ^= row
            rhs ^= value
            provenance ^= origin
        if not mask and rhs and contradiction is None:
            contradiction = provenance
    return basis, contradiction


def solve(basis: dict[int, Row], initial: int = 0, homogeneous: bool = False) -> int:
    answer = initial
    for pivot in sorted(basis, reverse=True):
        row, rhs, _ = basis[pivot]
        bit = (row & answer).bit_count() % 2
        if not homogeneous:
            bit ^= rhs
        if bit:
            answer ^= 1 << pivot
    return answer


def edge_key(a: int, b: int) -> Edge:
    return (min(a, b), max(a, b))


def carried_walk(relay: Relay, indices: dict[Edge, int], connection: int,
                 start: int, word: tuple[int, ...]) -> tuple[int, int]:
    site, bit = start, 0
    for port in word:
        target = relay.neighbors[site][port]
        bit ^= (connection >> indices[edge_key(site, target)]) & 1
        site = target
    return site, bit


def certificate_rows(certificate: int, masks: list[int]) -> list[int]:
    selected = [i for i in range(len(masks)) if certificate >> i & 1]
    total = 0
    for i in selected:
        total ^= masks[i]
    need(total == 0 and len(selected) % 2 == 1, "invalid odd XOR contradiction certificate")
    return selected


def analyze(relay: Relay) -> dict[str, object]:
    frozen_neighbors = relay.neighbors
    vertices = len(relay.neighbors)
    edges = tuple(sorted({edge_key(s, t) for s, row in enumerate(relay.neighbors) for t in row}))
    indices = {e: i for i, e in enumerate(edges)}
    need(len(edges) == 2 * vertices, "degree-four edge count")
    for s, row in enumerate(relay.neighbors):
        need(len(set(row)) == 4 and s not in row, "simple four-port relay")
        for p, t in enumerate(row):
            need(relay.neighbors[t][p] == s, "reciprocal port")
    faces: list[Face] = []
    masks: list[int] = []
    for start in range(vertices):
        for triple in TRIPLES:
            word = triple * 2
            site, mask = start, 0
            for p in word:
                target = relay.neighbors[site][p]
                mask ^= 1 << indices[edge_key(site, target)]
                site = target
            need(site == start, "nominated circuit is not closed")
            faces.append((start, triple))
            masks.append(mask)

    # Independent direct carried-bit controls: neither a flat connection nor
    # any of the sixteen port-only signs can create odd six-loop parity.
    for port_bits in product(range(2), repeat=4):
        connection = 0
        for site, row in enumerate(relay.neighbors):
            for p, target in enumerate(row):
                if port_bits[p]:
                    connection |= 1 << indices[edge_key(site, target)]
        need(all(carried_walk(relay, indices, connection, s, triple * 2) == (s, 0)
                 for s, triple in faces), "port-only signs unexpectedly produce odd flux")

    basis, contradiction = eliminate(masks)
    gauge_vectors = [sum(1 << i for i, edge in enumerate(edges) if vertex in edge)
                     for vertex in range(vertices)]
    gauge_basis: dict[int, int] = {}
    for vector in gauge_vectors:
        add_basis(vector, gauge_basis)
        need(all((vector & mask).bit_count() % 2 == 0 for mask in masks),
             "vertex gauge changes a closed circuit")
    need(len(gauge_basis) == vertices - 1, "connected vertex-gauge rank")
    report: dict[str, object] = {
        "name": relay.name, "vertices": vertices, "edges": len(edges),
        "rooted_face_constraints": len(faces), "distinct_edge_masks": len(set(masks)),
        "constraint_rank": len(basis), "vertex_gauge_rank": len(gauge_basis),
        "flat_and_all_16_port_only_connections": "even on every nominated loop",
        "solvable": contradiction is None,
    }
    if contradiction is not None:
        selected = certificate_rows(contradiction, masks)
        # A particularly transparent independent obstruction: the thirteen
        # A-site translates of one ordered triple cancel every edge mod two.
        transparent = [i for i, (s, t) in enumerate(faces)
                       if relay.role[s] == 0 and t == (0, 1, 2)]
        certificate_rows(sum(1 << i for i in transparent), masks)
        report["elimination_odd_certificate_size"] = len(selected)
        report["elimination_odd_certificate"] = [faces[i] for i in selected]
        report["transparent_odd_certificate"] = [faces[i] for i in transparent]
        report["certificate_meaning"] = "odd number of required ones XOR to zero edge boundary"
        need(vertices == 26 and len(transparent) == 13, "unexpected obstructed relay")
    else:
        particular = solve(basis)
        need(all((mask & particular).bit_count() % 2 == 1 for mask in masks),
             "particular solution failed matrix substitution")
        free = [i for i in range(len(edges)) if i not in basis]
        kernel = [solve(basis, 1 << i, homogeneous=True) for i in free]
        need(all(all((mask & vector).bit_count() % 2 == 0 for mask in masks)
                 for vector in kernel), "homogeneous basis substitution")
        quotient_basis = dict(gauge_basis)
        representatives: list[int] = []
        for vector in kernel:
            if add_basis(vector, quotient_basis):
                representatives.append(vector)
        need(len(quotient_basis) == len(edges) - len(basis), "gauge and quotient span kernel")
        need(len(representatives) == 3, "actual gauge-invariant freedom count")
        for choice in product(range(2), repeat=len(representatives)):
            connection = particular
            for bit, vector in zip(choice, representatives, strict=True):
                if bit:
                    connection ^= vector
            # This verification walks edges directly, independently of the
            # equation-mask evaluation used by Gaussian elimination.
            need(all(carried_walk(relay, indices, connection, s, t * 2) == (s, 1)
                     for s, t in faces), "direct walk rejected a gauge sector")
        report.update({"solution_affine_dimension": len(free),
                       "gauge_invariant_binary_freedoms": len(representatives),
                       "gauge_inequivalent_connections": 2 ** len(representatives),
                       "particular_edge_bitmask_hex": hex(particular),
                       "quotient_generators_hex": [hex(v) for v in representatives],
                       "edge_index": edges,
                       "all_eight_gauge_sectors_directly_verified": True})
    need(relay.neighbors == frozen_neighbors, "connection changed relay endpoints")
    return report


def main() -> None:
    source_sha = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    relays = (cyclic_26(), quotient_4((0, 1, 2, 3)), quotient_4((0, 2)))
    reports = [analyze(relay) for relay in relays]
    need(hashlib.sha256(SOURCE.read_bytes()).hexdigest() == source_sha,
         "imported relay source changed during the check")
    print(json.dumps({"source_sha256": source_sha, "relays": reports,
                      "boundaries": [
                          "A supplied Z2 edge connection reversibly flips a carried bit.",
                          "Odd elementary-loop parity is an imposed test, not a derived law.",
                          "Gauge inequivalence is algebraic freedom, not physical evidence.",
                          "All underlying relay endpoints and graph distances are unchanged.",
                          "Connection signs are not amplitudes or clicks; no interference/Born/QM derivation.",
                      ]}, indent=2))


if __name__ == "__main__":
    main()
