"""Verify an exact cut-space distance for the fixed measured ASI replay.

The certificate concerns binary transition labels, not errors, their
probabilities, or a reconstruction of microscopic dynamics. No optimizer runs.
"""

from __future__ import annotations

import hashlib
import json
import math
import sys
from collections import Counter, defaultdict, deque
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts import probe_measured_asi_loop_parity as measured

REPLAY_SHA256 = "ba47eeb7cc36be3a8c87294d3738b52900dfcbf6eb0bc86f0c85f2f5942efb2b"
# fmt: off
FACE_GROUPS = (
    *((i,) for i in (2, 3, 9, 14, 23, 26, 75, 80, 85, 109, 118, 131, 135,
                     149, 154, 156, 157, 159, 182, 185, 186, 187, 194, 231)),
    (89, 93, 103),
    (117, 121, 136),
)
TOGGLE_ROWS = (
    11, 37, 61, 102, 114, 172, 323, 353, 370, 440, 458, 470, 520, 573, 578,
    608, 615, 656, 663, 666, 691, 752, 787, 790, 794, 829, 830, 973,
)
# fmt: on


@dataclass(frozen=True)
class InferredGraph:
    islands: tuple[measured.Island, ...]
    edge_ends: tuple[tuple[int, int], ...]
    adjacent: dict[int, dict[int, int]]  # vertex -> neighbor -> island index
    face_edges: tuple[tuple[int, ...], ...]

    @property
    def labels(self) -> dict[int, bool]:
        return {
            s.first: s.flip
            for s in self.islands
            if s.first is not None and s.flip is not None
        }

    @property
    def face_rows(self) -> tuple[tuple[int, ...], ...]:
        """Face IDs are 1-based lexicographic ranks of sorted frame-000 rows."""
        supports = []
        for boundary in self.face_edges:
            rows = []
            for edge in boundary:
                row = self.islands[edge].first
                if row is None:
                    raise ValueError("bounded simple face has an island missing in 000")
                rows.append(row)
            supports.append(tuple(sorted(rows)))
        return tuple(sorted(supports))

    def odd_faces(self) -> tuple[bool, ...]:
        labels = self.labels
        parity = []
        for rows in self.face_rows:
            if not set(rows).issubset(labels):
                raise ValueError("bounded simple face has an unknown transition label")
            parity.append(sum(labels[row] for row in rows) % 2 == 1)
        return tuple(parity)


def build_graph(islands: Sequence[measured.Island]) -> InferredGraph:
    """Same endpoint/embedding rules as measured.faces, retaining each circuit."""
    endpoints = [
        (s.center[0] + dx, s.center[1] + dx * s.axis)
        for s in islands
        for dx in (-11.75, 11.75)
    ]
    groups = measured.Groups(len(endpoints))
    for i, j in measured.near_pairs(endpoints, endpoints, 4.0):
        if i < j:
            groups.join(i, j)
    members: defaultdict[int, list[measured.Point]] = defaultdict(list)
    for i, p in enumerate(endpoints):
        members[groups.find(i)].append(p)
    centers = {
        v: (
            sum(x for x, _ in points) / len(points),
            sum(y for _, y in points) / len(points),
        )
        for v, points in members.items()
    }
    adjacent: dict[int, dict[int, int]] = {v: {} for v in centers}
    edges = []
    for i in range(len(islands)):
        u, v = groups.find(2 * i), groups.find(2 * i + 1)
        if u == v or v in adjacent[u]:
            raise ValueError("endpoint clustering produced a self/parallel edge")
        edges.append((u, v))
        adjacent[u][v] = adjacent[v][u] = i
    if next(measured.intersections(centers, edges), None) is not None:
        raise ValueError("primary embedding has crossing edges")

    rotation = {}
    for v, neighbors in adjacent.items():
        x, y = centers[v]
        rotation[v] = sorted(
            neighbors, key=lambda w: math.atan2(centers[w][1] - y, centers[w][0] - x)
        )
    seen: set[tuple[int, int]] = set()
    faces = []
    for start in ((u, v) for u, neighbors in adjacent.items() for v in neighbors):
        if start in seen:
            continue
        u, v = start
        walk = []
        boundary = []
        twice_area = 0.0
        while (u, v) not in seen:
            seen.add((u, v))
            walk.append(u)
            boundary.append(adjacent[u][v])
            x, y = centers[u]
            xx, yy = centers[v]
            twice_area += x * yy - xx * y
            u, v = v, rotation[v][rotation[v].index(u) - 1]
        if (u, v) != start:
            raise ValueError("half-edge traversal failed to close at its start")
        if twice_area > 0 and len(set(walk)) == len(walk):
            faces.append(tuple(boundary))
    return InferredGraph(tuple(islands), tuple(edges), adjacent, tuple(faces))


@dataclass(frozen=True)
class PackingBound:
    minimum: int
    capacities: tuple[int, ...]


def verify_packing(
    graph: InferredGraph, face_groups: Sequence[tuple[int, ...]]
) -> PackingBound:
    """Every odd face must be hit; each row's capacity is local to one group."""
    supported_rows: set[int] = set()
    faces, odd = graph.face_rows, graph.odd_faces()
    minimum = 0
    capacities = []
    for group in face_groups:
        if not group or len(set(group)) != len(group):
            raise ValueError("face group must contain distinct face IDs")
        hits: Counter[int] = Counter()
        for face_id in group:
            if not 1 <= face_id <= len(faces):
                raise ValueError(f"unknown face ID {face_id}")
            if not odd[face_id - 1]:
                raise ValueError(f"face {face_id} is not odd")
            hits.update(faces[face_id - 1])
        if not supported_rows.isdisjoint(hits):
            raise ValueError("face groups do not have disjoint row supports")
        supported_rows.update(hits)
        capacity = max(hits.values())
        capacities.append(capacity)
        minimum += (len(group) + capacity - 1) // capacity
    return PackingBound(minimum, tuple(capacities))


def unknown_bridge_rows(graph: InferredGraph) -> tuple[int, ...]:
    """Check unknown edges against the full graph, without assigning a label."""
    rows = []
    for edge, s in enumerate(graph.islands):
        if s.flip is not None:
            continue
        u, v = graph.edge_ends[edge]
        seen = {u}
        pending = deque([u])
        while pending:
            w = pending.popleft()
            for z, step in graph.adjacent[w].items():
                if step != edge and z not in seen:
                    seen.add(z)
                    pending.append(z)
        if v in seen:
            raise ValueError("an unknown transition is not on a bridge")
        if s.first is not None or s.second is None:
            raise ValueError("unknown bridge is not a frame-001-only row")
        rows.append(s.second)
    return tuple(sorted(rows))


@dataclass(frozen=True)
class CutWitness:
    checked_edges: int
    assigned_vertices: int
    known_components: int


def verify_cut(graph: InferredGraph, toggle_rows: Sequence[int]) -> CutWitness:
    """Integrate corrected known labels by BFS and check every known edge."""
    toggles = set(toggle_rows)
    if len(toggles) != len(toggle_rows):
        raise ValueError("duplicate toggle row")
    if not toggles <= graph.labels.keys():
        raise ValueError("toggle rows must be known frame-000 transition labels")
    corrected = {
        i: s.flip ^ (s.first in toggles)
        for i, s in enumerate(graph.islands)
        if s.flip is not None
    }
    potentials: dict[int, bool] = {}
    known_components = 0
    for root in graph.adjacent:
        if root in potentials:
            continue
        known_components += 1
        potentials[root] = False
        pending = deque([root])
        while pending:
            u = pending.popleft()
            for v, edge in graph.adjacent[u].items():
                if edge in corrected and v not in potentials:
                    potentials[v] = potentials[u] ^ corrected[edge]
                    pending.append(v)
    for edge, label in corrected.items():
        u, v = graph.edge_ends[edge]
        if (potentials[u] ^ potentials[v]) != label:
            raise ValueError(
                f"corrected labels are not a cut at row {graph.islands[edge].first}"
            )
    return CutWitness(len(corrected), len(potentials), known_components)


def asynchronous_countercontrol() -> dict[str, object]:
    """A four-edge cycle, a whole star at vertex 0, and exact time-indexed reads."""
    cycle = ((0, 1), (1, 2), (2, 3), (3, 0))
    initial = (0,) * len(cycle)
    star_vertex = 0
    after_star = tuple(
        bit ^ (star_vertex in edge) for edge, bit in zip(cycle, initial, strict=True)
    )
    states = (initial, initial, after_star)  # sole update: after t=1, before t=2
    first_times = (0, 0, 0, 0)
    second_times = (2, 2, 2, 1)
    observed_delta = tuple(
        states[a][i] ^ states[b][i]
        for i, (a, b) in enumerate(zip(first_times, second_times, strict=True))
    )
    return {
        "cycle_edges_in_bit_order": cycle,
        "whole_star_vertex_between_times_1_and_2": star_vertex,
        "instantaneous_edge_bits": states,
        "instantaneous_cycle_parities": tuple(sum(state) % 2 for state in states),
        "first_sample_times": first_times,
        "second_sample_times": second_times,
        "observed_transition_bits": observed_delta,
        "observed_cycle_parity": sum(observed_delta) % 2,
        "scope": "Synthetic time-indexed readout only; not an XMCD measurement model.",
    }


def report() -> dict[str, object]:
    digest = hashlib.sha256(Path(measured.__file__).read_bytes()).hexdigest()
    if digest != REPLAY_SHA256:
        raise ValueError("frozen measured ASI replay source SHA-256 mismatch")
    graph = build_graph(measured.match(*measured.load_frames()))
    unknown_rows = unknown_bridge_rows(graph)
    lower = verify_packing(graph, FACE_GROUPS)
    upper = verify_cut(graph, TOGGLE_ROWS)
    if lower.minimum != len(TOGGLE_ROWS):
        raise ValueError("certificate bounds do not agree")
    return {
        "schema": "measured_asi_cut_distance_v1",
        "frame_sha256": measured.HASHES,
        "measured_replay_source_sha256": digest,
        "bounded_simple_faces": len(graph.face_rows),
        "original_changed_labels": sum(graph.labels.values()),
        "original_odd_faces": sum(graph.odd_faces()),
        "minimum_known_label_changes": lower.minimum,
        "lower_bound_certificate": {
            "face_id_convention": "1-based lexicographic rank of sorted 1-based frame-000 rows",
            "odd_face_groups_with_disjoint_row_supports": FACE_GROUPS,
            "max_faces_hit_by_one_row_in_each_group": lower.capacities,
        },
        "upper_bound_certificate": {
            "toggle_frame_000_rows": TOGGLE_ROWS,
            "known_edges_xor_checked": upper.checked_edges,
            "vertices_assigned_potentials": upper.assigned_vertices,
            "known_edge_components": upper.known_components,
        },
        "only_001_unknown_bridge_rows": unknown_rows,
        "asynchronous_countercontrol": asynchronous_countercontrol(),
        "claim_boundary": (
            "Exact Hamming distance for known binary transition labels on the primary inferred graph "
            "to the unrestricted whole-star cut space. Unknown bridge labels are not assigned. "
            "This is not a calibrated classification error estimate, evidence about hidden edges, "
            "or sufficiency for guarded (e.g. half-filled) star dynamics."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(report(), sort_keys=True, indent=2))
