"""Retrospective support test on the fixed Apamea inferred visible graph."""

from __future__ import annotations

import hashlib
import json
import sys
from collections import Counter, defaultdict, deque
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import TypedDict, cast

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts import probe_apamea_fixed_transfer as transfer
from scripts import probe_asi_cut_distance as cut
from scripts import probe_measured_asi_loop_parity as measured

Edge = tuple[int, int]


@dataclass(frozen=True)
class CoverCertificate:
    """Lower witness: disjoint changed edges; upper witness: covering sites."""

    matching: tuple[Edge, ...]
    cover: tuple[int, ...]


def _edge(u: int, v: int) -> Edge:
    if type(u) is not int or type(v) is not int or min(u, v) < 0 or u == v:
        raise ValueError("incidence edges need distinct nonnegative integer vertices")
    return (u, v) if u < v else (v, u)


def _simple_edges(edges: Iterable[Edge]) -> set[Edge]:
    seen: set[Edge] = set()
    for u, v in edges:
        e = _edge(u, v)
        if e in seen:
            raise ValueError("duplicate incidence edge")
        seen.add(e)
    return seen


def verify_certificate(edges: Iterable[Edge], cert: CoverCertificate) -> int:
    """Prove exactness from witnesses alone, with no solver or bipartite premise."""
    support = _simple_edges(edges)
    used: set[int] = set()
    for u, v in cert.matching:
        if _edge(u, v) not in support or u in used or v in used:
            raise ValueError("lower witness is not a matching of support edges")
        used.update((u, v))
    cover = set(cert.cover)
    sites = {v for edge in support for v in edge}
    if (
        any(type(v) is not int for v in cert.cover)
        or len(cover) != len(cert.cover)
        or not cover <= sites
        or any(u not in cover and v not in cover for u, v in support)
    ):
        raise ValueError("upper witness is not a cover by distinct support sites")
    if len(cert.matching) != len(cover):
        raise ValueError("incidence certificate bounds do not agree")
    return len(cover)


def _alternating_search(
    roots: Iterable[int],
    neighbors: dict[int, list[int]],
    matches: dict[int, int],
    reverse: dict[int, int],
) -> tuple[int | None, set[int], dict[int, int]]:
    """Search left-to-right on nonmatching edges and right-to-left on matches."""
    queue = deque(roots)
    visited_left = set(queue)
    right_parent: dict[int, int] = {}
    while queue:
        u = queue.popleft()
        for v in neighbors[u]:
            if v == matches.get(u) or v in right_parent:
                continue
            right_parent[v] = u
            mate = reverse.get(v)
            if mate is None:
                return v, visited_left, right_parent
            if mate not in visited_left:
                visited_left.add(mate)
                queue.append(mate)
    return None, visited_left, right_parent


def build_certificate(edges: Iterable[Edge]) -> CoverCertificate:
    """Find deterministic witnesses on checked bipartite support, fail otherwise."""
    support = _simple_edges(edges)
    neighbors: dict[int, list[int]] = defaultdict(list)
    for u, v in sorted(support):
        neighbors[u].append(v)
        neighbors[v].append(u)

    left: list[int] = []
    colors: dict[int, bool] = {}
    for root in sorted(neighbors):
        if root in colors:
            continue
        colors[root] = True
        queue = deque([root])
        while queue:
            u = queue.popleft()
            if colors[u]:
                left.append(u)
            for v in neighbors[u]:
                if v not in colors:
                    colors[v] = not colors[u]
                    queue.append(v)
                elif colors[v] == colors[u]:
                    raise ValueError("incidence support graph is not bipartite")

    matches: dict[int, int] = {}
    reverse: dict[int, int] = {}
    for root in sorted(left):
        free, _, parents = _alternating_search((root,), neighbors, matches, reverse)
        while free is not None:
            u = parents[free]
            previous = matches.get(u)
            matches[u] = free
            reverse[free] = u
            free = previous

    unmatched = sorted(set(left) - matches.keys())
    free, visited_left, right_parents = _alternating_search(
        unmatched, neighbors, matches, reverse
    )
    if free is not None:
        raise ValueError("matching still admits an augmenting path")
    cover = (set(left) - visited_left) | right_parents.keys()
    cert = CoverCertificate(
        tuple(sorted(_edge(u, v) for u, v in matches.items())), tuple(sorted(cover))
    )
    verify_certificate(support, cert)
    return cert


class EdgeTrace(TypedDict):
    frame_rows: tuple[int | None, int | None]
    endpoint_sites: Edge
    endpoint_degrees: tuple[int, int]
    bounded_simple_face_count: int


class Footprint(TypedDict):
    observed_reversals: int
    unsupported_observed_reversals: int
    unsupported_reversals_on_two_bounded_simple_faces: int
    minimum_non_fourfold_sites: int
    active_non_fourfold_sites: int
    total_non_fourfold_sites: int
    total_visible_sites: int
    known_edges_without_fourfold_endpoint: int
    unknown_edges_without_fourfold_endpoint: int
    known_transition_edges: int
    total_visible_edges: int
    reversed_edges: list[EdgeTrace]
    unknown_edges: list[EdgeTrace]
    matching_lower_bound_edge_endpoints: tuple[Edge, ...]
    cover_upper_bound_sites: tuple[int, ...]


def _check_same_geometry(graph: cut.InferredGraph, accepted: transfer.PairRow) -> None:
    """Fail closed if the trace builder diverges from the accepted primary census."""
    geometry = accepted["geometry"]
    if accepted["status"] != "usable" or accepted["reasons"] or geometry is None:
        raise ValueError("footprint requires an accepted primary geometry")
    labels = Counter(s.flip for s in graph.islands)
    flip_counts: Counter[int] = Counter()
    incomplete = 0
    for face in graph.face_edges:
        transitions = tuple(graph.islands[i].flip for i in face)
        if None in transitions:
            incomplete += 1
        else:
            flip_counts[sum(label is True for label in transitions)] += 1
    if (
        labels[True] != accepted["reversed_classifications"]
        or labels[True] + labels[False] != accepted["matched"]
        or sum(s.second is None for s in graph.islands) != accepted["only_first"]
        or sum(s.first is None for s in graph.islands) != accepted["only_second"]
        or len(graph.adjacent) != geometry["vertices"]
        or Counter(map(len, graph.adjacent.values())) != geometry["degrees"]
        or len(graph.face_edges) != geometry["bounded_simple_faces"]
        or Counter(map(len, graph.face_edges)) != geometry["size_histogram"]
        or flip_counts != geometry["flip_count_histogram"]
        or incomplete != geometry["incomplete"]
    ):
        raise ValueError("footprint graph disagrees with accepted primary census")


def analyze_usable_pair(
    a: Sequence[measured.Spin], b: Sequence[measured.Spin], accepted: transfer.PairRow
) -> Footprint:
    if accepted["status"] != "usable" or accepted["reasons"]:
        raise ValueError("footprint requires an accepted frame pair")
    graph = cut.build_graph(measured.match(a, b))
    _check_same_geometry(graph, accepted)
    faces = Counter(edge for boundary in graph.face_edges for edge in boundary)
    degrees = {site: len(neighbors) for site, neighbors in graph.adjacent.items()}
    reversed_edges: list[EdgeTrace] = []
    unknown_edges: list[EdgeTrace] = []
    unsupported: list[EdgeTrace] = []
    known_without_fourfold = unknown_without_fourfold = 0
    for i, (island, (u, v)) in enumerate(
        zip(graph.islands, graph.edge_ends, strict=True)
    ):
        endpoint_degrees = degrees[u], degrees[v]
        no_fourfold = 4 not in endpoint_degrees
        known_without_fourfold += no_fourfold and island.flip is not None
        unknown_without_fourfold += no_fourfold and island.flip is None
        if island.flip is False:
            continue
        trace = EdgeTrace(
            frame_rows=(island.first, island.second),
            endpoint_sites=(u, v),
            endpoint_degrees=endpoint_degrees,
            bounded_simple_face_count=faces[i],
        )
        if island.flip is None:
            unknown_edges.append(trace)
        else:
            reversed_edges.append(trace)
            if no_fourfold:
                unsupported.append(trace)

    edges = tuple(row["endpoint_sites"] for row in unsupported)
    cert = build_certificate(edges)
    return Footprint(
        observed_reversals=len(reversed_edges),
        unsupported_observed_reversals=len(edges),
        unsupported_reversals_on_two_bounded_simple_faces=sum(
            row["bounded_simple_face_count"] == 2 for row in unsupported
        ),
        minimum_non_fourfold_sites=verify_certificate(edges, cert),
        active_non_fourfold_sites=len({site for edge in edges for site in edge}),
        total_non_fourfold_sites=sum(degree != 4 for degree in degrees.values()),
        total_visible_sites=len(degrees),
        known_edges_without_fourfold_endpoint=known_without_fourfold,
        unknown_edges_without_fourfold_endpoint=unknown_without_fourfold,
        known_transition_edges=len(graph.islands) - len(unknown_edges),
        total_visible_edges=len(graph.islands),
        reversed_edges=reversed_edges,
        unknown_edges=unknown_edges,
        matching_lower_bound_edge_endpoints=cert.matching,
        cover_upper_bound_sites=cert.cover,
    )


class ResultRow(TypedDict):
    temperature_K: int
    first_pair_role: str
    status: str
    reasons: list[str]
    detail: list[str]
    members: list[str]
    row_counts: list[int | None]
    frame_sha256: tuple[str, str]
    missing_members: list[str]
    footprint: Footprint | None


class Result(TypedDict):
    schema: str
    scope: str
    claim_boundary: str
    trace_convention: str
    source_version_doi: object
    protocol_commit: object
    protocol_sha256: object
    primary_replay_sha256: object
    graph_builder_source_sha256: str
    rows: list[ResultRow]


def report() -> Result:
    # Checks the published protocol, replay source, selection, and all reserved pairs.
    frozen = transfer.report()
    a, b = measured.load_frames()  # Checks both pilot frame hashes.
    pilot = transfer.analyze_pair(a, b)
    rows = [
        ResultRow(
            temperature_K=250,
            first_pair_role="pilot",
            status=pilot["status"],
            reasons=pilot["reasons"],
            detail=pilot["detail"],
            members=[f"250K/{name}" for name in transfer.NAMES],
            row_counts=pilot["row_counts"],
            frame_sha256=measured.HASHES,
            missing_members=[],
            footprint=analyze_usable_pair(a, b, pilot),
        )
    ]
    for accepted in cast("list[transfer.TransferRow]", frozen["rows"]):
        footprint = None
        members = accepted["members"]
        digests = accepted["sha256_expected"]
        if accepted["status"] == "usable":
            if accepted["reasons"] or accepted["missing_members"]:
                raise ValueError("usable frozen transfer row has a failed guard")
            # Reopen only accepted pairs and recheck their original frame digests.
            a, b = (
                measured.read_frame((transfer.DATA / name).read_bytes(), digest)
                for name, digest in zip(members, digests, strict=True)
            )
            footprint = analyze_usable_pair(a, b, accepted)
        elif accepted["status"] != "inconclusive" or not accepted["reasons"]:
            raise ValueError("unrecognized frozen transfer row status")
        rows.append(
            ResultRow(
                temperature_K=accepted["temperature_K"],
                first_pair_role="reserved_for_fixed_transfer",
                status=accepted["status"],
                reasons=accepted["reasons"],
                detail=accepted["detail"],
                members=members,
                row_counts=accepted["row_counts"],
                frame_sha256=digests,
                missing_members=accepted["missing_members"],
                footprint=footprint,
            )
        )

    return Result(
        schema="idt-apamea-vertex-support/1",
        scope=(
            "The graph and pair acceptance follow the published fixed replay. The "
            "footprint test is retrospective at all settings, including the six pairs "
            "reserved for that replay. No fitted parameters or independent replication."
        ),
        claim_boundary=(
            "If the visible incidence and sign readout are fixed and faithful, updates "
            "confined to edges incident to degree-four sites leave all other edges "
            "unchanged at every sample time. Unlike face parity, time-smearing alone "
            "cannot generate a true sign change on an inert edge. The exact cover is "
            "a count of distinct non-fourfold sites needed in the incidence-only "
            "relaxation allowing arbitrary subsets at each site; it is not a count of "
            "events, an error bound, or sufficiency for a dynamical law. Unmatched "
            "labels remain unknown. Misclassification, hidden or mistaken geometry, "
            "lower-degree updates, and wider multi-site dynamics remain open."
        ),
        trace_convention=(
            "Frame rows are one-based in (000, 001) order; null is unmatched. Site IDs "
            "are the zero-based endpoint-cluster representatives from build_graph. "
            "Active sites are the endpoints of unsupported observed reversals only. "
            "Face counts use all inferred bounded simple faces, including incomplete ones."
        ),
        source_version_doi=frozen["source_version_doi"],
        protocol_commit=frozen["protocol_commit"],
        protocol_sha256=frozen["protocol_sha256"],
        primary_replay_sha256=frozen["primary_replay_sha256"],
        graph_builder_source_sha256=hashlib.sha256(
            Path(cut.__file__).read_bytes()
        ).hexdigest(),
        rows=rows,
    )


if __name__ == "__main__":
    print(json.dumps(report(), sort_keys=True, indent=2))
