"""Replay classified moment changes on inferred Apamea faces (two 250 K frames).

Sampling, geometry, and interpretation: see data/ergodicity_asi/README.md.
No network calls, raw-image classification, or inferred microscopic events.
"""

from __future__ import annotations

import hashlib
import json
import math
from collections import Counter, defaultdict
from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from pathlib import Path

DATA = Path(__file__).resolve().parents[1] / "data" / "ergodicity_asi"
HASHES = (
    "38ff466252d49e7c1c6ae61c28c407f2af5bc6447b63336dfc5cc1021ccf4df1",
    "4af3edaa975909ba2189d5623a30e94504d995651039ca535dbec24f2966dfb8",
)
Point = tuple[float, float]


@dataclass(frozen=True)
class Spin:
    row: int
    x: float
    y: float
    axis: int
    sign: int


def read_frame(data: bytes, digest: str) -> tuple[Spin, ...]:
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError("frame SHA-256 mismatch")
    spins = []
    for row, line in enumerate(data.splitlines(), 1):
        x, y, mx, my, angle = map(float, line.split())
        if not all(map(math.isfinite, (x, y, mx, my, angle))):
            raise ValueError(f"nonfinite input at row {row}")
        axis = 1 if angle > 0 else -1
        if abs(angle) != 45 or mx == 0 or my != axis * mx:
            raise ValueError(f"unrecognized moment/axis encoding at row {row}")
        spins.append(Spin(row, x, y, axis, 1 if mx > 0 else -1))
    return tuple(spins)


def load_frames() -> tuple[tuple[Spin, ...], tuple[Spin, ...]]:
    def load(i: int) -> tuple[Spin, ...]:
        return read_frame((DATA / f"coordinates_{i:03d}.dat").read_bytes(), HASHES[i])

    return load(0), load(1)


def near_pairs(
    query: Sequence[Point], reference: Sequence[Point], radius: float
) -> Iterator[tuple[int, int]]:
    """All pairs within the inclusive Euclidean radius (not nearest neighbors)."""
    if not math.isfinite(radius) or radius <= 0:
        raise ValueError("radius must be positive and finite")
    cells: defaultdict[tuple[int, int], list[int]] = defaultdict(list)
    for j, (x, y) in enumerate(reference):
        cells[math.floor(x / radius), math.floor(y / radius)].append(j)
    for i, (x, y) in enumerate(query):
        ax, ay = math.floor(x / radius), math.floor(y / radius)
        for bx in range(ax - 1, ax + 2):
            for by in range(ay - 1, ay + 2):
                for j in cells.get((bx, by), ()):
                    ux, uy = reference[j]
                    if (ux - x) ** 2 + (uy - y) ** 2 <= radius**2:
                        yield i, j


@dataclass(frozen=True)
class Island:
    center: Point
    axis: int
    first: int | None
    second: int | None
    flip: bool | None


def match(a: Sequence[Spin], b: Sequence[Spin]) -> list[Island]:
    """Accept only uniquely paired centers of the same undirected axis."""
    forward: dict[int, int] = {}
    backward: dict[int, int] = {}
    for i, j in near_pairs([(s.x, s.y) for s in a], [(s.x, s.y) for s in b], 4.0):
        if a[i].axis == b[j].axis:
            if i in forward or j in backward:
                raise ValueError(
                    f"ambiguous same-axis pairing near rows {a[i].row}/{b[j].row}"
                )
            forward[i], backward[j] = j, i
    islands = []
    for i, s in enumerate(a):
        if i in forward:
            t = b[forward[i]]
            islands.append(
                Island(
                    ((s.x + t.x) / 2, (s.y + t.y) / 2),
                    s.axis,
                    s.row,
                    t.row,
                    s.sign != t.sign,
                )
            )
        else:
            islands.append(Island((s.x, s.y), s.axis, s.row, None, None))
    islands.extend(
        Island((s.x, s.y), s.axis, None, s.row, None)
        for j, s in enumerate(b)
        if j not in backward
    )
    return islands


class Groups:
    def __init__(self, n: int) -> None:
        self.parent = list(range(n))

    def find(self, i: int) -> int:
        while i != self.parent[i]:
            self.parent[i] = self.parent[self.parent[i]]
            i = self.parent[i]
        return i

    def join(self, i: int, j: int) -> None:
        self.parent[self.find(j)] = self.find(i)


@dataclass(frozen=True)
class Census:
    sizes: dict[int, int]
    flips: dict[int, int]
    incomplete: int
    first_odd: tuple[tuple[int, int, bool], ...]
    vertices: int
    degrees: dict[int, int]
    components: int
    nonsimple_positive: int
    crossings: tuple[tuple[int | None, ...], ...]

    def summary(self) -> dict[str, object]:
        walk_counts = {
            "simple_walks": sum(self.sizes.values()),
            "size_histogram": self.sizes,
            "flip_count_histogram": self.flips,
            "odd": sum(n for f, n in self.flips.items() if f % 2),
            "even": sum(n for f, n in self.flips.items() if not f % 2),
            "incomplete": self.incomplete,
            "excluded_positive_nonsimple_walks": self.nonsimple_positive,
        }
        summary: dict[str, object] = {
            "vertices": self.vertices,
            "degrees": self.degrees,
            "components": self.components,
            "crossing_island_pairs_rows_000_001": self.crossings,
        }
        if self.crossings:
            summary["invalid_embedding_walk_diagnostic"] = walk_counts
        else:
            summary["bounded_simple_faces"] = walk_counts.pop("simple_walks")
            summary.update(walk_counts)
        return summary


def intersections(
    center: dict[int, Point], edges: list[tuple[int, int]]
) -> Iterator[tuple[int, int]]:
    """List intersecting straight segments unless they meet only at a shared vertex."""
    cells: defaultdict[tuple[int, int], list[int]] = defaultdict(list)

    def side(a: Point, b: Point, c: Point) -> float:
        return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])

    for i, (u, v) in enumerate(edges):
        a, b = center[u], center[v]
        x0, x1 = sorted((a[0], b[0]))
        y0, y1 = sorted((a[1], b[1]))
        # Only an acceleration grid: intersection tests use original coordinates.
        touched = [
            (x, y)
            for x in range(math.floor(x0 / 32), math.floor(x1 / 32) + 1)
            for y in range(math.floor(y0 / 32), math.floor(y1 / 32) + 1)
        ]
        for j in {j for cell in touched for j in cells[cell]}:
            w, z = edges[j]
            c, d = center[w], center[z]
            if (
                x1 < min(c[0], d[0])
                or max(c[0], d[0]) < x0
                or y1 < min(c[1], d[1])
                or max(c[1], d[1]) < y0
            ):
                continue
            shared = {u, v} & {w, z}
            if shared:
                (p,) = shared
                (q,) = {u, v} - {p}
                (r,) = {w, z} - {p}
                h, k, l = center[p], center[q], center[r]
                if (
                    side(h, k, l) == 0
                    and (k[0] - h[0]) * (l[0] - h[0]) + (k[1] - h[1]) * (l[1] - h[1])
                    > 0
                ):
                    yield j, i
            elif (
                side(a, b, c) * side(a, b, d) <= 0
                and side(c, d, a) * side(c, d, b) <= 0
            ):
                yield j, i
        for cell in touched:
            cells[cell].append(i)


def faces(
    islands: Sequence[Island],
    cutoff: float,
    *,
    slope: int = 1,
    diagnostic: bool = False,
) -> Census:
    """Single-link endpoint clusters; predecessor in CCW order keeps face on left."""
    if slope not in (-1, 1):
        raise ValueError("slope convention must be ±1")
    endpoints: list[Point] = [
        (s.center[0] + dx, s.center[1] + dx * s.axis * slope)
        for s in islands
        for dx in (-11.75, 11.75)
    ]
    groups = Groups(len(endpoints))
    for i, j in near_pairs(endpoints, endpoints, cutoff):
        if i < j:
            groups.join(i, j)
    members: defaultdict[int, list[Point]] = defaultdict(list)
    for i, p in enumerate(endpoints):
        members[groups.find(i)].append(p)
    center = {
        v: (sum(p[0] for p in ps) / len(ps), sum(p[1] for p in ps) / len(ps))
        for v, ps in members.items()
    }
    adj: defaultdict[int, list[int]] = defaultdict(list)
    edge: dict[tuple[int, int], int] = {}
    components = Groups(len(endpoints))
    for k in range(len(islands)):
        u, v = groups.find(2 * k), groups.find(2 * k + 1)
        if u == v or (u, v) in edge:
            raise ValueError("endpoint clustering produced a self/parallel edge")
        adj[u].append(v)
        adj[v].append(u)
        edge[u, v] = edge[v, u] = k
        components.join(u, v)
    edges = [(u, v) for u, v in edge if u < v]
    crossings = []
    for j, i in intersections(center, edges):
        s, t = islands[edge[edges[j]]], islands[edge[edges[i]]]
        crossings.append((s.first, s.second, t.first, t.second))
    if crossings and not diagnostic:
        raise ValueError(f"crossing edges at frame rows {crossings[0]}")
    for v, neighbors in adj.items():
        x, y = center[v]
        neighbors.sort(key=lambda w: math.atan2(center[w][1] - y, center[w][0] - x))
    seen: set[tuple[int, int]] = set()
    sizes: Counter[int] = Counter()
    flips: Counter[int] = Counter()
    incomplete = nonsimple = 0
    first_odd: tuple[tuple[int, int, bool], ...] = ()
    for start in edge:
        if start in seen:
            continue
        u, v = start
        walk: list[int] = []
        boundary: list[Island] = []
        twice_area = 0.0
        while (u, v) not in seen:
            seen.add((u, v))
            walk.append(u)
            boundary.append(islands[edge[u, v]])
            x, y = center[u]
            xx, yy = center[v]
            twice_area += x * yy - xx * y
            u, v = v, adj[v][adj[v].index(u) - 1]
        if (u, v) != start:
            raise ValueError("half-edge traversal failed to close at its start")
        if twice_area <= 0:
            continue
        if len(set(walk)) != len(walk):
            nonsimple += 1
            continue
        sizes[len(boundary)] += 1
        trace = tuple(
            (s.first, s.second, s.flip)
            for s in boundary
            if s.first is not None and s.second is not None and s.flip is not None
        )
        if len(trace) < len(boundary):
            incomplete += 1
            continue
        n = sum(flip for _, _, flip in trace)
        flips[n] += 1
        if n % 2 and not first_odd:
            first_odd = trace
    return Census(
        dict(sizes),
        dict(flips),
        incomplete,
        first_odd,
        len(adj),
        dict(Counter(map(len, adj.values()))),
        len({components.find(v) for v in adj}),
        nonsimple,
        tuple(crossings),
    )


def report() -> dict[str, object]:
    a, b = load_frames()
    islands = match(a, b)
    primary = faces(islands, 4)
    return {
        "schema": "measured_asi_loop_parity_v1",
        "source_doi": "10.5281/zenodo.8250892",
        "frame_sha256": HASHES,
        "frames": ["250K/coordinates_000.dat", "250K/coordinates_001.dat"],
        "row_counts": [len(a), len(b)],
        "center_radius": 4,
        "endpoint_half_dx": 11.75,
        "matched": sum(s.flip is not None for s in islands),
        "only_first": sum(s.second is None for s in islands),
        "only_second": sum(s.first is None for s in islands),
        "reversed_classifications": sum(s.flip is True for s in islands),
        "primary_endpoint_cutoff": 4,
        "primary": primary.summary(),
        "first_odd_face_rows_000_001_changed": primary.first_odd,
        "endpoint_cutoff_sensitivity": {
            str(c): faces(islands, c, diagnostic=True).summary() for c in (3, 5)
        },
        "opposite_slope_at_fixed_centers_diagnostic": faces(
            islands, 4, slope=-1, diagnostic=True
        ).summary(),
        "claim_boundary": "Two classified tables and an inferred graph; odd changes exclude only a direct all-star-only bit update on that graph under faithful readout.",
    }


if __name__ == "__main__":
    print(json.dumps(report(), sort_keys=True, indent=2))
