"""Print input-only marked relay controls built from the frozen finite probes.

Use ``python3 -m scripts.marked_relay_controls`` to write the JSON batch to
stdout. It does not run a verdict, create a cache, or archive a result.
Evaluate the batch with a 5,000-trajectory case cap per candidate; smaller
caps are separate coverage tests, not revisions of these inputs.
"""

from __future__ import annotations

import json
from collections.abc import Sequence

from scripts import probe_minimal_signal_relay as signal
from scripts import probe_shuttle_local_reunions as shuttle
from theory_experiments.marked_relay import OriginContract, Program

CONTROL_MAX_CASES = 5000


def _reachable_rows(ports: shuttle.Ports, root: int) -> tuple[tuple[int, ...], ...]:
    """Reindex exactly the reachable shuttle component; retain every port."""
    states = [root]
    index = {root: 0}
    rows: list[tuple[int, ...]] = []
    for source in states:
        destinations: list[int] = []
        for port in ports:
            target = port[source]
            if target not in index:
                index[target] = len(states)
                states.append(target)
            destinations.append(index[target])
        rows.append(tuple(destinations))
    return tuple(rows)


def _spec(
    identifier: str,
    table: Sequence[Sequence[int]],
    *,
    program: Program = "through_six",
    origin_contract: OriginContract = "all",
    origin: int | None = None,
    marker_classes: Sequence[int] | None = None,
) -> dict[str, object]:
    result: dict[str, object] = {
        "family": "marked_relay",
        "id": identifier,
        "transitions": [list(row) for row in table],
        "marker_classes": (
            list(range(len(table))) if marker_classes is None else list(marker_classes)
        ),
        "origin_contract": origin_contract,
        "program": program,
    }
    if origin is not None:
        result["origin"] = origin
    return result


def control_specs() -> list[object]:
    """Build auditable inputs, with no verdicts encoded in the specification."""
    small = signal.quotient_4((0, 1, 2, 3))
    large = signal.quotient_4((0, 2))

    # Same literal gate and original mark as probe_shuttle_local_reunions.moved_mark.
    # Use the constructor, not the probe's verdict routine, to form the inputs.
    moved_gate = (0, 1, 4, 6, 2, 7, 3, 5)
    original_mark = 4**4 + sum(2 * 4**p for p in shuttle.PORTS)
    moved = _reachable_rows(shuttle.tables(4, moved_gate), original_mark)
    cycle = _reachable_rows(shuttle.tables(4, shuttle.ring(4)), 0)
    neighbor = moved[0][0]

    return [
        _spec("relay_32_named_six", small.neighbors, program="named_six"),
        _spec("relay_32_through_six", small.neighbors),
        _spec("relay_64_through_six", large.neighbors),
        _spec(
            "relay_64_role_detector_through_six",
            large.neighbors,
            marker_classes=large.role,
        ),
        _spec("shuttle_105_fixed_original", moved, origin_contract="fixed", origin=0),
        _spec(
            "shuttle_105_fixed_neighbor",
            moved,
            origin_contract="fixed",
            origin=neighbor,
        ),
        _spec("shuttle_105_all_origins", moved),
        _spec("shuttle_105_exists_origin", moved, origin_contract="exists"),
        _spec("shuttle_128_cycle_all_origins", cycle),
    ]


def main() -> None:
    print(json.dumps(control_specs(), separators=(",", ":")))


if __name__ == "__main__":
    main()
