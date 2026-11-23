"""Enumerate finite contact fixtures with a given shared-edge graph.

There is one physical bit per edge. In the common frame both endpoints read
it; in the opposite frame the lower endpoint reads the bit and the upper
endpoint reads its complement. A vertex offers a move at local population two
on its four legs. Firing complements all four physical bits, changing both
endpoint reads on each affected edge. Free legs have no guard at the far end.

Snapshot union checks both guards in the initial state and complements each
touched edge once. Initial-guard XOR uses the same guards but cancels shared
flips. Actual serial orders recheck the second guard after the first fire.

These are finite fixtures with supplied graphs, endpoint frames and guards;
they infer neither a physical orientation nor a simultaneous scheduling law.
Offer-count sensitivity is not nonconfluence: every tested legal move can undo.
Run: python3 -B -m scripts.probe_contact_edge_frames
"""

import json
from dataclasses import dataclass
from itertools import combinations
from typing import Literal

Frame = Literal["common", "opposite"]
Edge = tuple[int, int]
FRAMES: tuple[Frame, Frame] = ("common", "opposite")
LABELS = "ABCDE"


@dataclass(frozen=True)
class _Fixture:
    incident_masks: tuple[int, ...]
    opposite_read_masks: tuple[int, ...]

    @classmethod
    def build(
        cls, guarded_vertices: int, edges: tuple[Edge, ...], frame: Frame
    ) -> "_Fixture":
        incident = [0] * guarded_vertices
        opposite = [0] * guarded_vertices
        for index, (lower, upper) in enumerate(edges):
            bit = 1 << index
            incident[lower] |= bit
            if upper < guarded_vertices:
                incident[upper] |= bit
                if frame == "opposite":
                    opposite[upper] |= bit
        if any(mask.bit_count() != 4 for mask in incident):
            raise ValueError("every guarded vertex must have four legs")
        return cls(tuple(incident), tuple(opposite))

    def population(self, state: int, vertex: int) -> int:
        return (
            (state ^ self.opposite_read_masks[vertex]) & self.incident_masks[vertex]
        ).bit_count()

    def fire(self, state: int, vertex: int) -> int | None:
        if self.population(state, vertex) != 2:
            return None
        return state ^ self.incident_masks[vertex]

    def moves(self, state: int) -> dict[int, int]:
        return {
            vertex: updated
            for vertex in range(len(self.incident_masks))
            if (updated := self.fire(state, vertex)) is not None
        }

    def nonreversible(self, state: int, moves: dict[int, int]) -> int:
        return sum(
            self.fire(updated, vertex) != state for vertex, updated in moves.items()
        )


def _word(state: int, width: int) -> str:
    return "".join(str((state >> index) & 1) for index in range(width))


def _parse_word(word: str) -> int:
    return sum(int(bit) << index for index, bit in enumerate(word))


def _overlapping_stars(frame: Frame, shared_edges: int) -> dict[str, int]:
    edges = ((0, 1),) * shared_edges + tuple(
        (vertex, 2 + 4 * vertex + leg)
        for vertex in range(2)
        for leg in range(4 - shared_edges)
    )
    fixture = _Fixture.build(2, edges, frame)
    left_mask, right_mask = fixture.incident_masks
    row = {
        "shared_edges": shared_edges,
        "states": 1 << len(edges),
        "jointly_legal": 0,
        "both_serial_legal": 0,
        "exactly_one_serial_legal": 0,
        "serial_output_disagreements": 0,
        "serial_output_not_preguarded_xor": 0,
        "snapshot_not_preguarded_xor": 0,
        "snapshot_not_both_legal_serials": 0,
        "nonreversible_moves": 0,
    }
    for state in range(row["states"]):
        moves = fixture.moves(state)
        row["nonreversible_moves"] += fixture.nonreversible(state, moves)
        if len(moves) != 2:
            continue
        row["jointly_legal"] += 1
        snapshot = state ^ (left_mask | right_mask)
        preguarded_xor = state ^ left_mask ^ right_mask
        row["snapshot_not_preguarded_xor"] += snapshot != preguarded_xor
        left_then_right = fixture.fire(moves[0], 1)
        right_then_left = fixture.fire(moves[1], 0)
        if left_then_right is not None and right_then_left is not None:
            row["both_serial_legal"] += 1
            row["serial_output_disagreements"] += left_then_right != right_then_left
            row["serial_output_not_preguarded_xor"] += (
                left_then_right != preguarded_xor or right_then_left != preguarded_xor
            )
            row["snapshot_not_both_legal_serials"] += (
                snapshot != left_then_right and snapshot != right_then_left
            )
        elif left_then_right is not None or right_then_left is not None:
            row["exactly_one_serial_legal"] += 1
    return row


def _doubled_triangle(frame: Frame) -> dict[str, object]:
    # Edge words are in AB, AB, AC, AC, BC, BC order.
    edges = tuple(edge for edge in combinations(range(3), 2) for _ in range(2))
    fixture = _Fixture.build(3, edges, frame)
    states = 1 << len(edges)
    all_live_starts = 0
    always_preserving_starts = 0
    always_only_fired_live_starts: list[str] = []
    nonreversible_moves = 0
    for state in range(states):
        moves = fixture.moves(state)
        nonreversible_moves += fixture.nonreversible(state, moves)
        if len(moves) != 3:
            continue
        all_live_starts += 1
        after = {
            vertex: tuple(fixture.moves(updated)) for vertex, updated in moves.items()
        }
        always_preserving_starts += all(len(offers) == 3 for offers in after.values())
        if all(offers == (vertex,) for vertex, offers in after.items()):
            always_only_fired_live_starts.append(_word(state, len(edges)))

    witness = "110011"
    fired = fixture.fire(_parse_word(witness), 0)
    return {
        "states": states,
        "all_live_starts": all_live_starts,
        "always_preserving_starts": always_preserving_starts,
        "always_only_fired_live_starts": sorted(always_only_fired_live_starts),
        "witness_after_a": {
            "word": witness,
            "populations": [fixture.population(fired, vertex) for vertex in range(3)]
            if fired is not None
            else None,
        },
        "nonreversible_moves": nonreversible_moves,
    }


def _common_k5_half_filling() -> dict[str, object]:
    # Edge words are in AB, AC, AD, AE, BC, BD, BE, CD, CE, DE order.
    edges = tuple(combinations(range(5), 2))
    fixture = _Fixture.build(5, edges, "common")
    half_filling = len(edges) // 2
    states = 0
    offer_count_choice_sensitive_starts = 0
    fully_enabled_starts = 0
    fully_enabled_first_fires = 0
    first_fires_with_nonbacktracking_continuation = 0
    nonreversible_moves = 0
    half_filling_violations = 0
    witness = "0111110000"
    witness_offers: dict[str, list[str]] = {}
    for state in range(1 << len(edges)):
        if state.bit_count() != half_filling:
            continue
        states += 1
        moves = fixture.moves(state)
        nonreversible_moves += fixture.nonreversible(state, moves)
        half_filling_violations += sum(
            updated.bit_count() != half_filling for updated in moves.values()
        )
        after = {
            vertex: tuple(fixture.moves(updated)) for vertex, updated in moves.items()
        }
        offer_count_choice_sensitive_starts += (
            len({len(offers) for offers in after.values()}) > 1
        )
        if len(moves) == 5:
            fully_enabled_starts += 1
            fully_enabled_first_fires += len(moves)
            first_fires_with_nonbacktracking_continuation += sum(
                any(next_vertex != vertex for next_vertex in offers)
                for vertex, offers in after.items()
            )
        if state == _parse_word(witness):
            witness_offers = {
                LABELS[vertex]: [LABELS[next_vertex] for next_vertex in offers]
                for vertex, offers in after.items()
            }

    return {
        "states": states,
        "offer_count_choice_sensitive_starts": offer_count_choice_sensitive_starts,
        "fully_enabled_starts": fully_enabled_starts,
        "fully_enabled_first_fires": fully_enabled_first_fires,
        "first_fires_with_nonbacktracking_continuation": first_fires_with_nonbacktracking_continuation,
        "nonreversible_moves": nonreversible_moves,
        "half_filling_violations": half_filling_violations,
        "choice_witness": {"word": witness, "offers_after": witness_offers},
    }


def main() -> None:
    report = {
        "overlapping_stars": {
            frame: [_overlapping_stars(frame, shared) for shared in range(5)]
            for frame in FRAMES
        },
        "doubled_triangle": {frame: _doubled_triangle(frame) for frame in FRAMES},
        "common_k5_half_filling": _common_k5_half_filling(),
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
