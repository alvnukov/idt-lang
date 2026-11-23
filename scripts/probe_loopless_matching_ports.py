"""Compile and glue addressed Boolean gates on a loopless graph carrier.

Each logical bit is the presence of one bond. At logical gate boundaries,
port edges form a matching, all other bonds touching their vertices are
absent, and work ports are blank. Spectator bonds may live on disjoint
vertices. The raw rule is the same endpoint outside-degree parity rule as
the loopless quartet probe: code 6 toggles on OR of the two parities.

Port allocation, blank work edges and offer order are supplied externally.
This is an addressed finite Boolean construction, not endogenous routing,
arbitrary graph-state cloning, a particle model or a quantum gate claim.

Run: python3 -m scripts.probe_loopless_matching_ports
"""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import asdict, dataclass
from itertools import combinations, product

from scripts.probe_loopless_link_quartet import (
    BLANK_NAND,
    BLANK_OR,
    Edge,
    GateWitness,
    LooplessGraph,
    Word,
)

OR_CODE = 6
PairWord = tuple[Edge, ...]


def _require(condition: bool, message: str) -> None:
    # Keep the finite evidence checks active under python -O.
    if not condition:
        raise AssertionError(message)


def _require_disjoint(*ports: Edge) -> None:
    if len({vertex for edge in ports for vertex in edge}) != 2 * len(ports):
        raise ValueError("port edges must have distinct endpoints")


def matching_ports(count: int) -> tuple[Edge, ...]:
    return tuple((2 * i, 2 * i + 1) for i in range(count))


def addresses(graph: LooplessGraph, pairs: PairWord) -> Word:
    return tuple(graph.edge_index[(min(a, b), max(a, b))] for a, b in pairs)


def logical_mask(bits: int, edges: Word) -> int:
    return sum(1 << edge for slot, edge in enumerate(edges) if (bits >> slot) & 1)


def apply_quartet_target(mask: int, data: Word) -> int:
    """Complement the addressed four data bonds at weight two, else idle."""
    block = sum(1 << edge for edge in data)
    return mask ^ block if (mask & block).bit_count() == 2 else mask


def cnot_word(control: Edge, target: Edge) -> PairWord:
    """Toggle a matching target by the control, then clear both bridges."""
    _require_disjoint(control, target)
    a, b = control
    u, _ = target
    route = ((a, u), (b, u), (a, u))
    return route + (target,) + route[::-1]


def parity_copy_word(anchor: int, scratch: Edge) -> PairWord:
    """Record the original degree parity at anchor on a blank isolated port."""
    if anchor in scratch or scratch[0] == scratch[1]:
        raise ValueError("parity readout needs a distinct scratch port")
    bridge = (anchor, scratch[0])
    return (bridge, scratch, bridge)


def toffoli_word(x: Edge, y: Edge, target: Edge, scratch: Edge) -> PairWord:
    """Toggle target by x AND y with one reusable clean matching port."""
    _require_disjoint(x, y, target, scratch)
    bridge = ((x[0], y[0]),)
    copy = parity_copy_word(x[0], scratch)
    # Adding the bridge gives anchor parity q = x XOR (x OR y). Record q,
    # toggle target by it, reverse the record and bridge, then XOR in y.
    return (
        bridge
        + copy
        + cnot_word(scratch, target)
        + copy[::-1]
        + bridge
        + cnot_word(y, target)
    )


@dataclass(frozen=True)
class QuartetProgram:
    select: PairWord
    toggle: PairWord

    @property
    def word(self) -> PairWord:
        return self.select + self.toggle + self.select[::-1]


def quartet_program(
    data: tuple[Edge, ...], temporary: Edge, flag: Edge, scratch: Edge
) -> QuartetProgram:
    """Compile F4 on four data ports using three blank work ports."""
    if len(data) != 4:
        raise ValueError("quartet needs four data ports")
    _require_disjoint(*data, temporary, flag, scratch)
    select: PairWord = ()
    # The F2 sum of all quadratic and cubic squarefree monomials is 1
    # exactly at weight two. Reuse temporary by undoing each cubic's pair.
    for x, y in combinations(data, 2):
        select += toffoli_word(x, y, flag, scratch)
    for x, y, z in combinations(data, 3):
        pair = toffoli_word(x, y, temporary, scratch)
        select += pair + toffoli_word(temporary, z, flag, scratch) + pair[::-1]
    toggle = tuple(offer for edge in data for offer in cnot_word(flag, edge))
    # F4 preserves its own weight-two flag, so reversing select with the
    # updated data clears the flag as well as all temporary graph bonds.
    return QuartetProgram(select, toggle)


def audit_matching_ports() -> dict[str, int]:
    graph = LooplessGraph(14)
    ports = matching_ports(7)
    indices = addresses(graph, ports)
    x, y, target = ports[:3]
    scratch, spectator = ports[5:]
    cnot = addresses(graph, cnot_word(x, target))
    for bits in range(8):
        start = logical_mask(bits, addresses(graph, (x, target, spectator)))
        expected = start ^ ((bits & 1) << indices[2])
        _require(graph.replay(start, cnot, OR_CODE) == expected, "unclean CNOT")

    toffoli = addresses(graph, toffoli_word(x, y, target, scratch))
    x_y_bridge = 1 << addresses(graph, ((x[0], y[0]),))[0]
    target_bit, scratch_bit = 1 << indices[2], 1 << indices[5]
    dirty_scratch_wrong_targets = 0
    skipped_reset_dirty_inputs = 0
    skipped_reset_then_clean_wrong_targets = 0
    for bits in range(8):
        start = logical_mask(bits, indices[:3])
        x_value, y_value = bits & 1, (bits >> 1) & 1
        bridge_value = x_value | y_value
        q = x_value ^ bridge_value
        bridged = start ^ (bridge_value * x_y_bridge)
        recorded = bridged ^ (q * scratch_bit)
        want = start ^ ((x_value & y_value) * target_bit)
        trace = tuple(graph.trace(start, toffoli, OR_CODE))
        checkpoints = (trace[1], trace[4], trace[11], trace[14], trace[15], trace[-1])
        _require(
            checkpoints
            == (
                bridged,
                recorded,
                recorded ^ (q * target_bit),
                bridged ^ (q * target_bit),
                start ^ (q * target_bit),
                want,
            ),
            "unclean Toffoli checkpoint",
        )
        dirty = graph.replay(start | scratch_bit, toffoli, OR_CODE)
        dirty_scratch_wrong_targets += int(bool((dirty ^ want) & target_bit))
        skipped = graph.replay(start, toffoli[:11] + toffoli[14:], OR_CODE)
        skipped_reset_dirty_inputs += int(skipped != want)
        second = graph.replay(skipped, toffoli, OR_CODE)
        skipped_reset_then_clean_wrong_targets += int(
            bool((second ^ start) & target_bit)
        )
    _require(dirty_scratch_wrong_targets > 0, "missing dirty-scratch control")
    _require(skipped_reset_dirty_inputs > 0, "missing skipped-reset control")
    _require(skipped_reset_then_clean_wrong_targets > 0, "missing context disturbance")

    data = ports[:4]
    program = quartet_program(data, *ports[4:])
    select, toggle, clean = (
        addresses(graph, word)
        for word in (program.select, program.toggle, program.word)
    )
    quartet_no_uncompute_dirty_inputs = 0
    for bits in range(16):
        start = logical_mask(bits, indices[:4])
        expected = apply_quartet_target(start, indices[:4])
        selected = (1 << indices[5]) if bits.bit_count() == 2 else 0
        after_select = graph.replay(start, select, OR_CODE)
        _require(after_select == start | selected, "unclean selector")
        after_toggle = graph.replay(after_select, toggle, OR_CODE)
        _require(after_toggle == expected | selected, "incorrect controlled complement")
        _require(graph.replay(start, clean, OR_CODE) == expected, "unclean F4")
        quartet_no_uncompute_dirty_inputs += int(after_toggle != expected)
    return {
        "raw_code": OR_CODE,
        "cnot_offers": len(cnot),
        "cnot_clean_inputs": 4,
        "cnot_with_spectator_cases": 8,
        "toffoli_offers": len(toffoli),
        "toffoli_clean_inputs": 8,
        "toffoli_full_state_checkpoint_cases": 8 * 6,
        "toffoli_dirty_scratch_wrong_targets": dirty_scratch_wrong_targets,
        "toffoli_no_scratch_reset_dirty_inputs": skipped_reset_dirty_inputs,
        "toffoli_no_reset_then_clean_wrong_targets": skipped_reset_then_clean_wrong_targets,
        "quartet_sites": graph.size,
        "quartet_select_offers": len(select),
        "quartet_toggle_offers": len(toggle),
        "quartet_offers": len(clean),
        "quartet_clean_inputs": 16,
        "quartet_no_uncompute_dirty_inputs": quartet_no_uncompute_dirty_inputs,
    }


@dataclass(frozen=True)
class CompositionAudit:
    order: str
    logical_inputs: int
    spectator_states: int
    clean_through: int
    final_matches: int
    logical_order_differences: int


def audit_shared_port_composition() -> tuple[CompositionAudit, ...]:
    graph = LooplessGraph(22)
    ports = matching_ports(11)
    data = (ports[:4], ports[3:7])
    work = ports[7:10]
    raw = tuple(addresses(graph, quartet_program(d, *work).word) for d in data)
    block = tuple(addresses(graph, d) for d in data)
    indices = addresses(graph, ports)
    spectator = 1 << indices[-1]

    rows: list[CompositionAudit] = []
    for first, second in ((0, 1), (1, 0)):
        clean_through = final_matches = order_differences = 0
        for bits in range(128):
            data_state = logical_mask(bits, indices[:7])
            expected_mid = apply_quartet_target(data_state, block[first])
            expected_end = apply_quartet_target(expected_mid, block[second])
            other_end = apply_quartet_target(
                apply_quartet_target(data_state, block[second]), block[first]
            )
            order_differences += int(expected_end != other_end)
            for external in (0, spectator):
                mid = graph.replay(data_state | external, raw[first], OR_CODE)
                end = graph.replay(mid, raw[second], OR_CODE)
                correct_final = end == expected_end | external
                final_matches += int(correct_final)
                clean_through += int(correct_final and mid == expected_mid | external)
        _require(clean_through == 256, "shared port composition was not clean")
        _require(order_differences > 0, "composition orders did not discriminate")
        rows.append(
            CompositionAudit(
                "left_then_right" if first == 0 else "right_then_left",
                128,
                2,
                clean_through,
                final_matches,
                order_differences,
            )
        )
    return tuple(rows)


@dataclass(frozen=True)
class LiteralGlueCensus:
    code: int
    word_length: int
    gluing_count: int
    inputs_per_gluing: int
    min_final_matches: int
    max_final_matches: int
    fully_final_gluings: int
    fully_clean_gluings: int
    final_matches_histogram: dict[int, int]
    clean_through_matches_histogram: dict[int, int]
    correct_final_wrong_intermediate: int


def audit_literal_k4_edge_glue(witness: GateWitness) -> LiteralGlueCensus:
    """Try the supplied blank K4 word under literal identification of a data edge."""
    if (
        witness.layout.work_state != 0
        or witness.layout.data_edges != (0, 1, 2, 3)
        or witness.radius is not None
    ):
        raise ValueError(
            "control needs unguarded K4 with first-four data and blank work"
        )
    small = LooplessGraph(4)
    graph = LooplessGraph(6)
    left_word = addresses(graph, tuple(small.edges[i] for i in witness.word))
    left_data = addresses(graph, small.edges[:4])
    exact: Counter[int] = Counter()
    clean: Counter[int] = Counter()
    hidden_mid_failures = 0
    for left_role, right_role, flip in product(range(4), range(4), (False, True)):
        shared = small.edges[left_role]
        right_pair = small.edges[right_role]
        image = dict(zip(right_pair, shared[::-1] if flip else shared, strict=True))
        image.update(
            zip((v for v in range(4) if v not in right_pair), (4, 5), strict=True)
        )
        right_edges = tuple((image[a], image[b]) for a, b in small.edges)
        right_word = addresses(graph, tuple(right_edges[i] for i in witness.word))
        right_data = addresses(graph, right_edges[:4])
        union = tuple(dict.fromkeys(left_data + right_data))
        _require(len(union) == 7, "glue must identify exactly one data edge")
        final_matches = clean_through = 0
        for bits in range(128):
            start = logical_mask(bits, union)
            expected_mid = apply_quartet_target(start, left_data)
            expected_end = apply_quartet_target(expected_mid, right_data)
            # The six-site rule sees ALL outside bonds on both shared vertices.
            mid = graph.replay(start, left_word, witness.code)
            end = graph.replay(mid, right_word, witness.code)
            final_matches += int(end == expected_end)
            clean_through += int(end == expected_end and mid == expected_mid)
        exact[final_matches] += 1
        clean[clean_through] += 1
        hidden_mid_failures += final_matches - clean_through
    return LiteralGlueCensus(
        witness.code,
        len(witness.word),
        sum(exact.values()),
        128,
        min(exact),
        max(exact),
        exact[128],
        clean[128],
        dict(sorted(exact.items())),
        dict(sorted(clean.items())),
        hidden_mid_failures,
    )


def run_probe() -> dict[str, object]:
    return {
        "scope": "addressed finite Boolean gates on an unmarked loopless graph",
        "boundary": "matching ports, blank work, fixed pair offers; spectators disjoint",
        "matched_ports": audit_matching_ports(),
        "shared_port_composition": [
            asdict(row) for row in audit_shared_port_composition()
        ],
        "literal_k4_edge_glue": [
            asdict(audit_literal_k4_edge_glue(witness))
            for witness in (BLANK_OR, BLANK_NAND)
        ],
        "literal_control_limit": "two supplied K4 words only; not a gluing no-go",
    }


def main() -> None:
    print(json.dumps(run_probe(), indent=2))


if __name__ == "__main__":
    main()
