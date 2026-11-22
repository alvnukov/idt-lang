"""Export a prepared local petal-and-clock orbit as a finite screen input.

One reversible signal, with its held hub rail, and one independent reference
advance one physical edge per step. Their complete reachable tables are
recorded before evaluating any rail-share reference. The graph, unary
installation, initial excitations, ports and common step rate are inputs;
no preparation law, geometry or physical prediction is inferred.

Example: python3 -m scripts.compile_petal_clock_hypothesis --current 1 2 -1 -2
Use --emit to obtain a one-candidate JSON array for screen_hypotheses.py.
"""

from __future__ import annotations

import argparse
import sys
from collections.abc import Callable, Hashable
from pathlib import Path
from typing import TypeVar

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_internal_detector_clocks import advance, retreat, ring
from scripts.probe_matched_vernier_petals import extend_one_wire
from scripts.probe_reversible_excitation_detector import Apparatus
from theory_experiments.periodic_contact_observer import (
    MAX_CURRENT,
    MAX_RAILS,
    MAX_STATES,
    evaluate_periodic_contact_observer,
    parse_periodic_contact_observer,
)
from theory_experiments.primitive_screen import (
    Limits,
    bounded_int,
    candidate_id,
    canonical_json,
)

CLOCKS = ("matched", "identical", "ring", "trapped")
# The unmodified default installation has eight undirected physical edges
# per supplied logical edge. The reference splice adds just two more.
MAX_INSTALLATION_LOGICAL_EDGES = 256
MAX_BATCH_INPUT_BYTES = 128 * 1024
State = TypeVar("State", bound=Hashable)
Device = dict[str, object]


class OrbitBudgetExceeded(ValueError):
    """A full observed return was not available within the state budget."""


def _trace_device(start: State, step: Callable[[State], State],
                  read: Callable[[State], int | bool], *, max_states: int, name: str) -> Device:
    """Number full states in their first-visit order and record each local read."""
    seen: dict[State, int] = {}
    outputs = []
    state = start
    while state not in seen:
        if len(seen) >= max_states:
            raise OrbitBudgetExceeded(f"{name} did not close within {max_states} device states")
        seen[state] = len(seen)
        outputs.append(read(state))
        state = step(state)
    if seen[state] != 0:
        raise ValueError(f"{name} obtained a transient from a reversible preparation")
    # Successor numbering follows actual visits until the observed return.
    rows = [[i + 1, output] for i, output in enumerate(outputs)]
    rows[-1][0] = seen[state]
    return {"initial": 0, "transitions": rows}


def _signal_device(sizes: tuple[int, ...], home: int, direction: int, max_states: int) -> Device:
    signal = Apparatus(sizes)

    def step(local):
        state, held_rail = local
        successor = advance(signal, state, held_rail)
        if retreat(signal, *successor) != local:
            raise ValueError("signal and held rail did not reverse")
        return successor

    # Read the held register, not the rail tag on a remote directed arc.
    return _trace_device((signal.launch(home, direction, 0), home), step, lambda s: s[1],
                         max_states=max_states, name="signal")


def _reference_device(sizes: tuple[int, ...], home: int, direction: int,
                      kind: str, max_states: int, trap_rail: int | None) -> Device:
    reference = Apparatus(sizes)
    if kind in ("matched", "trapped"):
        extend_one_wire(reference, home)
    marked_ports = {reference.starts[home, d, 1] for d in (-1, 1)}
    start = reference.launch(home, direction, 0)
    if trap_rail is not None:
        # A single mark is stored away from the travelling unmarked cursor,
        # in the lowest installed cell of an explicitly different petal.
        mask = reference.cellmask[trap_rail]
        start = (0, reference.starts[home, direction, 0], mask & -mask)

    def step(state):
        successor = reference.step(state)
        if reference.inverse(successor) != state:
            raise ValueError("reference did not reverse")
        return successor

    return _trace_device(start, step, lambda s: s[0] == 0 and s[1] in marked_ports,
                         max_states=max_states, name="reference")


def _ring_device(period: int, direction: int, max_states: int) -> Device:
    contacts = ring(period)

    def step(state):
        at, previous = state
        a, b = contacts[at]
        if previous not in (a, b):
            raise ValueError("nonincident ring pulse")
        return (b if previous == a else a), at

    return _trace_device((0, (-direction) % period), step, lambda s: s[0] == 0,
                         max_states=max_states, name="ring reference")


def compile_hypothesis(
    current: tuple[int, ...] | list[int], *, clock: str = "matched", period: int | None = None,
    first_rail: int | None = None, direction: int = 1, max_device_states: int = MAX_STATES,
    identifier: str | None = None,
) -> dict[str, object]:
    """Compile an explicit prepared installation; never return a censored table."""
    if type(current) not in (tuple, list) or not 2 <= len(current) <= MAX_RAILS:
        raise ValueError(f"expected 2..{MAX_RAILS} labelled current coordinates")
    packet = tuple(bounded_int(a, -MAX_CURRENT, MAX_CURRENT) for a in current)
    if sum(packet) or not any(packet):
        raise ValueError("a nonzero neutral integer installation is required")
    sizes = tuple(map(abs, packet))
    if sum(sizes) > MAX_INSTALLATION_LOGICAL_EDGES:
        raise ValueError("unary installation exceeds logical edge budget")
    if type(clock) is not str or clock not in CLOCKS:
        raise ValueError(f"expected a clock in {CLOCKS}")
    cap = bounded_int(max_device_states, 1, MAX_STATES)
    d = bounded_int(direction, -1, 1)
    if not d:
        raise ValueError("direction must be -1 or 1")
    live = tuple(i for i, size in enumerate(sizes) if size)
    home = live[0] if first_rail is None else bounded_int(first_rail, 0, len(sizes) - 1)
    if home not in live:
        raise ValueError("first rail must be live")
    if clock == "ring":
        h = bounded_int(period, 4, MAX_STATES)
        if h % 2:
            raise ValueError("ring period must be even")
    elif period is not None:
        raise ValueError("--period applies only to an explicit ring reference")
    else:
        h = None
    trap = None
    if clock == "trapped":
        trap = next((i for i in live if i != home and sizes[i] > 1), None)
        if trap is None:
            raise ValueError("trapped reference needs an interior cell outside the home rail")
    default_id = f"petal_clock_{clock}" + (f"_{h}" if h is not None else "")
    name = candidate_id(default_id if identifier is None else identifier)

    signal = _signal_device(sizes, home, d, cap)
    reference = (_ring_device(h, -d, cap) if h is not None
                 else _reference_device(sizes, home, -d, clock, cap, trap))
    proposed = {"id": name, "family": "periodic_contact_observer", "current": list(packet),
                "signal": signal, "clock": reference}
    return parse_periodic_contact_observer(proposed).specification()


def controls() -> list[dict[str, object]]:
    """Fixed prepared packet; positive route, two alias controls and a silent reference."""
    packet = (1, 2, -1, -2)
    return [
        compile_hypothesis(packet, clock="matched"),
        compile_hypothesis(packet, clock="identical"),
        compile_hypothesis(packet, clock="ring", period=10),
        compile_hypothesis(packet, clock="trapped"),
    ]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--current", nargs="+", type=int, required=True, help="signed neutral integer rails")
    parser.add_argument("--clock", choices=CLOCKS, default="matched")
    parser.add_argument("--period", type=int, help="explicit even ring size (required for --clock ring)")
    parser.add_argument("--first-rail", type=int, help="prepared departure and marked home (default: first live rail)")
    parser.add_argument("--direction", type=int, choices=(-1, 1), default=1, help="direction of the signal")
    parser.add_argument("--max-device-states", type=int, default=MAX_STATES)
    parser.add_argument("--max-cases", type=int, help="relative phase budget for the compact summary (default: 64)")
    parser.add_argument("--id", help="candidate id override")
    parser.add_argument("--emit", action="store_true", help="print canonical candidate batch input instead of evaluating")
    args = parser.parse_args(argv)
    try:
        if args.emit and args.max_cases is not None:
            raise ValueError("--max-cases is for the summary; set it on the screen CLI for an emitted batch")
        budget = Limits(max_cases=64 if args.max_cases is None else args.max_cases)
        spec = compile_hypothesis(args.current, clock=args.clock, period=args.period, first_rail=args.first_rail,
                                  direction=args.direction, max_device_states=args.max_device_states,
                                  identifier=args.id)
        if args.emit:
            raw = canonical_json([spec]) + "\n"
            if len(raw.encode("utf-8")) > MAX_BATCH_INPUT_BYTES:
                raise ValueError("compiled input exceeds the batch CLI's 128 KiB limit")
            sys.stdout.write(raw)
            return 0
        (check,), scope = evaluate_periodic_contact_observer(parse_periodic_contact_observer(spec), budget)
        print(canonical_json({"id": spec["id"], "current": spec["current"],
                              "clock_construction": args.clock, "check": check.specification(), "scope": scope}))
        return (1 if check.status == "counterexample"
                else 0 if check.status == "no_counterexample_within_bounds" else 3)
    except (ValueError, TypeError, AssertionError) as error:
        print(f"compile_petal_clock_hypothesis: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
