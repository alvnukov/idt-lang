"""Which reciprocal cell rules can a held rail and a marked hub clock distinguish?

Finite fixture only. Four rules are selected by the existing synthetic timing
census. Blank cells, unary petals, the latch, a shared hop and a two-edge
reference detour are supplied; squared shares are tested, not used as dynamics.
Run: python3 -B -m scripts.probe_cell_rule_clock_projection
"""

from collections import Counter
from itertools import product
from math import lcm

from scripts.compile_petal_clock_hypothesis import (
    _ring_device,
    _trace_device,
    compile_hypothesis,
)
from scripts.probe_bipartite_triangle_origin import need
from scripts.probe_internal_detector_clocks import advance, retreat
from scripts.probe_matched_vernier_petals import extend_one_wire
from scripts.probe_reversible_cell_census import (
    TablePetal,
    census,
    encode,
    inferred_rule,
)
from theory_experiments.periodic_contact_observer import (
    MAX_STATES,
    evaluate_periodic_contact_observer,
    parse_periodic_contact_observer,
)
from theory_experiments.primitive_screen import Limits, canonical_json

PACKETS = ((1, 2, -1, -2), (0, 0, -2, -2, 1, 3), (0, 3, 3, -1, -5, 0), (5, -5))
PASS = "no_counterexample_within_bounds"


def signal(sizes, rule, first, direction):
    g = TablePetal(sizes, rule)
    # Each incoming hub port identifies its local rail, travel direction and
    # lane. Record this richer instrument independently of the held-rail read.
    ports = {v: (i, -d, b) for (i, d, b), v in g.starts.items()}
    calendar, tick = [], 0

    def read(local):
        nonlocal tick
        (u, v, _), label = local
        tick += 1
        if v == 0:
            calendar.append((tick, *ports[u]))
        return label

    def step(local):
        after = advance(g, *local)
        need(retreat(g, *after) == local, "latch or signal hop lost its inverse")
        return after

    table = _trace_device((g.launch(first, direction, 0), first), step, read,
                          max_states=MAX_STATES, name="table-rule signal")
    return table, tuple(calendar)


def reference(sizes, rule, first, direction, detune):
    g = TablePetal(sizes, rule)
    if detune:
        extend_one_wire(g, first)
    ports = {g.starts[first, d, 1] for d in (-1, 1)}

    def step(state):
        after = g.step(state)
        need(g.inverse(after) == state, "reference hop lost its inverse")
        return after

    return _trace_device(g.launch(first, direction, 0), step, lambda s: s[0] == 0 and s[1] in ports,
                         max_states=MAX_STATES, name="table-rule reference")


def inspect(packet, s, c):
    model = parse_periodic_contact_observer({"family": "periodic_contact_observer", "id": "cell_projection",
                                             "current": list(packet), "signal": s, "clock": c})
    (check,), scope = evaluate_periodic_contact_observer(model, Limits(max_cases=5000))
    return model.specification(), check, scope


def replay(s, c, i, j, nrails):
    """Directly traverse two submitted reached-state tables at literal starting states."""
    begin = i, j
    counts = [0] * nrails
    for _ in range(lcm(len(s), len(c))):
        i, label = s[i]
        j, fire = c[j]
        if fire:
            counts[label] += 1
    need((i, j) == begin, "direct offset replay did not return")
    return counts


def marked_control(rule):
    # Different preparation and instrument: read the first marked incoming
    # hub contact with two marks stored in the length-three home rail.
    g = TablePetal((3, 3), rule)
    state = g.launch(0, 1, g.cellmask[0])
    marked = {g.starts[0, d, 1] for d in (-1, 1)}
    for tick in range(1, 37):
        if state[1] == 0 and state[0] in marked:
            return tick
        state = g.step(state)
    raise AssertionError("missing marked-control return within fixture bound")


def probe():
    rows, _ = census()
    winners = {word for word, flags in rows if flags == "1111"}
    rules = {key: inferred_rule(*key) for key in product((False, True), repeat=2)}
    need({encode(rule) for rule in rules.values()} == winners and len(winners) == 4,
         "full census winners changed")
    prepared = phase_cases = 0
    calendar_classes = Counter()
    controls, signatures, examples = {}, {}, []
    for packet in PACKETS:
        sizes = tuple(map(abs, packet))
        for first, direction in product((i for i, n in enumerate(sizes) if n), (-1, 1)):
            compiled = compile_hypothesis(packet, first_rail=first, direction=direction,
                                          identifier="cell_projection")
            reference_result = inspect(packet, compiled["signal"], compiled["clock"])
            calendars = set()
            for (transfer, double), rule in rules.items():
                s, calendar = signal(sizes, rule, first, direction)
                c = reference(sizes, rule, first, -direction, True)
                submitted, check, scope = inspect(packet, s, c)
                # Compare entire reached-state tables (including successors and
                # first-visit indices) and entire checker evidence, not just histograms.
                need((submitted, check, scope) == reference_result and submitted == compiled,
                     "a rule differs at this coarse projection")
                need(check.status == PASS and check.checked == check.planned == 2 and
                     scope["all_recurrent_phase_rail_rates_certified"] and
                     scope["trigger_count_per_clock_cycle"] == 1, "matched phase coverage changed")
                calendars.add(calendar)
                prepared += 1
                phase_cases += check.checked
                if packet == (5, -5) and first == 0 and direction == 1:
                    tick, rail, d, lane = calendar[0]
                    need((rail, lane) == (0, 0), "not the first unmarked home return")
                    signatures[encode(rule)] = [tick, d, marked_control(rule)]
                    need((tick, d, signatures[encode(rule)][-1]) ==
                         (8 if transfer else 20, -1 if transfer else 1, 8 if double else 12),
                         "two-preparation physical hub signature changed")
                if packet == PACKETS[0] and first == 0 and direction == 1:
                    for name, clock in (("identical", reference(sizes, rule, first, -direction, False)),
                                        ("ring_10", _ring_device(10, -direction, MAX_STATES))):
                        control, result, _ = inspect(packet, s, clock)
                        original = compile_hypothesis(packet, clock="identical" if name == "identical" else "ring",
                            period=None if name == "identical" else 10, identifier="cell_projection")
                        need(control == original and result.status == "counterexample", "missing alias control")
                        w = result.witness["inputs"]
                        measured = replay(s["transitions"], clock["transitions"], w["signal_state"],
                                          w["clock_state"], len(packet))
                        need(measured == w["observed_rail_counts"], "alias witness replay failed")
                        controls[name] = {"offset": w["relative_phase_offset"], "counts": measured}
            calendar_classes[len(calendars)] += 1
            # Two genuinely different starts per residue, not only clock-phase 0.
            s, c = compiled["signal"]["transitions"], compiled["clock"]["transitions"]
            expected = reference_result[2]["observed_phase_rail_counts"]["matching_rail_counts"]
            for i, j in ((0, 0), (0, 1), (len(s)-1, len(c)-1), (len(s)-1, 0)):
                need(replay(s, c, i, j, len(packet)) == expected, "literal phase replay disagrees")
            if direction == 1 and first == next(i for i, n in enumerate(sizes) if n):
                examples.append({"current": packet, "signal_home": first, "signal_direction": direction,
                                 "clock_direction": -direction, "periods": [len(s), len(c)],
                                 "observed_counts_each_offset": expected})
    need(len(set(map(tuple, signatures.values()))) == 4 and calendar_classes[2] > 0,
         "calendars did not discriminate despite identical submissions")
    return {"scope": "four census survivors; listed blank packets, every live home, both signal directions; "
                     "oppositely launched matched reference; no universal or physical status",
            "packets": PACKETS, "rule_preparations": prepared, "matched_phase_classes_checked": phase_cases,
            "distinct_submissions_per_fixed_preparation": 1,
            "representative_matched_measurements": examples,
            "preparations_by_number_of_rich_signal_calendars": dict(sorted(calendar_classes.items())),
            "control_counterexamples": controls,
            "signature_columns": ["blank_5_first_hub_tick", "incoming_direction", "two_stored_3_first_marked_tick"],
            "rich_hub_signatures": dict(sorted(signatures.items()))}


if __name__ == "__main__":
    print(canonical_json(probe()))
