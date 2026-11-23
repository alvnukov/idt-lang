"""A local signed rotor refines integer streams into a contact's mean wave.

Reflect an incoming sign and copy it to the rotor's two consecutive ports.
A positive ingress takes two forward steps; a negative one first takes
two backward steps and uses the pair just untraversed. The update uses
only a head, reciprocal neighbor links, the ingress, and its sign.
The signed routed increments telescope: from head p, net signed input N
is a walk of signed length 2N on the port ring, no matter the order.
Hence aggregate output is -x plus that walk's signed visit counts, within
one record per port of (2N/d)-x_i. At d|2N it equals that map exactly.

This is not an event-frequency law, passive physical time reversal, or a
lossless one-packet junction. Two signed copies, port-local cancellation,
ordered entry, atomic event boundaries, cyclic wiring and a latched head
are supplied. Orthogonality applies to the completed signed aggregate,
not to raw marks, absolute flux or energy per ingress. No squared readout
or random phase is used. See the output's scope and comparisons.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction as F
from math import gcd, lcm, prod

Vector = tuple[int, ...]
Record = tuple[int, int]


def need(condition, message):
    if not condition:
        raise ArithmeticError(message)


@dataclass(frozen=True)
class Ring:
    order: Vector
    next_port: Vector
    prev_port: Vector

    @classmethod
    def wire(cls, order: Vector) -> Ring:
        d = len(order)
        need(d >= 2 and set(order) == set(range(d)), "ring must visit each port once")
        nxt = [0] * d
        prev = [0] * d
        for j, port in enumerate(order):
            nxt[port] = order[j + 1] if j + 1 < d else order[0]
            prev[nxt[port]] = port
        return cls(order, tuple(nxt), tuple(prev))

    def burst(
        self, head: int, source: int, sign: int, *, forward_only=False
    ) -> tuple[int, tuple[Record, ...]]:
        # This is the circuit update, not the floor-count reference below.
        # Return only the surviving ports of one atomic three-record burst.
        p = head
        if sign == -1 and not forward_only:
            p = self.prev_port[self.prev_port[head]]
            after = p
        else:
            after = self.next_port[self.next_port[head]]
        q = self.next_port[p]
        if source == p:
            return after, ((q, sign),)
        if source == q:
            return after, ((p, sign),)
        return after, ((source, -sign), (p, sign), (q, sign))

    def recover(self, after: int, emitted: tuple[Record, ...]) -> tuple[int, int, int]:
        # Signed flux supplies the ingress sign even after port cancellation.
        sign = sum(s for _, s in emitted)
        need(sign in (-1, 1), "expected one atomic signed burst")
        p = self.prev_port[self.prev_port[after]] if sign == 1 else after
        prior = p if sign == 1 else self.next_port[self.next_port[after]]
        v = tally(len(self.order), emitted)
        v[p] -= sign
        v[self.next_port[p]] -= sign
        need(
            v.count(-sign) == 1 and sum(a != 0 for a in v) == 1,
            "invalid atomic signed burst",
        )
        return prior, v.index(-sign), sign


def tally(d: int, records) -> list[int]:
    result = [0] * d
    for port, sign in records:
        result[port] += sign
    return result


def stream(ring: Ring, head: int, records, *, forward_only=False):
    output = [0] * len(ring.order)
    surviving_count = 0
    for source, sign in records:
        head, burst = ring.burst(head, source, sign, forward_only=forward_only)
        surviving_count += len(burst)
        for p, s in burst:
            output[p] += s
    return head, tuple(output), surviving_count


def visits_and_head(
    ring: Ring, head: int, signed_count: int
) -> tuple[Vector, int, int]:
    """Separate floor formula: oriented interval from 0 to 2N, even for N<0."""
    d = len(ring.order)
    origin = ring.order.index(head)
    quotient, rem = divmod(2 * signed_count, d)
    result = [0] * d
    for j, port in enumerate(ring.order):
        result[port] = quotient + int((j - origin) % d < rem)
    return tuple(result), ring.order[(origin + rem) % d], rem


def exact_comparison(ring, start, input_counts, output_counts, head):
    d = len(ring.order)
    n = sum(input_counts)
    visits, predicted_head, rem = visits_and_head(ring, start, n)
    errors = tuple(
        d * (x + y) - 2 * n for x, y in zip(input_counts, output_counts, strict=True)
    )
    need(head == predicted_head, "head disagrees with independent modular-bin oracle")
    need(
        all(
            x + y == visit
            for x, y, visit in zip(input_counts, output_counts, visits, strict=True)
        ),
        "signed visit mismatch",
    )
    need(
        max(map(abs, errors)) <= d - gcd(d, 2) and sum(errors) == 0,
        "signed input prefix exceeded sharp coordinate discrepancy",
    )
    need(
        sum(e * e for e in errors) == d * rem * (d - rem),
        "wrong exact square error on visits",
    )
    need(
        all(e == 0 for e in errors) == (rem == 0) == (head == start),
        "cycle closure differs from exact rate",
    )
    return max(map(abs, errors))


def check_history_tree(ring, start, max_depth):
    d = len(ring.order)
    alphabet = tuple((port, sign) for port in range(d) for sign in (-1, 1))
    observed = [0] * d
    entered = [0] * d

    def visit(head, left):
        exact_comparison(ring, start, entered, observed, head)
        states = 1
        if left:
            for p, s in alphabet:
                after, emitted = ring.burst(head, p, s)
                entered[p] += s
                for q, t in emitted:
                    observed[q] += t
                states += visit(after, left - 1)
                entered[p] -= s
                for q, t in emitted:
                    observed[q] -= t
        return states

    return visit(start, max_depth)


def exhaustive_signed_histories():
    states_checked = 0
    for d in range(2, 8):
        # Use reversed ordering of labels to reject a hidden numeric successor.
        ring = Ring.wire(tuple(reversed(range(d))))
        max_depth = 4 if d <= 5 else 3
        states_checked += sum(
            check_history_tree(ring, start, max_depth) for start in range(d)
        )
    return states_checked


def phase_resources():
    rows = {}
    transitions_checked = 0
    for d in range(2, 33):
        ring = Ring.wire(tuple(range(d)))
        period = d // gcd(2, d)
        ideal_positive = 2 - F(2, d)
        ideal_negative = 1 - F(2, d)
        worst = 0
        for start in range(d):
            for source in range(d):
                for sign in (-1, 1):
                    head = start
                    observed = [0] * d
                    reached = set()
                    raw_positive = raw_negative = 0
                    for j in range(period):
                        # Atomic invertibility is checked for all current phases
                        # and both signs/ingresses below, not just for the aggregate.
                        reached.add(head)
                        head_before = head
                        head, burst = ring.burst(head, source, sign)
                        need(
                            sum(t for _, t in burst) == sign
                            and ring.recover(head, burst)
                            == (head_before, source, sign),
                            "not a signed-flux bijection onto its image",
                        )
                        for p, s in burst:
                            observed[p] += s
                            raw_positive += s == sign
                            raw_negative += s == -sign
                        if source == 0 and start == 0:
                            signed_input = ((j + 1) * sign,) + (0,) * (d - 1)
                            worst = max(
                                worst,
                                exact_comparison(
                                    ring, start, signed_input, observed, head
                                ),
                            )
                        transitions_checked += 1
                    need(
                        len(reached) == period and head == start,
                        "wrong autonomous steady period",
                    )
                    expected = tuple(
                        sign * (F(2 * period, d) - (period if i == source else 0))
                        for i in range(d)
                    )
                    need(tuple(observed) == expected, "nonexact complete rotor orbit")
                    need(
                        F(raw_positive, period) == ideal_positive
                        and F(raw_negative, period) == ideal_negative,
                        "per-cycle emission is not optimal for this fixed sign/source",
                    )
                    need(
                        raw_positive + raw_negative == sum(map(abs, observed)),
                        "avoidable cross-event cancellations",
                    )
        need(worst == d - gcd(2, d), "the discrepancy bound was not attained")
        if d in (2, 3, 4, 5, 6, 8, 12, 31, 32):
            rows[d] = {
                "period_and_minimum_reachable_phase_states": period,
                "raw_survivors_per_input_after_same_port_cancellation": str(
                    ideal_positive + ideal_negative
                ),
                "extra_opposite_sign_pairs_per_input": str(ideal_negative),
                "sharp_error_per_port": str(F(worst, d)),
            }
    return {
        "selected_degrees": rows,
        "transitions_checked_in_fixed_source_orbits": transitions_checked,
    }


def sign_order_and_inverse_controls():
    drift_at_degrees = {}
    for d in range(3, 13):
        ring = Ring.wire(tuple(range(d)))
        length = d // gcd(d, 2)
        # The source is fixed. Repeat two rotor cycles: assign always + at
        # the first phase and always - at the second, balance other phases.
        signs = (1, -1) + (1,) * (length - 2) + (1, -1) + (-1,) * (length - 2)
        records = tuple((0, s) for s in signs)
        linear = stream(ring, 0, records)
        wrong = stream(ring, 0, records, forward_only=True)
        repeated_wrong = stream(ring, 0, records * 13, forward_only=True)
        need(
            sum(signs) == 0
            and linear[:2] == (0, (0,) * d)
            and wrong[0] == 0
            and any(wrong[1])
            and repeated_wrong[1] == tuple(13 * x for x in wrong[1]),
            "missing forward-only signed drift",
        )
        drift_at_degrees[d] = wrong[1]

    ring = Ring.wire((0, 1, 2))
    records = ((0, 1), (1, -1))
    same_port = ((0, 1), (0, -1))
    neutral = stream(ring, 0, records)
    need(
        neutral[:2] == (0, (-1, 1, 0)),
        "net zero should reset but not erase nonzero directional input",
    )
    need(
        stream(ring, 0, same_port)[:2]
        == stream(ring, 0, reversed(same_port))[:2]
        == (0, (0, 0, 0)),
        "same-source inverse bursts fail to cancel",
    )
    from_plus = ring.burst(0, *same_port[0])
    from_minus = ring.burst(0, *same_port[1])
    need(
        tally(3, from_plus[1]) != tally(3, from_minus[1]),
        "timing should still resolve distinct sign histories",
    )
    wrong_time_reverse = stream(ring, from_plus[0], from_plus[1])
    need(
        wrong_time_reverse[:2] == (1, (1, -1, 1)),
        "same-rule physical return falsely undid the burst",
    )

    _, one_record = ring.burst(0, 0, 1)
    _, three_records = ring.burst(1, 0, 1)
    need(
        sum(x * x for x in tally(3, one_record)) == 1
        and sum(x * x for x in tally(3, three_records)) == 3,
        "squared norm of an individual record burst is not a conserved wave energy",
    )

    # Independent clockwise convention can be supplied even on identical
    # reciprocal edges. This is not a graph-only head/orientation selector.
    same_edges_reverse_order = Ring.wire((0, 2, 1))
    _, reverse_orientation = same_edges_reverse_order.burst(0, 0, 1)
    need(
        reverse_orientation != one_record,
        "orientation should be detectable in short traces",
    )
    return {
        "forward_only_zero_net_drift_per_closed_block": drift_at_degrees,
        "net_zero_mixed_rails_output_and_head": neutral[:2],
        "opposite_temporal_orders_first_burst": [
            tally(3, from_plus[1]),
            tally(3, from_minus[1]),
        ],
        "same_rule_reinject_one_burst_is_not_its_inverse": wrong_time_reverse[:2],
        "raw_burst_squared_norm_at_two_heads": [1, 3],
        "short_traces_at_opposite_orientations": [one_record, reverse_orientation],
    }


def normal_order(counts: Vector):
    # A controller need not use this order. Any history with the same
    # signed port totals has precisely the same closed- or open-window sum.
    return (
        (p, 1 if a > 0 else -1) for p, a in enumerate(counts) for _ in range(abs(a))
    )


def ideal_stage(v, slots):
    common = F(2 * sum(v[p] for p in slots), len(slots))
    out = list(v)
    for p in slots:
        out[p] = common - v[p]
    return tuple(out)


def staged(counts, stages, heads):
    result = counts
    advanced = []
    stage_residual_sqnorm = []
    for head, slots in zip(heads, stages, strict=True):
        d = len(slots)
        ring = Ring.wire(tuple(range(d)))
        local = tuple(result[p] for p in slots)
        head_out, next_local, _ = stream(ring, head, normal_order(local))
        exact_comparison(ring, head, local, next_local, head_out)
        out = list(result)
        for p, a in zip(slots, next_local, strict=True):
            out[p] = a
        stage_residual_sqnorm.append(
            sum(
                (a - b) ** 2
                for a, b in zip(out, ideal_stage(result, slots), strict=True)
            )
        )
        advanced.append(head_out)
        result = tuple(out)
    return result, tuple(advanced), tuple(stage_residual_sqnorm)


def least_closing_gain(seed, stages):
    """Least alpha returning every head, not just approximating the last output."""
    acc = seed
    gain = 1
    for slots in stages:
        d = len(slots)
        period = d // gcd(2, d)
        net = F(sum(acc[i] for i in slots))
        # With all earlier heads closed, exact local net is alpha * net;
        # it must lie in period*Z. Because net is reduced, the least
        # multiple allowed here is period*denominator/gcd(period,numerator).
        gain = lcm(gain, period * net.denominator // gcd(period, net.numerator))
        acc = ideal_stage(acc, slots)
    return gain


def alpha_and_composition_controls():
    stage_slots = ((0, 1, 2), (1, 3, 2, 4), (5, 2, 3, 1, 0), (3, 4, 5))
    initial_heads = (1, 3, 4, 1)
    seed = (2, -1, 1, 0, -2, 3)
    full_gain = prod(len(slots) // gcd(2, len(slots)) for slots in stage_slots)
    fixed_gain = least_closing_gain(seed, stage_slots)
    uniform_gain = lcm(
        *(
            least_closing_gain(
                tuple(int(j == i) for j in range(len(seed))), stage_slots
            )
            for i in range(len(seed))
        )
    )
    need(
        full_gain % uniform_gain == uniform_gain % fixed_gain == 0,
        "invalid stage denominator reductions",
    )
    ideal = seed
    for slots in stage_slots:
        after = ideal_stage(ideal, slots)
        need(
            sum(v * v for v in ideal) == sum(v * v for v in after),
            "ideal reflection is not orthogonal",
        )
        ideal = after
    rows = {}
    for gain in sorted({1, 2, 3, 6, 10, 30, fixed_gain, full_gain, 2 * full_gain}):
        macro, heads, stage_errors = staged(
            tuple(gain * v for v in seed), stage_slots, initial_heads
        )
        relative_error = tuple(
            F(a, gain) - b for a, b in zip(macro, ideal, strict=True)
        )
        norm2 = sum(a * a for a in relative_error)
        # Squared triangle inequality with Cauchy-Schwarz. Exact S_d acts
        # orthogonally on each prior error, while each new error is bounded.
        need(
            norm2 <= F(len(stage_errors), gain * gain) * sum(stage_errors),
            "finite composition error bound",
        )
        need(
            (heads == initial_heads) == (gain % fixed_gain == 0),
            "exact closure gain formula",
        )
        if gain % fixed_gain == 0:
            need(
                norm2 == 0 and not any(stage_errors),
                "closed heads without exact composition",
            )
        rows[gain] = {
            "signed_output": macro,
            "heads": heads,
            "normalized_squared_error": str(norm2),
        }
    need(
        rows[1]["normalized_squared_error"] != "0",
        "unclosed composition negative control",
    )

    # Nontrivial fixed-input reduction and check all smaller gains. Fixed
    # source need not pay the uniform product. A balanced vector on each
    # selected subset closes already at alpha=1.
    reduction = (0, 0, 0, 1, 2, -2)
    reduced_gain = least_closing_gain(reduction, stage_slots)
    need(
        1 < reduced_gain < full_gain
        and least_closing_gain((0,) * len(seed), stage_slots) == 1,
        "missing gain reduction control",
    )
    for tested_seed, predicted in ((seed, fixed_gain), (reduction, reduced_gain)):
        for gain in range(1, predicted + 1):
            checked_gain = staged(
                tuple(gain * v for v in tested_seed), stage_slots, initial_heads
            )
            need(
                (checked_gain[1] == initial_heads) == (gain == predicted),
                "least gain failed exhaustive replay",
            )

    persistent_outputs = []
    reset_outputs = []
    current_heads = initial_heads
    windows = (1, 2, 13, 74)
    need(sum(windows) == full_gain, "window lengths must sum to the closing gain")
    for gain in windows:
        entered = tuple(gain * v for v in seed)
        output, current_heads, _ = staged(entered, stage_slots, current_heads)
        persistent_outputs.append(output)
        reset_outputs.append(staged(entered, stage_slots, initial_heads)[0])
    persistent = tuple(map(sum, zip(*persistent_outputs, strict=True)))
    reset = tuple(map(sum, zip(*reset_outputs, strict=True)))
    need(
        persistent == rows[full_gain]["signed_output"]
        and current_heads == initial_heads
        and reset != persistent,
        "persistent vs independent reset windows were not discriminated",
    )

    # The same nonclosing one-input window repeated R times: bias is O(R)
    # with reset, bounded without it. It is not detector sampling noise.
    ring = Ring.wire((0, 1, 2))
    singles = ((0, 1),)
    repeats = 300
    once = stream(ring, 0, singles)[1]
    repeated_reset = tuple(repeats * v for v in once)
    recurrent = stream(ring, 0, singles * repeats)[1]
    need(
        repeated_reset == (0, 300, 0) and recurrent == (-100, 200, 200),
        "fixed-phase window resets do not average",
    )
    return {
        "stage_slots": stage_slots,
        "seed": seed,
        "ideal_composed_output": tuple(map(str, ideal)),
        "sufficient_gain_product": full_gain,
        "least_gain_for_all_integer_seeds": uniform_gain,
        "least_gain_for_seed": fixed_gain,
        "gain_checks": rows,
        "fixed_seed_gain_reduction_control": {
            "seed": reduction,
            "least_gain_checked": reduced_gain,
        },
        "same_input_subdivided_signed_gain_windows": windows,
        "persistent_windows_output": persistent,
        "reinitialized_windows_output": reset,
        "one_ingress_windows_repeated_300_times": {
            "persisted": recurrent,
            "reset_to_head_zero": repeated_reset,
        },
    }


def long_history_control():
    cases = 0
    for d in (3, 4, 5, 6, 7, 8, 9, 12, 15, 16, 31):
        # Long correlated runs, switches in sign and rail, neutral insertions.
        order = tuple(range(1, d, 2)) + tuple(range(0, d, 2))
        ring = Ring.wire(order)
        word = tuple(
            (j * j % d, -1 if ((j // 17) % 3 or j % 23 == 0) else 1) for j in range(529)
        )
        for start in (0, 1, d - 1):
            for first, end in ((0, 529), (1, 171), (23, 370), (110, 529)):
                block = word[first:end]
                shifted, _, _ = stream(ring, start, word[:first])
                entered = tally(d, block)
                head, out, _ = stream(ring, shifted, block)
                exact_comparison(ring, shifted, entered, out, head)
                need(
                    stream(ring, shifted, reversed(block))[:2] == (head, out)
                    and stream(ring, shifted, sorted(block))[:2] == (head, out),
                    "order variation changed signed total",
                )
                cases += 1
    return cases


def probe():
    return {
        "scope": "exact local integer-stream transducer; mean wave columns, not single registered event distributions",
        "finite_signed_prefixes_exhausted_including_empty": exhaustive_signed_histories(),
        "long_adversarial_window_reorder_controls": long_history_control(),
        "phase_and_cost": phase_resources(),
        "negative_controls": sign_order_and_inverse_controls(),
        "finite_gain_and_composition": alpha_and_composition_controls(),
        "argument": {
            "sharp_phase_lower_bound": "at fixed source/sign the eventual orbit of any finite deterministic integer-output device must have cycle length divisible by d/gcd(d,2), by the off-diagonal rate 2/d; the reachable head orbit meets it",
            "raw_output_lower_bound": "for one fixed positive source complete-cycle survivors have no cross-event cancellations, attaining the column l1 norm 3−4/d; each extra opposite-sign pair adds two raw records; before even same-port cancellation there are three attempts per input",
            "one_output_obstruction": "if each positive ingress conserved signed flux and had exactly one unit output, every burst would be positive; the contact column's negative source entry is then impossible for d>2",
            "finite_interval": "signed visits of the oriented interval of length 2N; discrepancy vector has r entries 1−r/d and d−r entries −r/d with r=2N mod d; sharp infinity bound 1−gcd(d,2)/d",
            "finite_gain": "for input amplified by positive integer alpha the single-stage normalized error per port is less than 1/alpha; in a chain errors compose through orthogonal ideal stages; the product of reduced denominators is sufficient, not necessarily minimal, for simultaneous closure",
            "least_closing_gain": "for ideal pre-stage net a/b in lowest terms and phase period L, alpha must be divisible by bL/gcd(L,a); lcm across stages is sufficient and necessary for all heads to return, and across basis seeds gives the uniform gain",
        },
        "supplied_not_derived": [
            "the cyclic contact order, orientation, initial pointer and empty alternative output paths",
            "arrival serialization, signed unit copies and opposite-mark cancellation within a timed burst",
            "the signed aggregate, boundary windows and injected integer gain; a timing-resolved readout can distinguish histories",
            "energy reservoir, passive time-reverse implementation, and single registered event rule are not supplied by the algebra",
        ],
        "comparisons": {
            "scripts/probe_reciprocal_detector_petals.py": "one-hop rotor circulation on reciprocal petal paths; no two-copy signed reflection",
            "scripts/probe_rotor_event_stream.py": "event-selection counter per incoming tag; no signed rewind stream algebra",
            "scripts/probe_complement_collision_mixer.py": "four-port complement collisions plus supplied matching; here the primitive is signed duplication and cancellation instead",
            "prior_art": {
                "https://arxiv.org/abs/0904.4507": "Holroyd and Propp, deterministic rotor discrepancy for Markov walks; the reflected signed outputs here are not that stochastic comparator",
                "https://ar5iv.labs.arxiv.org/html/1006.1003#S4": "Friedrich and Levine, reverse stack steps when unfiring holes; not a two-copy junction or wave law",
            },
        },
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
