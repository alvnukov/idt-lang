"""Detector resources for the six-symbol relative comparator of the joint relay.

Two separated local readers are SUPPLIED with symbols in a common Z/6
frame. Alice receives x, Bob receives y; x and y are fresh independent
uniform inputs for scoring. One forward d-symbol register is the only
setting-dependent channel. Static input-independent shared randomness and
local randomization are free; output one bit on EVERY shot. This is not a
claim that separately addressable absolute symbols are observable on the
216-state quotient, which identifies simultaneous shifts by three.

MICROSCOPIC task: compute B(x,y) = [x-y in {0,1,5}] on each actual pair.
STATIC TABLE task: reproduce the public setting-conditioned probabilities
P(+|x,y) = (1+cos(pi*(x-y)/3))/2. These are not the microscopic labels.
Using B only to score the observed table gives success 5/6; two messages
cannot achieve that score, but three reproduce every table entry. Perfect
microscopic B needs six. Conditioning on all randomness reduces the
strategy to an Alice partition and Bob's majority on each (message,y).
At a given offset the trit names one adjacent pair. Across the two fair
offsets the partner is equally likely to be x-1 or x+1. Fair ties give
P(+|x,y)=(2B(x,y)+B(x-1,y)+B(x+1,y))/4 exactly.

The raw shuttle role toggles regardless of the addressed cell. Its
projection to (role, Bob cell) is closed under any fixed address word,
so it does not supply even a signal of Alice's cell through that cut.
A mobile six-symbol accumulator and detector are an added positive control,
not a new primitive of the relay or a general no-go for other mechanisms.

The separate eight-station Z/6 task gives a different bound: only the live
register spans each cut, the fresh independent dials add mod six, and
score is E[Y cos(pi sum/3)] with terminal output mean in [-1,1]. For
w=exp(i*pi/3), the unnormalized conditional first Fourier moments update
with l1 contraction at most C_d per cut. For each input state this follows
from triangle inequality and the maximum, over partitions into d bins, of
the sum of bin resultants of w^x divided by six. Convexity covers stochastic
kernels. The terminal reader has binary-result factor C_2, including any
mean zero. Thus five dynamic symbols give |score| <= C_2 C_5^7 < 1/2,
even with arbitrary time dependence and input-independent shared seeds.
This is neither a two-reader bound nor a quantum derivation.

Run: python3 -B -O -m scripts.probe_local_phase_comparator
"""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Iterator
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product

from scripts.probe_joint_relay_phase import BRIGHT, ROW, A, B, model, prepared
from scripts.probe_shuttle_local_reunions import PORTS, ring, tables, walk

Q = 6
SYMBOLS = tuple(range(Q))
BITS = (0, 1)
TARGET = (4, 3, 1, 0, 1, 3)
HEX = ((2, 0), (1, 1), (-1, 1), (-2, 0), (-1, -1), (1, -1))
Partition = tuple[tuple[int, ...], ...]
Radical = tuple[int, int]  # coefficients of 1, sqrt(3)


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def bright(x: int, y: int) -> bool:
    return (x - y) % Q in BRIGHT


def partitions() -> Iterator[Partition]:
    def extend(blocks: Partition, x: int) -> Iterator[Partition]:
        if x == Q:
            yield blocks
            return
        for i, block in enumerate(blocks):
            yield from extend(blocks[:i] + (block + (x,),) + blocks[i + 1 :], x + 1)
        yield from extend(blocks + ((x,),), x + 1)

    yield from extend((), 0)


def optimal_win_count(partition: Partition) -> int:
    correct = 0
    for block, y in product(partition, SYMBOLS):
        yes = sum(bright(x, y) for x in block)
        correct += max(yes, len(block) - yes)
    return correct


def deterministic_win_count(partition: Partition) -> int:
    message = {x: k for k, block in enumerate(partition) for x in block}
    reader = {
        (k, y): 2 * sum(bright(x, y) for x in block) >= len(block)
        for k, block in enumerate(partition)
        for y in SYMBOLS
    }
    return sum(
        reader[message[x], y] == bright(x, y) for x, y in product(SYMBOLS, repeat=2)
    )


def exact_bounds(pools: tuple[Partition, ...]) -> list[int]:
    counts = Counter(map(len, pools))
    need(len(set(pools)) == len(pools) == 203, "lost or duplicated partitions")
    need(
        [counts[d] for d in range(1, Q + 1)] == [1, 31, 90, 65, 15, 1],
        "partition counts",
    )
    best = [0] * Q
    for p in pools:
        correct = optimal_win_count(p)
        need(correct == deterministic_win_count(p), "majority strategy replay")
        for i in range(len(p) - 1, Q):
            best[i] = max(best[i], correct)
    need(best == [18, 28, 30, 32, 34, 36], "deterministic comparator score bounds")
    need(
        len({tuple(bright(x, y) for y in SYMBOLS) for x in SYMBOLS}) == Q,
        "perfect truth must distinguish all six Alice rows",
    )
    return best


def encode(x: int, offset: int) -> int:
    return (x - offset) % Q // 2


def decode(message: int, y: int, offset: int, tie: int) -> bool:
    a = (offset + 2 * message) % Q
    votes = int(bright(a, y)) + int(bright((a + 1) % Q, y))
    return votes == 2 or (votes == 1 and tie == 1)


def trit_table() -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(
            sum(decode(encode(x, b), y, b, coin) for b, coin in product(BITS, repeat=2))
            for y in SYMBOLS
        )
        for x in SYMBOLS
    )


def relay_table() -> tuple[tuple[int, ...], ...]:
    relay = model(Q, identify=True)
    need(
        len(relay.reps) == 216 and BRIGHT == {0, 1, 5} and ROW == TARGET,
        "frozen comparator inputs",
    )
    histories = prepared(relay)
    need(
        tuple(relay.phase(s) for s in histories) == (5, 0, 0, 1),
        "frozen preparation histories",
    )
    # Both signed public dials act on the same four histories with the same analyzer.
    return tuple(
        tuple(
            sum(
                relay.phase(walk(relay.ports, s, A * x + B * y)) in BRIGHT
                for s in histories
            )
            for y in SYMBOLS
        )
        for x in SYMBOLS
    )


def static_controls(table: tuple[tuple[int, ...], ...]) -> dict[str, object]:
    expected = tuple(tuple(TARGET[(x - y) % Q] for y in SYMBOLS) for x in SYMBOLS)
    need(table == expected == relay_table(), "not the entire public 6x6 table")
    correct = sum(
        table[x][y] if bright(x, y) else 4 - table[x][y]
        for x, y in product(SYMBOLS, repeat=2)
    )
    score = F(correct, 4 * Q**2)
    need(score == F(5, 6) > F(28, 36), "the two-symbol bound must exclude the target")

    # Leakage: disguise the high encoder bit as a marginally fair bit L.
    # Together with the mask R already known to Bob it carries an extra
    # input-dependent bit. Its fair one-bit marginal is no independence test.
    joint_seed_distributions: set[tuple[tuple[int, int, int], ...]] = set()
    for x in SYMBOLS:
        seen: list[tuple[int, int, int]] = []
        for b in BITS:
            message = encode(x, b)
            binary = message & 1
            leaked = tuple((message >> 1) ^ mask for mask in BITS)
            need(sorted(leaked) == list(BITS), "leak marginal is not fair")
            for mask, bit in zip(BITS, leaked, strict=True):
                seen.append((b, mask, bit))
                restored = ((bit ^ mask) << 1) | binary
                need(
                    restored == message,
                    "leaked seed and binary channel must reconstruct trit",
                )
                need(
                    all(
                        decode(restored, y, b, coin) == decode(message, y, b, coin)
                        for y, coin in product(SYMBOLS, BITS)
                    ),
                    "leakage replay",
                )
        joint_seed_distributions.add(tuple(seen))
    need(
        len(joint_seed_distributions) > 1,
        "full purported seed remained independent of x",
    )

    # Loss: with shared fair guess g, one sent bit flags x=g. Only that
    # branch clicks, so efficiency is 1/6 at EACH setting pair, yet the
    # retained shot is perfectly correct. Keep all other shots as fair bits.
    total_retained = retained_wins = filled_wins = total_shots = 0
    for x, y in product(SYMBOLS, repeat=2):
        retained = 0
        for guess, coin in product(SYMBOLS, BITS):
            sent = int(x == guess)
            outcome = bright(guess, y) if sent else bool(coin)
            retained += sent
            retained_wins += sent * int(outcome == bright(x, y))
            filled_wins += outcome == bright(x, y)
            total_shots += 1
        need(retained == len(BITS), "loss is not uniform for every pair of settings")
        total_retained += retained
    efficiency = F(total_retained, total_shots)
    postselected = F(retained_wins, total_retained)
    filled = F(filled_wins, total_shots)
    need(efficiency == F(1, 6) and postselected == 1, "conditional perfect loss spoof")
    need(filled == F(7, 12), "lost emissions were not included in score")
    return {
        "brightness_quarter_numerators_by_public_setting_pair": table,
        "success_against_microscopic_truth": str(score),
        "messages_for_entire_public_table": 3,
        "messages_for_perfect_microscopic_truth": 6,
        "leaked_marginally_fair_seed_exactly_spoofs_trit_table_with_counted_binary": True,
        "binary_loss_spoof": {
            "efficiency_at_every_setting_pair": str(efficiency),
            "success_if_misses_dropped": str(postselected),
            "success_with_all_misses_filled_fairly": str(filled),
        },
    }


def raw_cut_control() -> dict[str, object]:
    """Verify the raw projected generator for every state/Bob/address choice."""
    ports = tables(Q, ring(Q))
    local_checks = 0
    for bob, addressed, state in product(PORTS, PORTS, range(len(ports[0]))):
        stride = Q**bob
        old_role, y = state // Q**4, state // stride % Q
        target = ports[addressed][state]
        new_role, received = target // Q**4, target // stride % Q
        bob_shift = (1 if old_role == 0 else -1) if addressed == bob else 0
        need(
            (new_role, received) == (old_role ^ 1, (y + bob_shift) % Q),
            "raw local projection",
        )
        local_checks += 1
    # The canonical quotient representative can shift all coordinates by
    # three. Bob's own coordinate modulo three descends without needing
    # access to that global representative choice.
    relay = model(Q, identify=True)
    quotient_checks = 0
    for bob, addressed, site in product(PORTS, PORTS, range(len(relay.reps))):
        role = relay.role(site)
        target = relay.ports[addressed][site]
        bob_shift = (1 if role == 0 else -1) if addressed == bob else 0
        need(
            (relay.role(target), relay.symbol(target, bob) % 3)
            == (role ^ 1, (relay.symbol(site, bob) + bob_shift) % 3),
            "gauge-invariant Bob projection on quotient",
        )
        quotient_checks += 1
    return {
        "raw_states_including_all_components": len(ports[0]),
        "exact_local_projection_checks": local_checks,
        "gauge_invariant_quotient_projection_checks": quotient_checks,
        "bob_view_closed_under_every_input_independent_address_word": True,
        "no_signal_from_alice_cell_in_this_cut": True,
    }


@dataclass(frozen=True)
class Carrier:
    location: str
    value: int

    def visit(self, here: str, local_symbol: int, sign: int) -> Carrier:
        need(
            self.location == here and local_symbol in SYMBOLS and sign in (-1, 1),
            "not a local visit",
        )
        return Carrier(here, (self.value + sign * local_symbol) % Q)

    def move(self) -> Carrier:
        need(self.location in ("Alice", "Bob"), "not a wire endpoint")
        return Carrier("Bob" if self.location == "Alice" else "Alice", self.value)

    def write_flag(self, previous: int) -> int:
        need(self.location == "Bob" and previous in BITS, "not a detector-local flag")
        return previous ^ int(bright(self.value, 0))


def mobile_control() -> dict[str, object]:
    for x, y, initial, flag in product(SYMBOLS, SYMBOLS, SYMBOLS, BITS):
        source = Carrier("Alice", initial)
        # Each visit reads only the symbol at the carrier's current endpoint.
        loaded = source.visit("Alice", x, +1)
        at_detector = loaded.move().visit("Bob", y, -1)
        written = at_detector.write_flag(flag)
        need(
            at_detector.value == (initial + x - y) % Q, "wrong mobile relative residue"
        )
        need(
            written == flag ^ int(bright((initial + x) % Q, y)),
            "mobile comparator mismatch",
        )
        need(at_detector.write_flag(written) == flag, "output XOR is not reversible")
        # Optional cleanup, after the one-forward measurement, uses a
        # return traversal but leaves the copied detector bit untouched.
        back = at_detector.visit("Bob", y, +1).move().visit("Alice", x, -1)
        need(back == source, "carrier reset without the inverse visits")
    return {
        "forward_register_symbols": Q,
        "two_local_reversible_updates": ["m <- m+x at Alice", "m <- m-y at Bob"],
        "detector_operation": "flag <- flag XOR bright(m,0)",
        "microscopic_comparator_with_ready_m0": "perfect",
        "six_residue_register_not_a_native_shuttle_property": True,
        "optional_uncompute_requires_a_return_trip": True,
    }


def radical_positive(a: int, b: int) -> bool:
    if a >= 0 and b >= 0:
        return bool(a or b)
    if a <= 0 and b <= 0:
        return False
    if a > 0:
        return a * a > 3 * b * b
    return 3 * b * b > a * a


def radical_mul(p: Radical, q: Radical) -> Radical:
    a, b = p
    c, d = q
    return a * c + 3 * b * d, a * d + b * c


def max_resultants(pools: tuple[Partition, ...], symbols: int) -> Radical:
    # Lengths of subsets of sixth roots, via exact doubled hex coordinates.
    norms = {0: (0, 0), 4: (1, 0), 12: (0, 1), 16: (2, 0)}
    best = (0, 0)
    for p in pools:
        if len(p) > symbols:
            continue
        a = b = 0
        for block in p:
            u = sum(HEX[x][0] for x in block)
            v = sum(HEX[x][1] for x in block)
            c, d = norms[u * u + 3 * v * v]
            a, b = a + c, b + d
        if radical_positive(a - best[0], b - best[1]):
            best = a, b
    return best


def sequential_control(pools: tuple[Partition, ...]) -> dict[str, object]:
    terminal, five, six = (max_resultants(pools, d) for d in (2, 5, 6))
    need(
        (terminal, five, six) == ((4, 0), (4, 1), (6, 0)), "wrong Fourier contractions"
    )
    seven_steps = terminal
    for _ in range(6):
        seven_steps = radical_mul(seven_steps, five)
    eight_steps = radical_mul(seven_steps, five)
    a, b = eight_steps
    den = Q**8
    need(
        radical_positive(den - 2 * a, -2 * b),
        "five states not excluded at eight stations",
    )
    u, v = seven_steps
    need(
        radical_positive(2 * u - Q**7, 2 * v),
        "this certificate already excludes at seven stations",
    )

    hist = [1, 0, 0, 0, 0, 0]
    for _ in range(8):
        hist = [sum(hist[(residue - x) % Q] for x in SYMBOLS) for residue in SYMBOLS]
    need(hist == [Q**7] * Q, "six-state accumulator residue counts")
    mean = tuple(F(2 * n - 4, 4) for n in TARGET)
    cos = tuple(F(real, 2) for real, _ in HEX)
    need(mean == cos, "readout means changed")
    score = sum((hist[s] * mean[s] * cos[s] for s in SYMBOLS), F(0)) / den
    need(score == F(1, 2), "six-symbol sequential comparator score")
    return {
        "distinct_fresh_dials": 8,
        "five_dynamic_symbols_exact_score_bound": f"({a}+{b}*sqrt(3))/{den}",
        "five_dynamic_symbols_bound_below_1/2": True,
        "six_symbol_accumulator_score": str(score),
        "at_least_six_dynamic_symbols_in_this_sequential_model": True,
    }


def main() -> None:
    pools = tuple(partitions())
    report = {
        "one_way_microscopic_game": {
            "unordered_partitions": len(pools),
            "maximum_correct_out_of_36_by_message_alphabet_size_1_through_6": exact_bounds(
                pools
            ),
        },
        "static_public_table": static_controls(trit_table()),
        "native_raw_shuttle_control": raw_cut_control(),
        "added_reversible_mobile_carrier": mobile_control(),
        "distinct_sequential_task": sequential_control(pools),
        "boundary": [
            "The prepared source, common symbol frame, addressed visits, comparator and readout remain supplied.",
            "No input-dependent side channel, writable shared reference, loss normalization or hidden communication is free.",
            "Perfect microscopic truth is stronger than reproducing the observed setting-conditioned probabilities.",
            "No general comparator impossibility, amplitudes, Born rule, detector mechanism, or QM derivation.",
        ],
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
