"""Test whether a reversible integer bucket lifts overlapping wave gates.

For support G of size d, write 2*sum(x_G)+r_G = d*q+r'_G, 0<=r'_G<d.
Replace x_G by -x_G+q and update only r_G. This is an involution and
conserves total signed flux sum(x)+sum(r). On an isolated support it
exactly reflects the local corrected vector x_G+(r_G/d)*1_G.

Across supports, the simple global decoder x+sum_h(r_h/d_h)*1_h has
defect sum_{h!=G}(r_h/d_h)*(I-S_G)*1_h. Each term vanishes if support h
is disjoint from G or contains G. The summed defect vanishes exactly
when the other buckets' joint correction is constant on G. On clean
integer input any d>=3 slot can get dirty in one shot; a d=2 slot
never gets dirty. The directed criterion is necessary across *all*
clean seeds and addressed words, not for every fixed seed and context.

We also test decoder impossibility, denominator growth, and a nested
clean-state drift. This is a mathematical audit of this scheduled state
rule; it assumes addressed gates, persistent buckets, synchronized integer
batches and an ideal comparison map. It does not reject a different
integer-lattice construction or a physical wave/measurement mechanism.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, prod

Support = tuple[int, ...]
Raw = tuple[int, ...]


def need(condition, message):
    if not condition:
        raise ArithmeticError(message)


def basis(size: int, j: int) -> Raw:
    return tuple(int(i == j) for i in range(size))


def l2sq(v):
    return sum(a * a for a in v)


def difference(a, b):
    return tuple(x - y for x, y in zip(a, b, strict=True))


def readable(v):
    return tuple(map(str, v))


def matvec(matrix, v):
    return tuple(sum(a * b for a, b in zip(row, v, strict=True)) for row in matrix)


@dataclass(frozen=True)
class State:
    x: Raw
    r: Raw


@dataclass(frozen=True)
class Network:
    size: int
    supports: tuple[Support, ...]

    def clean(self, x: Raw) -> State:
        need(len(x) == self.size and all(type(a) is int for a in x), "bad clean field")
        return State(x, (0,) * len(self.supports))

    def fire(self, state: State, gate: int) -> State:
        ports = self.supports[gate]
        d = len(ports)
        nxt = list(state.x)
        q, rem = divmod(2 * sum(state.x[i] for i in ports) + state.r[gate], d)
        for i in ports:
            nxt[i] = q - state.x[i]
        residues = list(state.r)
        residues[gate] = rem
        return State(tuple(nxt), tuple(residues))

    def decode(self, state: State):
        x = list(map(F, state.x))
        for r, ports in zip(state.r, self.supports, strict=True):
            for i in ports:
                x[i] += F(r, len(ports))
        return tuple(x)

    def defect(self, state: State, gate: int):
        """Independent rank-one overlap formula, not differences of two runs."""
        ports = self.supports[gate]
        d = len(ports)
        defect = [F(0)] * self.size
        for other, (r, h) in enumerate(zip(state.r, self.supports, strict=True)):
            if other == gate or r == 0:
                continue
            intersection = set(ports).intersection(h)
            w = F(2 * r, len(h))
            for i in ports:
                defect[i] += w * (int(i in intersection) - F(len(intersection), d))
        return tuple(defect)

    def verified_fire(self, state: State, gate: int) -> State:
        nxt = self.fire(state, gate)
        need(self.fire(nxt, gate) == state, "bucket involution or signed floor failed")
        need(
            sum(nxt.x) + sum(nxt.r) == sum(state.x) + sum(state.r),
            "lost corrected signed flux",
        )
        need(
            all(0 <= r < len(g) for r, g in zip(nxt.r, self.supports, strict=True)),
            "bad remainder",
        )
        roles = self.supports[gate]
        defect = difference(
            self.decode(nxt), wave(state_v=self.decode(state), ports=roles)
        )
        need(defect == self.defect(state, gate), "wrong signed overlap defect")
        need(
            not sum(defect)
            and all(not v for i, v in enumerate(defect) if i not in roles),
            "defect must be zero-sum and supported on active gate",
        )
        return nxt


def wave(state_v, ports: Support):
    t = F(2 * sum(state_v[i] for i in ports), len(ports))
    return tuple(t - a if i in ports else a for i, a in enumerate(state_v))


def wave_word(seed, supports, word):
    v = seed
    for g in word:
        after = wave(v, supports[g])
        need(
            l2sq(v) == l2sq(after) and sum(v) == sum(after),
            "ideal reflection changed norm or flux",
        )
        v = after
    return v


def run(net: Network, state: State, word) -> State:
    for g in word:
        state = net.verified_fire(state, g)
    return state


def show(state: State):
    return {"x": state.x, "r": state.r}


def pair_characterization():
    failing_accessible = 0
    formal_only = 0
    directed_pairs_tested = 0
    classifications = {}
    for n in range(2, 6):
        supports = tuple(a for d in range(2, n + 1) for a in combinations(range(n), d))
        for h, g in product(supports, repeat=2):
            net = Network(n, (h, g))
            direction_bad = bool(set(h).intersection(g) and not set(g).issubset(h))
            formal = State((0,) * n, (1, 0))
            net.verified_fire(formal, 1)
            need(
                any(net.defect(formal, 1)) == direction_bad,
                "wrong directed formal support classification",
            )
            directed_pairs_tested += 1
            # All single-h residue values generated from the integer sum j.
            # Pick just one rail on h during this reachability witness.
            i = next(iter(set(h).intersection(g)), h[0])
            reachable = set()
            for s in range(len(h)):
                clean = net.clean(tuple(s * a for a in basis(n, i)))
                dirty = net.verified_fire(clean, 0)
                net.verified_fire(dirty, 1)
                reachable.add(dirty.r[0])
                need(
                    any(net.defect(dirty, 1)) == bool(direction_bad and dirty.r[0]),
                    "wrong accessible support test",
                )
            need(
                reachable == set(range(0, len(h), gcd(2, len(h)))),
                "single-contact residue reachability",
            )
            if direction_bad and len(h) == 2:
                formal_only += 1
            if direction_bad and len(h) >= 3:
                # All clean-preserving additive decoders x+f(r) fail,
                # not merely linear f. Fire h from residue zero to force
                # f(2e_h)=2/d_h 1_h; cancel the raw active g sum with a
                # port of g\h so firing g leaves all residues unchanged.
                j = next(iter(set(g) - set(h)))
                seed = tuple(
                    a + b for a, b in zip(basis(n, i), basis(n, j), strict=True)
                )
                initial = net.clean(seed)
                dirty = net.verified_fire(initial, 0)
                after = net.verified_fire(dirty, 1)
                need(
                    dirty.r == after.r == (2, 0) and sum(dirty.x[p] for p in g) == 0,
                    "bad witness holding the entire residue fixed",
                )
                forced_f = difference(wave(seed, h), dirty.x)
                need(
                    forced_f == tuple(F(2, len(h)) if k in h else 0 for k in range(n)),
                    "wrong forced f(r)",
                )
                need(
                    wave(dirty.x, g) == after.x and forced_f != wave(forced_f, g),
                    "nonlinear additive decoder countercontrol",
                )
                failing_accessible += 1
            key = f"{len(h)}:{len(g)}:{len(set(h).intersection(g))}"
            classifications[key] = direction_bad and len(h) >= 3
    return {
        "directed_pairs_exhausted_through_five_ports": directed_pairs_tested,
        "directed_pairs_with_reachable_failure_and_forced_additive_decoder_obstruction": failing_accessible,
        "extra_formal_only_failures_with_unreachable_swap_correction": formal_only,
        "class_rule": "dirty-capable source h with |h|>=3 forces receiving g to be disjoint from h or contained in h",
        "required_receiving_permitted_two_way": "large supports identical or disjoint; swaps may be contained or disjoint; arbitrary overlaps between swaps",
        "tested_distinct_size_overlap_profiles": len(classifications),
    }


def minimal_witnesses():
    h = (0, 1, 2)
    seed = (1, 0, 0, 0)
    outputs = {}
    for name, g in (
        ("swap_straddles_triple", (2, 3)),
        ("two_triples", (1, 2, 3)),
        ("triple_inside_quartet", (0, 1, 2, 3)),
    ):
        net = Network(4, (h, g))
        clean = net.clean(seed)
        dirty = net.verified_fire(clean, 0)
        final = net.verified_fire(dirty, 1)
        ideal = wave_word(seed, net.supports, (0, 1))
        decoded = net.decode(final)
        need(
            net.decode(dirty) == wave(seed, h) and decoded != ideal,
            "not a minimal length-two witness",
        )
        need(run(net, final, (1, 0)) == clean, "explicit inverse schedule failed")
        if name != "triple_inside_quartet":
            # NO decoder of the entire state (whether additive or not):
            # the second rule fixes the raw state pointwise yet its ideal
            # wave changes the state forced by the single clean first step.
            need(
                final == dirty,
                "expected the second addressed bucket to fix the entire raw state",
            )
        else:
            need(
                l2sq(decoded) == F(5, 3) and l2sq(ideal) == 1,
                "expected a nonconserved global decoded norm",
            )
            reverse = run(net, clean, (1, 0))
            need(
                net.decode(reverse) == ideal,
                "big-dirty then small is the allowed direction",
            )
        outputs[name] = {
            "dirty": show(dirty),
            "after_second": show(final),
            "proposed_decode": readable(decoded),
            "ideal": readable(ideal),
            "defect": readable(difference(decoded, ideal)),
            "decoded_squared_norm": str(l2sq(decoded)),
        }
    # Joint cancellation: the two independent dirty triples contribute
    # opposite defects on a final straddling swap. This state is reachable.
    net = Network(6, ((0, 1, 2), (3, 4, 5), (0, 3)))
    clean = net.clean((1, 0, 0, 1, 0, 0))
    dirty = run(net, clean, (0, 1))
    need(
        dirty.r == (2, 2, 0) and not any(net.defect(dirty, 2)),
        "missing accessible cancellation of overlap defects",
    )
    need(
        any(net.defect(run(net, clean, (0,)), 2)), "single dirty term unexpectedly zero"
    )
    outputs["reachable_multi_bucket_defect_cancellation"] = show(dirty)
    return outputs


def denominator_growth():
    rows = {}
    h = (0, 1, 2)
    seed = (1, 0, 0, 0)
    for name, g, base, contrast, sign, plane_trace, support in (
        ("swap_and_triple", (2, 3), 3, (1, -1, 0, 0), -1, F(-2, 3), (0, 1, 3)),
        ("two_triples", (1, 2, 3), 9, (0, 1, -1, 0), 1, F(-14, 9), (1, 2, 3)),
    ):
        staged = (h, g)
        columns = tuple(wave_word(basis(4, j), staged, (0, 1)) for j in range(4))
        need(
            all(
                sum(a * b for a, b in zip(c, d, strict=True)) == int(i == j)
                for i, c in enumerate(columns)
                for j, d in enumerate(columns)
            ),
            "ideal map not orthogonal",
        )
        trace = sum(c[j] for j, c in enumerate(columns))
        need(
            wave_word((1,) * 4, staged, (0, 1)) == (1,) * 4
            and wave_word(contrast, staged, (0, 1))
            == tuple(sign * a for a in contrast),
            "wrong split-off real eigenvalues",
        )
        # Each star has d-1 negative eigenvalues. After splitting off +1
        # and 'sign', restriction to the orthogonal plane has det +1.
        det = (-1) ** (len(h) + len(g) - 2)
        need(
            trace - 1 - sign == plane_trace and det == sign,
            "wrong two-dimensional rotation invariant",
        )

        raw_matrix = tuple(
            tuple(base * a for a in row) for row in zip(*columns, strict=True)
        )
        need(
            all(x.denominator == 1 for row in raw_matrix for x in row),
            "wrong matrix denominator",
        )
        matrix = tuple(tuple(map(int, row)) for row in raw_matrix)

        residues = tuple(int(i in support) * 2 for i in range(4))
        need(
            all(
                matrix[i][j] % 3 == residues[i] * int(j in h)
                for i in range(4)
                for j in range(4)
            ),
            "wrong nonzero rank-one reduction of scaled map modulo three",
        )
        need(
            tuple(x % 3 for x in matvec(matrix, residues)) == residues,
            "mod-three surviving image must be fixed",
        )
        state = seed
        v = seed
        denominators = []
        for k in range(1, 11):
            state = matvec(matrix, state)
            v = wave_word(v, staged, (0, 1))
            den = base**k
            need(
                v == tuple(F(a, den) for a in state),
                "scaled matrix power differs from replayed word",
            )
            need(
                tuple(a % 3 for a in state) == residues
                and all(v[j].denominator == den for j in support),
                "partial cancellation erased full denominator growth",
            )
            denominators.append(den)
        rows[name] = {
            "plane_trace_equals_2cos": str(plane_trace),
            "growth_base": base,
            "first_ten_exact_denominators": denominators,
            "persistent_numerators_mod_three": residues,
            "coordinates_with_exact_denominator": support,
        }
    return rows


def nested_clean_obstructions():
    seed4 = (1, 0, 0, 0)
    net = Network(4, ((0, 1, 2), (0, 1, 2, 3)))
    initial = net.clean(seed4)
    word = (0, 1) * 3
    cycle = [show(run(net, initial, word[: 2 * k])) for k in range(1, 4)]
    ideal = wave_word(seed4, net.supports, word)
    need(
        run(net, initial, word) == initial and ideal != seed4,
        "missing nested clean return obstruction",
    )
    need(
        wave_word(seed4, net.supports, (0, 1, 0, 1)) == seed4,
        "nested ideal products must commute and square to one",
    )

    net = Network(5, ((0, 1, 2, 3), (0, 1, 2, 3, 4)))
    seed5 = (1, 0, 0, 0, 0)
    initial5 = net.clean(seed5)
    delta = (-1, -1, -1, -1, 4)
    orbit_word = (0, 1) * 10
    after_one = run(net, initial5, orbit_word)

    def shift(state, n):
        return State(
            tuple(x + n * t for x, t in zip(state.x, delta, strict=True)), state.r
        )

    need(
        sum(delta) == 0 and len({delta[i] for i in net.supports[0]}) == 1,
        "delta shift invariants",
    )
    need(
        after_one == shift(initial5, 1)
        and wave_word(seed5, net.supports, orbit_word) == seed5,
        "missing clean drift against a bounded period-two comparator",
    )
    # General translation symmetry: the h local sum shifts by a multiple
    # of d_h, hence q_h shifts by twice its uniform translation and the
    # residue stays put. The g sum doesn't shift and q_g stays put, so
    # the field translation reverses. An even number of g acts gives
    # equivariance, yielding unbounded clean drift by induction.
    drift = []
    state = initial5
    for k in range(5):
        need(
            state == shift(initial5, k),
            "nonlinear saturation of the predicted arithmetic drift",
        )
        for g in range(2):
            need(
                net.fire(shift(state, 1), g)
                == shift(net.fire(state, g), 1 if g == 0 else -1),
                "failed independent translation symmetry check",
            )
        drift.append(show(state))
        state = run(net, state, orbit_word)
    need(
        run(net, state, reversed(orbit_word * len(drift))) == initial5,
        "drift must still be fully reversible",
    )
    return {
        "triple_inside_quartet_odd_clean_return": {
            "raw_two_gate_blocks": cycle,
            "ideal_after_three_blocks": readable(ideal),
        },
        "quartet_inside_quintet_unbounded_clean_drift": {
            "delta_per_ten_two_gate_blocks": delta,
            "first_five_clean_endpoints": drift,
            "ideal_at_each_of_these_endpoints": seed5,
        },
    }


def schedule_controls():
    net = Network(5, ((0, 1, 2), (1, 2, 3, 4), (1, 3)))
    seed = (2, -1, 1, 0, -2)
    word = (0, 1, 2, 1, 0, 2, 0, 1)
    ideal = wave_word(seed, net.supports, word)
    periods = tuple(len(g) // gcd(2, len(g)) for g in net.supports)
    closing_gain = prod(periods[g] for g in word)
    counts = {}
    for gain in (1, 2, 9, 27, closing_gain):
        initial = net.clean(tuple(gain * a for a in seed))
        actual = run(net, initial, word)
        need(
            run(net, actual, reversed(word)) == initial,
            "reverse full schedule corrupted an integer seed",
        )
        error = difference(tuple(F(x, gain) for x in actual.x), ideal)
        # Each uncorrected local defect is a constant on its active ports
        # with magnitude <= 1−1/L; the ideal propagators are orthogonal.
        variance_bound = sum(
            len(net.supports[g]) * ((1 - F(1, periods[g])) ** 2) for g in word
        )
        squared_bound = F(len(word), gain * gain) * variance_bound
        need(
            l2sq(error) <= squared_bound,
            "finite-word global error exceeded propagated local bounds",
        )
        if gain == closing_gain:
            need(
                not any(error) and not any(actual.r),
                "pre-gained product must close each addressed step",
            )
            entry = initial
            for g in word:
                entry = net.verified_fire(entry, g)
                need(not any(entry.r), "sufficient gain failed a prefix closure")
        counts[gain] = {
            "raw": show(actual),
            "normalized_error_squared": str(l2sq(error)),
            "upper_bound": str(squared_bound),
        }
    need(
        counts[1]["normalized_error_squared"] != "0",
        "gain control lacks an open-prefix comparator",
    )

    commuting = Network(7, ((0, 1, 2), (0, 2), (0, 1, 2), (3, 4, 5, 6)))
    clean = commuting.clean((2, 0, -1, -3, 2, 0, 0))
    allowed = (0, 3, 1, 2, 3, 1, 0, 2)
    dirty = run(commuting, clean, allowed[:2])
    need(
        dirty.r[0] == dirty.r[3] == 2,
        "compatible control did not dirty both disjoint blocks",
    )
    end = clean
    for j, g in enumerate(allowed, start=1):
        end = commuting.verified_fire(end, g)
        need(
            commuting.decode(end)
            == wave_word(clean.x, commuting.supports, allowed[:j]),
            "failed contained-swap/disjoint/identical positive control",
        )
    return {
        "fixed_word_gain_tests": counts,
        "ideal_fixed_word": readable(ideal),
        "product_gain_sufficient_for_each_clean_step": closing_gain,
        "compatible_schedule_end": show(end),
    }


def probe():
    return {
        "scope": "reversible addressed integer bucket and its ideal rational wave comparator; no physics or event law",
        "pair_characterization": pair_characterization(),
        "minimal_witnesses": minimal_witnesses(),
        "unbounded_ideal_denominators": denominator_growth(),
        "nested_clean_obstructions": nested_clean_obstructions(),
        "controls": schedule_controls(),
        "proof_boundaries": {
            "arbitrary_state_decoder": "a clean one-step forces D(s); a following gate fixes s yet changes S_G D(s), so no function of the entire stored state works in the incomparable examples. The nested clean endpoint also independently forces a contradiction.",
            "any_additive_decoder": "a clean single firing of dirty-capable h forces f(2e_h)=2/d_h on h. In every bad direction choose a clean seed making firing g leave all residues unchanged; its ideal wave changes that forced offset, contradicting any x+f(r).",
            "finite_auxiliary_extension_bounded_denominators": "an exact infinite ideal orbit with denominators 3^k or 9^k cannot fit finitely many reachable rational offsets x+f(r); with any uniformly bounded displacement decoder, exact norm conservation would force bounded integer x and only finitely many joint states",
            "clarify_approximation": "local errors have a finite-word divided-by-gain bound and can be removed by a sufficient finite integer gain for a predeclared word. No fixed finite denominator, gain or final zero residue proves every word exact.",
            "physical_scope": "addressed schedules, time boundaries and bucket operation supplied. Raw flux, reversibility and static finite control do not imply norm preservation, physical unitary scattering, or single-event weights.",
        },
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
