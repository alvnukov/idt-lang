"""Can the detector identify which of three late local plate settings differs?

Each heralded trial starts BEFORE three independently uniform local bits are
drawn. Distinct isolated controllers hold one bit each; the same-duration
plate windows are used for all eight bit strings. Guess a port. Score one if
it is the unique exceptional bit, zero on uniform strings, loss, double
clicks or wrong answers. The six nonconstant patterns can equivalently be
written b_j = t XOR [j=s] for independent uniform s and t. The complement
t is an unobservable common sign ON THE PAIRED CODE, not a controller input.
The all-eight score needs no promise, discarded uniform rows, or central
oracle knob. Record settings for scoring only AFTER recording the output.

Classical null: during a trial the information that can reach the output
depends on at most k distinct individual plate bits. The order can be
adaptive, the queries can read the whole bit, and the source/receiver can
have any memory, local randomness, shared seeds or prior histories that
are independent of the fresh bits. A repeated read of a known bit conveys
no new information in this model. A classical field, empty-arm state, or
controller sending information from three settings is NOT in the k=2 null.
The null is about settings contacted, not the number of physical devices
updated, particle paths measured or internal symbols stored. Clock, power,
herald, data-bus, and detector side channels must be isolated; calibrating
single-port intensities does not establish this isolation.

Coherent comparison: the existing signed-count paired-rail construction has
two addressed mixers preparing logical probabilities (1/2,1/4,1/4). Apply
one local sign per chosen logical pair; follow with the reflection about
the prepared state and the ordinary grouped port readout. All eight
interventions have the same time slots. This is a short explicit example of
amplitude amplification, NOT a new search algorithm: see Grover
(https://arxiv.org/abs/quant-ph/9605043) and Brassard et al.
(https://arxiv.org/abs/quant-ph/0005055). It needs no ideal equal tritter.

The coherent preparation, sign action, coherent recombination, addressable
rails, pre-choice herald and intensity readout are supplied. This is a
finite circuit and contact-bound calculation, not a solar-neutrino
intervention, an experimental measurement or a derivation of a physical
oracle, quantum mechanics, the Born rule or spacetime locality.
Run: python3 -B -m scripts.probe_three_arm_setting_contacts (also with -O).
"""

from __future__ import annotations

from fractions import Fraction as F
from functools import cache
from itertools import product

from scripts import gaussian_dyadic_words as gauss
from scripts import probe_paired_rail_encoding as rail

PORTS = range(3)
BITS = tuple(product((0, 1), repeat=3))
U = (rail.cross(0, 1), rail.cross(1, 2))
U_LOG = (("T", 0, 1), ("T", 1, 2))
OUTER = (0, 1, 1)  # reflection about the injected logical port


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def odd(bits):
    n = sum(bits)
    return bits.index(1 if n == 1 else 0) if n in (1, 2) else None


def plates(bits):
    # T acts as i on the antisymmetric pair, so T² acts as -1. Blank
    # layers physically bypass all ports with the same normalization clock.
    layer = tuple(rail.PAIRS[j] for j in PORTS if bits[j])
    return (layer, layer)


def logical_plates(bits):
    return tuple(("i", j, j) for j in PORTS if bits[j] for _ in range(2))


def circuit(bits):
    return U + plates(bits) + rail.inverse(U) + plates(OUTER) + U


def logical_circuit(bits):
    inverse = tuple(op for op in reversed(U_LOG) for _ in range(3))
    return U_LOG + logical_plates(bits) + inverse + logical_plates(OUTER) + U_LOG


def classical() -> None:
    # Finite decision-tree optimum: each leaf chooses the best of all three
    # answers for its *whole* posterior class. A terminal miss cannot help.
    # Stop early, revisit a bit, or choose the next bit after any transcript.
    @cache
    def wins(pool, budget):
        best = max(sum(odd(bits) == j for bits in pool) for j in PORTS)
        if budget:
            for j in PORTS:
                subsets = (tuple(b for b in pool if b[j] == r) for r in (0, 1))
                best = max(best, sum(wins(subset, budget-1) for subset in subsets))
        return best

    promised = tuple(b for b in BITS if odd(b) is not None)
    need(tuple(wins(BITS, k) for k in range(4)) == (2, 2, 4, 6), "all-eight decision tree")
    need(tuple(wins(promised, k) for k in range(4)) == (2, 2, 4, 6), "masked single-mark promise")
    # Known uncomplemented orientation leaks useful information; now two
    # queries find the marked port even though the third is never accessed.
    unmasked = tuple(b for b in BITS if sum(b) == 1)
    need(tuple(wins(unmasked, k) for k in range(3)) == (1, 2, 3), "orientation leakage")
    # An explicit nonadaptive strategy meets the 2-contact optimum: equal
    # bits -> use unseen port; different -> fixed one of the observed pair.
    need(sum(odd(b) == (2 if b[0] == b[1] else 0) for b in BITS) == 4, "sharp two contacts")
    need(sum(odd(b) is not None for b in BITS) == 6, "three contacts read whole setting")
    print("Best 0/1/2/3 classical bit-contact scores: 2/8, 2/8, 4/8, 6/8."
          " On the six nonconstant strings: 1/3, 1/3, 2/3, 1.")


def coherent() -> None:
    source, src_den = rail.prepare()
    herald_prob = sum(rail.weights(source, src_den))
    need(herald_prob == F(1, 2), "pre-choice source herald yield")
    p = tuple(z[0].norm2() for z in gauss.run(gauss.eye(3), U_LOG))
    need(p == (F(1, 2), F(1, 4), F(1, 4)), "native unbalanced preparation")
    scores = {}
    decoded = {}
    for bits in BITS:
        word = circuit(bits)
        den = 2**len(word)
        m = gauss.run(gauss.eye(3), logical_circuit(bits))
        need(len(word) == 14 and gauss.unitary(m), "fixed depth and reversibility")
        decoded[bits] = m
        for j in PORTS:
            col = rail.physical(rail.code_basis(j), word)
            for k, (a, b) in enumerate(rail.PAIRS):
                x, y = col[2*a:2*a+2]
                need(col[2*b:2*b+2] == (-x, -y)
                     and gauss.g(F(x, den), F(y, den)) == m[k][j],
                     "integer physical columns must equal logical Gaussian circuit")
        # Check complete invertibility outside as well as inside the code.
        for k in range(2*rail.PORTS):
            basis = tuple(int(h == k) for h in range(2*rail.PORTS))
            restored = rail.physical(rail.physical(basis, word), rail.inverse(word))
            need(restored == tuple(a*den**4 for a in basis), "raw inverse on all 12 components")
        actual = tuple(w/herald_prob for w in rail.weights(
            rail.physical(source, word), src_den*den))
        expected = tuple(m[j][0].norm2() for j in PORTS)
        need(actual == expected and sum(actual) == 1, "complete per-herald grouped outcomes")
        s = odd(bits)
        if s is None:
            need(actual == p, "common sign must not move port probabilities")
            scores[bits] = F(0)
        else:
            closed_form = tuple(p[j]*(3-4*p[s])**2 if j == s else
                                p[j]*(1-4*p[s])**2 for j in PORTS)
            need(actual == closed_form, "independent one-step reflection formula")
            scores[bits] = actual[s]

    for b, m in decoded.items():
        mb = decoded[tuple(1-bit for bit in b)]
        need(all(m[i][j] + mb[i][j] == gauss.ZERO for i, j in product(PORTS, repeat=2)),
             "all complementary masks differ only by a global sign on the code")
    per_mark = tuple(sum(scores[b] for b in BITS if odd(b) == j)/2 for j in PORTS)
    score = sum(scores.values()) / len(BITS)
    need(per_mark == (F(1, 2), F(1), F(1)) and score == F(5, 8)
         and score*herald_prob == F(5, 16), "native unconditional score")
    # Fully recording the arm after setting the signs preserves the three
    # populations p. Ignoring that record removes all setting dependence in
    # the output; this control is not a claim about partial visibility.
    inv_log = tuple(op for op in reversed(U_LOG) for _ in range(3))
    reflection = gauss.run(gauss.eye(3), inv_log + logical_plates(OUTER) + U_LOG)
    recorded = tuple(sum(p[k]*reflection[j][k].norm2() for k in PORTS) for j in PORTS)
    need(recorded == (F(1, 4), F(3, 8), F(3, 8)) and
         sum(recorded[odd(b)] for b in BITS if odd(b) is not None)/8 == F(1, 4),
         "complete ignored which-arm record")
    print("Native six physical rails (three logical arms), 14 equally clocked layers:"
          " success by marked arm (1/2, 1, 1); 5/6 on nonconstant strings;"
          " all-eight score 5/8 per pre-choice herald, vs the two-contact ceiling 1/2.")
    print("Half of source attempts herald: 5/16 ideal score per original source attempt."
          " With uniform setting-independent detection efficiency the per-herald score"
          " is eta*5/8, exceeding 1/2 only for eta>4/5. Misses score zero.")
    print("A complete ignored which-arm record leaves all first-stage intensities alone"
          " but lowers the all-eight score to 1/4.")


def main() -> None:
    classical()
    coherent()
    print("This separates a specified limit on accessible settings. It cannot exclude"
          " classical mechanisms with three contacts, a global setting leak, or"
          " information carried on all three otherwise empty/occupied modes.")


if __name__ == "__main__":
    main()
