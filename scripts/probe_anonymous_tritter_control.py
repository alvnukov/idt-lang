"""Calibrated anonymous collisions versus an ideal Fourier tritter.

A deterministic single-step rule on three NONNEGATIVE OCCUPANCIES, with
no further state, commuting with all port permutations, fixes 111 at
total three. This remains true for arbitrary mixtures of such rules, and
for an equivariant evolution with a fully permutation-fixed blank apparatus
as long as the entire input/environment retains the symmetry.

An *ensemble* of oriented reversible devices is different. In the two-unit
sector six fixed permutations with weights 1/9 or 2/9 give all 36 ideal
bosonic probabilities in this ONE optical setting. In the three-unit
sector an oriented hidden port and a switch reproduce the single 111 row
while failing other preparations. Uniform initial seeds, refreshed trials
and optical preparation are not consequences of local reversibility.

We compute the ideal Fourier prediction exactly by summing permutation
phases in Z[omega], omega²=-1-omega. Bosonic Fock lift and detection rule
are given benchmark inputs. The distinguishable-particle control is a
separate multinomial, not an arbitrary classical-wave or hidden-device bound.
Spagnolo et al. actually measured reconstructed coincidences with a herald,
finite indistinguishability, an independently characterized transfer matrix
and delay scans: doi:10.1038/ncomms2616, especially Figs. 2 and 5. Their
article's ideal histogram is not raw all-herald event data. We do not fit
or test the local candidate against the laboratory apparatus.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
from math import factorial, prod


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def patterns(n):
    return tuple((i, j, n-i-j) for i in range(n+1) for j in range(n+1-i))


def list_ports(occupancy):
    return tuple(i for i, n in enumerate(occupancy) for _ in range(n))


def ideal(source, target):
    i, o = list_ports(source), list_ports(target)
    need(len(i) == len(o), "different number sectors")
    # Repeated port entries are intentional; Fock factorials divide their
    # multiplicities outside the squared permanent.
    phases = Counter(sum(a*b for a, b in zip(i, order, strict=True)) % 3
                     for order in permutations(o))
    real0, phase1 = phases[0]-phases[2], phases[1]-phases[2]
    norm = real0*real0-real0*phase1+phase1*phase1
    return F(norm, 3**len(i)*prod(factorial(x) for x in (*source, *target)))


def distinguishable(out):
    n = sum(out)
    return F(factorial(n), 3**n*prod(factorial(x) for x in out))


def wires():
    pairs = tuple(tuple(0 if j == k else 1 for j in range(3)) for k in range(3))
    doubles = tuple(tuple(2 if j == k else 0 for j in range(3)) for k in range(3))
    states = doubles+pairs
    # A common permutation of the three physical ports, even if randomly
    # redrawn, only permutes the input occupancies: it cannot turn two
    # individually occupied ports into one double. Conversely, independent
    # uniform choices per particle bunch with probability 1/3, not 2/3.
    physical = [tuple(tuple(s[j] for j in p) for s in states)
                for p in permutations(range(3))]
    need(all(max(table[i]) == max(states[i]) for table in physical for i in range(6))
         and sum(distinguishable(s) for s in doubles) == F(1, 3)
         and sum(ideal(pairs[0], s) for s in doubles) == F(2, 3),
         "common physical wires and uncorrelated outputs are distinct models")
    outputs = {s: Counter() for s in states}
    for dx, flip in product(range(3), (0, 1)):
        perm = tuple(3*(a//3 ^ flip)+(a%3+dx) % 3 for a in range(6))
        need(sorted(perm) == list(range(6)), "oriented rule is not reversible")
        for a, b in enumerate(perm):
            outputs[states[a]][states[b]] += F(1+flip, 9)
    need(all(outputs[a][b] == ideal(a, b) for a, b in product(states, repeat=2)),
         "six oriented permutation tables do not reproduce single setting")
    need(all(len(row) == 6 for row in outputs.values()), "six hidden choices needed in this class")
    # The only fully equivariant bijections in the two-unit sector are identity
    # and the common point↔complement swap. Test all 6! maps, not just our two.
    perms = []
    for p in permutations(range(3)):
        perms.append(tuple(states.index(tuple(s[j] for j in p)) for s in states))
    sym = [p for p in permutations(range(6))
           if all(p[h[i]] == h[p[i]] for h in perms for i in range(6))]
    need(len(sym) == 2 and all(len({p[i] for p in sym}) == 2 for i in range(6)),
         "equivariant mixture has wrong support")
    return len(sym)


def triple():
    n = 3
    states = patterns(n)
    balanced = (1, 1, 1)
    bunch = [s for s in states if max(s) == 3]
    partial = [s for s in states if max(s) == 2]
    need([s for s in states if all(tuple(s[i] for i in p) == s
          for p in permutations(range(3)))] == [balanced], "fixed pattern not unique")
    p = {s: ideal(balanced, s) for s in states}
    need(all(sum(ideal(a, b) for b in states) == 1 for a in states)
         and all(sum(ideal(a, b) for a in states) == 1 for b in states),
         "unconditional ideal sector probabilities")
    need(p[balanced] == F(1, 3) and all(p[s] == F(2, 9) for s in bunch)
         and not any(p[s] for s in partial), "ideal three-photon suppression")
    need(distinguishable(balanced) == F(2, 9)
         and all(distinguishable(s) == F(1, 27) for s in bunch)
         and all(distinguishable(s) == F(1, 9) for s in partial), "distinguishable control")
    tv = sum(abs(p[s]-(s == balanced)) for s in states)/2
    need(tv == F(2, 3), "distance from fixed symmetric rule")
    # Each h selects a port (an oriented hidden resource). Transpose 111
    # with the selected triple and leave all other states alone.
    def mix(src, dest):
        return F(src == dest, 3)+F(2, 9)*sum(
            dest == (h if src == balanced else balanced if src == h else src) for h in bunch)
    need(all(mix(balanced, s) == p[s] for s in states), "oriented countercontrol")
    need(all(mix(s, s) == 1 and ideal(s, s) != 1 for s in partial),
         "one prepared row must not predict the full device")
    return tv


if __name__ == "__main__":
    print(f"Two-unit portwise equivariant bijections: {wires()}; six oriented tables match all 36 "
          "Fourier probabilities with a supplied input-independent mixture.")
    print(f"Input 111: total variation {triple()} from the ideal tritter for every mixture of "
          "individually anonymous rules. A pre-existing random port and switch can imitate this row.")
