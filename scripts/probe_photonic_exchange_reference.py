"""What a phase reference adds to a two-slot exchange comparison.

Laboratory comparators (not IDT data, fits, thresholds or detector models):

* Tschernig et al., Nat. Photonics (2021), Eq. 2 and Fig. 3:
  https://doi.org/10.1038/s41566-021-00818-7 ; https://arxiv.org/pdf/2011.08777 .
  For the selected cross-arm coincidence channels, the two amplitudes have
  opposite photon-to-output assignments. With the authors' port signs,
  C14+C23-C13-C24 has ideal expectation cos(phi1+phi2+pi-phi_x)/2.
  Single-count differences from a separate reference beam calibrate the two
  path phases; the additional geometric pi is part of the apparatus model,
  not a measured fermionic sign. The fit has a positive amplitude (otherwise
  its sign could mimic pi) and a free offset. It gives phi_x=-0.04 +/- 0.07
  rad (95% confidence interval); indistinguishability was 86 +/- 5 percent.
  These are selected coincidences,
  not a statement about the unconditional outcome of every emitted pair.
* Wang et al., Phys. Rev. Applied (2022), Eqs. 2,4 and Fig. 2:
  https://doi.org/10.1103/PhysRevApplied.18.064024 ; https://arxiv.org/pdf/2202.00575 .
  Independent photonic comparison: condition on one detection in each L,R
  region. For rotated polarization analyzers their port convention gives
  C13+C24-C14-C23 and ideal normalized contrast sin(2 beta) cos(phi).
  They varied spatial overlap, and used a tomographic performance factor
  F=0.977 in the analysis. The real photonic boson result is 0.04 +/- 0.06
  rad (Monte Carlo standard deviation); 3.12 +/- 0.05 rad is a PROGRAMMED
  optical simulation of the fermionic phase, not a measurement on fermions.
  Different apparatus, estimand conventions and uncertainties: no pooled fit.

Below is a conditional model of a path comparison, NOT a reconstruction of
either apparatus. Supply an idle arm coherently controlled against a cell
arm, matched exit paths, a common phase reference, a prepared direction
character, a balanced recombiner, unread path tags and squared-norm detection.
The raw cell is an unsigned permutation of an ingress side and two bits.
The empty and full addressed pairs each use TWO total bits, with two fixed
spectator slots carrying the remainder. Different preparation runs are never
superposed. Binary capacity does not imply physical Pauli exclusion.

In the odd direction sector a minus on the full addressed pair inverts a
calibrated fringe. Tracing a perfectly distinguishing path tag removes this
contrast without changing occupation counts. A local pi phase on joint
occupancy in the cell arm can imitate the minus exactly in that sector,
including its empty-address reference and path-tag controls. Interference
identifies a relative implementation phase, not its physical origin. No
native coherent controller, detector/species assignment or statistics law
is inferred. Run: python3 -B -m scripts.probe_photonic_exchange_reference .
"""

from collections import defaultdict
from fractions import Fraction as F
from itertools import product

from scripts import gaussian_dyadic_words as w
from scripts.probe_cell_exchange_intervention import scatter
from scripts.probe_reversible_cell_census import census, encode, inferred_rule

EMPTY = (0, 0, 1, 1)
FULL = (1, 1, 0, 0)
PHASES = (w.ONE, w.I, w.g(-1), w.g(0, -1))
# Idle path always has tag (1,0). The other path's real unit vector gives
# a tunable overlap: no tag, partial distinguishing information, full tag.
TAGS = ((F(1), F(0)), (F(3, 5), F(4, 5)), (F(0), F(1)))


def need(test, why):
    if not test:
        raise ArithmeticError(why)


def ports(table, occupation, character, phase, tag, joint_phase=1):
    """Two exit-port probabilities, traced over direction, mark bits and tag."""
    need(occupation in (EMPTY, FULL) and character in (-1, 1)
         and phase.norm2() == 1 and sum(v*v for v in tag) == 1
         and joint_phase in (-1, 1), "invalid interferometer resources")
    outputs = defaultdict(lambda: w.ZERO)
    for u, arm, port in product((0, 1), repeat=3):
        dest, occ = scatter(table, u, occupation) if arm else (u, occupation)
        need(occ == occupation and sum(occ) == 2, "changed occupation record")
        amp = w.g(character**u * (-1)**(arm*port))
        if arm:
            amp = amp * phase * w.g(joint_phase**(occupation[0]*occupation[1]))
        for label, weight in enumerate(tag if arm else (1, 0)):
            outputs[port, dest, occ, label] += amp * w.g(weight)
    # Unnormalized path split, two direction branches, unnormalized two-port
    # recombiner: squared norm 2*2*2. No likelihood or detector postselection.
    p = tuple(sum(z.norm2() for key, z in outputs.items() if key[0] == k)/8
              for k in (0, 1))
    need(sum(p) == 1, "lost a branch")
    return p


def probe():
    rows, _ = census()
    actual = {word: tuple(map(int, word)) for word, flags in rows if flags == "1111"}
    family = {(a, c): encode(inferred_rule(a, c)) for a, c in product((0, 1), repeat=2)}
    need(len(rows) == 764 and len(actual) == 4 and set(actual) == set(family.values()),
         "the four tables no longer match the finite timing census")
    results = {}
    for (a, c), word in family.items():
        table = actual[word]
        for character, occupation, phase, tag in product(
                (1, -1), (EMPTY, FULL), PHASES, TAGS):
            # The apparatus pi offset is deliberately supplied separately.
            # Empty-address and full-address runs share the same reference.
            route_phase = w.g(-1) * phase
            p, q = ports(table, occupation, character, route_phase, tag)
            sign = character if c and occupation == FULL else 1
            need(p-q == route_phase.re * sign * tag[0], "quadrature or tag contrast")
            if character == -1:
                ordinary = actual[family[a, 0]]
                counterfeit = ports(ordinary, occupation, character, route_phase,
                                    tag, joint_phase=(-1)**c)
                need((p, q) == counterfeit, "local joint phase should mimic the sign")
        # At reference setting zero (net -1), report a full/empty signed
        # ratio: the common geometric pi cancels. A quadrature with zero
        # reference contrast cannot be used this way.
        def contrast(occ, table=table):
            p, q = ports(table, occ, -1, w.g(-1), TAGS[0])
            return p-q
        results[word] = contrast(FULL) / contrast(EMPTY)
    return results


if __name__ == "__main__":
    for word, ratio in sorted(probe().items()):
        print(f"{word}: odd-sector full/empty calibrated contrast ratio {int(ratio):+d}")
    print("Matched fully tagged arms: both ports 1/2; occupation readouts unchanged. "
          "In the odd sector an occupancy-dependent pi can exactly imitate the minus. "
          "No physical statistics or cell-to-photon bridge established.")
