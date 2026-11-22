# What six unordered packets explain, and what they do not

**Candidate:** the six unordered pairs of four distinct legs of a junction.
At fixed total packet count there are five possible difference directions.
The operation “take the other two legs” splits them without naming any
color or weak label. This is a reproducible lead, not the Standard Model.

| Addition to the model | Test result |
| --- | --- |
| Nothing beyond counting packet types | There are three directions odd under complement and two centered even directions. The latter are **exactly invisible** to all four individual leg counts. They are correlations, not two additional leg populations. |
| Keep only the integer populations | The two sector lattices together have index four in the total difference lattice. The primitive traceless scalar weights, −2 and +3, do not carry every original integer difference to an integer difference: their **double** does. This is not a derivation of the physical charge unit. |
| Supply coherent, addressable amplitudes on the six **packet types** and synchronized paired mixers | The connected controls on the three and two centered modes are respectively SU(3) and SU(2), using the native density argument and an exact finite word that separates their actions. Independent finite determinant phases remain. A single unmatched substep can leak half the squared norm to the other sector. These are internal controls, not space-dependent gauge fields. |
| Require a phase that is scalar on both sectors and leaves the uniform packet mode unchanged | In exactly returning lossless six-slot words the pure weight circle `(z^-2,z^3)` contains **only the identity**. In their closure there are 24 points on that circle. Treating global phase as invisible on five single-particle modes changes the count; it is not generally innocuous across exterior grades or against a reference. |
| Interpret pairs as two ordinary particles on the original **four** ports | Distinct fermion pairs give two three-dimensional sectors without a uniform line for the native finite group. For bosons the six distinct pairs are not closed: opposite-even and opposite-odd preparations with identical one-body statistics have coincidence probabilities **1 and 0**. Keeping doubled-port amplitudes coherently gives a different six-dimensional rescue, not the original six packet states. |

The [integer and control calculations](probe_six_packet_sectors.py),
[finite phase and reference tests](probe_packet_hypercharge_reference.py) and
[two-particle propagation test](probe_packet_exchange_transport.py) keep
these different data contracts separate. Adding a fourth opposite pair
permits an exact new point, z=−1, by compensating the hidden phase, and
greater freedom in closure; this extra reference does not select hypercharge.

### A null model with exactly the same numbers

In the two-boson rescue, exclude the uniform single-particle mode and take
the symmetric square of the remaining three. A symmetric 3-by-3 tensor
has one trace, two diagonal traceless entries and three off-diagonal
entries. The finite cubic rotations preserve these last two spaces.
Any traceless block-scalar label on them is proportional to **−2,+3**, just
as in the packet calculation. An ordinary spatial rotation not in the cube
group mixes the blocks: one checked rational rotation produces coefficients
−7/25 and 24/25. This example needs **no charge or local gauge dynamics**.
Neither the multiplicities nor the charge ratio alone distinguish the
gauge interpretation from a cubic quadrupole.

### Does chirality select the family, or was the family put in?

The [matter probe](probe_six_packet_matter.py) tests several inequivalent
ways of obtaining 16 labels. An unsigned six-bit complement quotient has
the wrong permutation characters. A signed Hodge half improves the finite
character but is not invariant under a tested complex determinant-one gate.
Grades zero and two on the six raw modes give the same finite character
and a stable 16, but the wrong charges. By contrast, supplying ordinary
fermionic exterior powers, an unoccupied uniform mode and even parity
gives a candidate one-family representation with an optional neutral
comparison label. Neither exclusion nor fermionic signs follow from a
list of 16 labels.

The [inverse anomaly filter](probe_packet_chiral_selection.py) **does
not assume even parity**. Starting from all twelve exterior blocks, it
tests all 4,096 subsets against the usual four-dimensional left-Weyl
local anomaly coefficients and the ordinary doublet parity test.
128 selections are vectorlike or neutral; four have one chiral orientation,
four the conjugate. Each nonzero selection contains exactly the same 15
charged components up to conjugation. Its four variants just choose none,
either, or both of two neutral labels. For arbitrary multiplicities a
rank-four integer minor fixes only a common **net family multiple**.
No generation number, absolute chirality, sterile particle, or mass follows.

This uses exterior statistics, a local gauge interpretation, the charge
dictionary and the chiral consistency conditions as *inputs*. It helps
test a representation without treating its parity selection as independent
evidence. With an affine vacuum offset, the whole 16 admits a two-parameter
anomaly-free charge plane. Removing that vacuum from this candidate 16
forces its charge to vanish if mixed gravitational consistency is retained.
The physical problem of charge quantization under the assumptions of a
minimal chiral theory is discussed in this [original study](https://doi.org/10.1103/PhysRevD.41.2619);
the finite inverse search here is not an independent experimental test.
The six-element common central kernel of these local representations also
does not determine the physical global gauge group; different allowed
line operators can distinguish theories with the same local fields
([Tong](https://arxiv.org/abs/1705.01853)).

Replay: `python3 -B scripts/replay_primitive_probe_campaign.py --bundle packet_sectors`.
