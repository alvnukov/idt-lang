# Can a detector prepare the collision that would distinguish its laws?

The previous moving/parked contact proposed `(k,s) -> (1+s,k-1)`. On
the moving *excess* and parked stock, `(k-1,s)`, this is just exchange.
The alternative doing that exchange only when one excess/stock is zero
agrees on every binary excess/stock pair. Arbitrarily many serial contacts
on that closed sector do not synthesize an excess of two. Directly loading a
mixed high-stock cell would therefore beg the preparation question.

## Simultaneous arrivals change what can be made

Give a junction `m` equivalent ports carrying nonnegative integer loads.
Supply a deterministic, conserving, reversible rule commuting with all
permutations of these ports. It preserves the stabilizer of each state.
Starting with `k` ones and the rest zero, where `0<k<m`, the output
is constant on the originally filled ports and on the empty ports. These
two constants must be different and obey `k a+(m-k)b=k`. Besides the
unchanged input the only possibility is to put `k/(m-k)` units on each
originally empty port, if this is an integer. On an entirely filled
configuration no distinguished outlet exists.

Three ports are the first that can make a moving double from singles:
`110 <-> 002` and relabelings. At total two there are exactly two
fully symmetric reversible laws, this one and identity. Symmetry does not
choose fusion. On a closed simple cubic graph with the fusion law, transport
on reciprocal links and simultaneous updates, each undirected edge has a
six-tick two-unit collision orbit. Other configurations have period one or
two. The double does not propagate freely through the whole graph. Shift
one arrival by one tick and the fusion can disappear. A double is moving
material; it is not two units parked in the older two-port storage cell.

## A separation using only an occupied side edge

Calibrate a ternary fusion junction, a four-port junction allowing
`1110 <-> 0003`, and a cold two-port storage cell. Starting from five
separate units, the ternary junction supplies a pair to the cell and leaves
stock one; a later triple reaches that stock. Full exchange sends out a pair,
while exchange only at the extremes sends out a triple. At the same ternary
analyzer a pair splits into the two unused arms; an isolated triple returns
on its original arm. The latter follows even for other equivariant reversible
total-three completions: the candidate output `111` has a larger stabilizer.
No integer-load meter and no hidden source of triples are needed. The actual
binary outcome on a specified side arm at tick 5 is one versus zero.

Four initial units suffice if the four-port junction is **also** calibrated
on its two-unit sector, `1100 <-> 0011`. A returned singleton can then
participate in preparing the triple. The side-arm outcome is one versus zero
at tick 6. Fewer than four total units cannot distinguish these two storage
laws; their local tables agree at every such total. Four-unit sufficiency
without the additional calibration is not established. The circuit supplies
pulse timing, fixed wiring, prepared singles and a selected local observation;
its forward and inverse are checked. Five disturbed/disabled control settings
give zero on both branches. These are designs for an intervention, not a
measurement selecting the law of our universe.

## A physical comparison where anonymous fusion is not enough

A balanced optical three-port coupler is a different candidate interface.
For its **ideal** bosonic Fourier model and input `111`, the probabilities
are 1/3 for `111`, 2/9 for each of the three single-port triples, and zero
for each partial bunch. An anonymous deterministic device acting only on
occupancies fixes `111`; finite memory in a completely permutation-symmetric
blank state cannot pick a particular exit either. Any mixture of individually
equivariant such maps has total variation distance 2/3 from that ideal row.
Conversely, an ensemble with an already oriented hidden port can imitate
the whole row while failing every partial-bunch preparation. Its distribution
is symmetric, but its individual devices are not.

At total two, a six-table mixture of reversible occupancy permutations
reproduces all 36 ideal probabilities for this single basis and setting.
Six is minimal in the class of mixtures of fixed deterministic maps because
each row has six possible outputs. These are *occupancy* maps, not permutations
of three physical wires: a common random rewiring cannot fuse two singly
occupied inputs. Independent random outputs give bunching 1/3 in place of
the ideal 2/3. None of these one-setting fits implements a phase-controllable
optical device or explains independent randomness.

[Spagnolo et al., published Fig. 5](https://www.nature.com/articles/ncomms2616/figures/5)
compared reconstructed coincidences and delay visibilities for three photons
from a heralded four-photon setup; the paper includes partial distinguishability,
a nonideal reconstructed matrix and higher-emission contributions. In the
[authors' source and supplement](https://arxiv.org/abs/1210.6935), the
reconstructed/ideal similarity at 785 nm is 0.9595 ± 0.0003; a **separate**
two-photon 50:50 comparison across photon pairs reports visibility 0.63 ±
0.03. Neither number is a measured three-photon bunch probability. The
ideal distribution above is not a fit to raw all-herald data, nor a
statistical rejection of our contact device.

Reproduce: `python3 -B scripts/replay_primitive_probe_campaign.py --bundle anonymous_collision_preparations`.
The three source candidates, including their controls, are retained without a
theory-status promotion.
