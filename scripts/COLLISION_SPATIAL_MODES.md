# What propagates if the four-leg collision is wired into space?

There are two distinct hits. An untwisted collision gives a longitudinal
wave. Some cyclic wirings give isolated, handed two-component waves at
nonzero momentum. Neither outcome follows from the bare collision alone.
Both supply a periodic diamond network, a global two-tick clock, linear
amplitudes (or a common background/resolution for finite signed-deviation
replays), and an interpretation of the lattice translations as space.

| Wiring and observation | Result | What the result does not give |
| --- | --- | --- |
| [Fixed four-leg reflection](probe_diamond_collision_walk.py) at both ends of a diamond link | At zero momentum the generator couples a scalar to the longitudinal component. Two transverse directions are flat. Uniform preparation/detection can miss finite circulations that leg-resolved detectors see. | The two transverse directions are not two *propagating* photon polarizations. Invisibility to one detector is not a gauge law. |
| [Reflection followed by a cyclic port permutation](probe_routed_diamond_cones.py) at each end | Among 36 oriented wirings and eight real-sign momentum corners, 48 **wiring/corner pairs** meet the double-carrier test. Each has two opposite eigenphase cones, a full-rank three-dimensional linear generator, and no first-order tilt. | 48 is neither a species count nor a census over continuous momentum. Different wirings need not have the same light cone. |
| [Perturb one ruled junction](probe_collision_cone_stability.py) | A representative crossing has nonzero determinant and local topological charge. Its momentum and phase move rather than opening a gap for sufficiently small periodic unitary changes. | A full-rank local argument is not a numerical radius, a disorder theorem, a relativistic continuum theory, or protection at arbitrary perturbation. |

In the routed example the real two-tick matrix F at the selected point
satisfies F²−F+I=0. Thus the **calculated** operator (2F−I)/√3 squares to
−I on the four real coordinates; its two conjugate complex sectors carry
the two linear modes. No complex instruction at the junction was needed
for this spectral calculation. This is not yet composition of independently
prepared quantum systems, a measurement probability, or a particle.
The squared-speed ratios in the supplied tetrahedral coordinates are 2:1:1,
up to permuting the distinguished axis. One may rescale coordinates for
one cone; that does not prove that independent carriers share one metric.

At zero momentum an identity-returning sequence of these wirings has a
common basis in which all its first derivatives have zero diagonal. That
rules out a four-real-dimensional Clifford triple of full rank **there**,
not the observed finite-momentum modes. For the representative away from
zero, conjugate eigenphase cones have opposite handedness. The corresponding
individual band charges agree after exchanging upper/lower branch and
reversing momentum. These are different sign conventions/observables.

Replay with `python3 -B scripts/replay_primitive_probe_campaign.py --bundle
collision_space`. The optional `--numeric` switch on the stability probe
computes all four band fluxes on sampled spheres with NumPy; it is not
part of the default exact check. As a literature comparator,
[D'Ariano and Perinotti](https://arxiv.org/abs/1306.1934) reconstruct a
different quantum cellular automaton under their own locality and symmetry
hypotheses. Their result is not evidence for these packets.

### First-order isotropy without continuously tuning a junction

The [periodic schedule search](probe_periodic_collision_metric.py) keeps
the same four-leg junction, but repeats three pairs of ticks. In each pair,
both sublattices use the **same** cyclic rewiring. In one fixed schedule
the two conjugate eigenphase cones at a real momentum corner have zero
tilt and squared-speed matrix **4 times the identity** per six ticks.
At that corner the real return map squares to −I. The two carriers now
share a spherical first-order cone in the supplied lattice coordinates.
No adjustable coefficient or fit to measured speeds was used. The extra
schedule and its clock are real costs of this candidate.

For ordered words over 36 possible two-tick wirings, the real corners,
up to tetrahedral symmetry and an overall sign, have three representatives
(multiplicities 1,4,3). No word of length one or two has an isotropic,
full-rank **nonreal double carrier** in this search. Of 46,656 words of
length three, twelve pass at a representative with one minus sign, and
none at the other two representatives. Permutations or clock shifts in
these counts need not be distinct physical systems. One example uses
cyclic permutations with row maps 2031, 2310, 1230, in that order.
Default replay checks the example with rational arithmetic; the optional
`--period 1`, `2`, or `3` reruns the exhaustive integer census with NumPy.

The isotropy has a measurable mathematical limit **within the walk**:
at equal-length directions (5,0,0) and (3,4,0) the trace of the six-tick
map already has different second derivatives. It is the linear mode
splitting that is isotropic, not the full dispersion. The scan does not
count all momenta, derive a common cone for independent matter sectors,
select a physical speed unit, or derive spacetime symmetry.
