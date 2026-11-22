# Can the marked carrier generate its six signed levels without a charge dictionary?

**Yes as a measured mode shape, no as a conserved scalar of its native
hops.** These are different statements. The earlier additive model supplied
occupation weights, antipodal sign and an ordered reference. Here the signal
rule receives only adjacency, a reference vertex `r` and a point `t` at the
end of a non-backtracking two-step route. The readout simply happens to match
the same six-level field after an overall calibration. Both mechanisms use
the same graph and marks, so the match is not independent evidence for the
Standard Model.

## A smaller readout: ten binary comparisons

A port *germ* means just a locally distinguished edge at the current vertex.
When moving along that edge, carry the return edge as the new germ. When
moving along another edge, carry the opposite side of the unique square.
Give this transported reference a reusable bit. If the only inputs to a
reversible bit update are “same direction” or “different direction”, there
are four update tables. On the folded graph exactly one nonconstant table
gives path-independent endpoint readings: **flip on different, do nothing
on same**. A flip on same changes the result on a five-edge closed walk.
The ordinary unfolded cube is a control: there all four tables are flat.

Run the same experiment from each of the five root directions to the mark
and the queried vertex. Take an unordered pair of directions. Abstain if
either destination gives identical bits for that pair. Otherwise add one
when the two destinations order the pair alike and subtract one when their
orders disagree. The ten signed votes total
`n00*n11 - n01*n10`, where the four cells jointly count the two destination
bits. No weight −2 or +3, no continuous amplitude and no random drawing
law enter this tally. The actual integers agree with the prior field on
**all 2,560 frame–vertex combinations**. Dropping any one direction already
changes the result at the second mark.

This is a readout protocol, not an integer carried by a particle. It requires
a root, marked endpoints, reliably transportable port references, repeated
comparisons and the ability to add signed votes. An unresolved single click
records none of that table. The comparison rule is supplied; the six outputs
and the flat update within the stated class are not.

Why use the signed difference at all? If a tally may use at most quadratic
polynomials of the four cell counts and must be zero on **every** independent
factorized count table, the determinant is the only nonzero choice, up to an
overall multiplier. Substitution `(a,b,c,d)=(ru,rv,su,sv)` leaves only
`ad` and `bc` with the same exponents. No nonzero linear statistic has this
property. The tally is also `5|T ∩ W| − |T||W|` for the two sets of
directions whose recorder flipped. Thus disjoint-union additivity and
complement sign reversal now follow, and `|T|=2` gives elementary +3 and
−2. Independence nulling, low comparison order and signed orientation are
**instrument requirements**, not experimental discoveries. Higher-order and
normalized associations need not give these integer levels.

There is a binary energy interpretation as well. Put one sign on each
vertex and penalize equal neighbors. Of all 65,536 assignments, ten minimize
the cost at eight frustrated edges; they are two global signs for each of
five directions. In a symmetry-invariant ensemble of these minima, the
covariance of the two relative signs `s_r s_t` and `s_r s_v` is `4q_v/25`.
One fixed minimum alone has zero covariance. At any positive thermal
weight the full shape is not exactly proportional to the ground result.
Strict single-site descent has 80 additional traps; with uniform starting
bits and uniform improving choices it reaches a minimum only about 79.2%
of the time. An added neutral adjacent-pair update removes permanent traps
under a symmetric random scheduler; convergence is almost sure, not a
guaranteed finite preparation time.

## Path counts and local readings

Clamp/absorb `r`, inject a unit at `t`, and at each tick count one wait and
one move along each available port. A hop changes the parity bit, a wait does
not. Absorbed attempts stay in the denominator. With `A` the adjacency
matrix of the 15 live sites, the **difference** of even- and odd-hop counts
evolves by `I−A`. No signs or charges are assigned to individual sites.
The largest-magnitude mode of this update has eigenvalue 4. Its space has
dimension four: the graph alone selects a *space*, not one charge vector.
The source position selects its projection `P e_t`.

Over all 160 ordered two-step frames, `20 P e_t` equals the prior field
point by point. In primitive integer units its values (multiplicities) are
−4 (3), −3 (2), 0 (1), 1 (6), 2 (3), 6 (1). The six numbers are obtained
only after the overall sign and scale are chosen; the adjacency calculation
does not need these labels to run. Distributing the source uniformly over
either root shell gives **zero** projection. An adjacent source yields
a different pattern; leaving the root unpinned introduces a tied mode.

The iterated counts are not event probabilities. For a uniformly sampled
wait/port choice the normalization is six per tick: at 64 ticks the example's
signed all-attempt signal at the source is about (1.61) parts in a trillion,
not an amplified detector signal. A short graph-specific analysis filter
`40P=−A³+4A²+5A−8I` recovers the mode exactly; a uniform 258-ticket
comparison realizes its *expected* signed contrast `q/129` in at most
three hops. The filter is computed from this graph's spectrum, not posited
as a universal physical law. Polynomial filters on adjacency are standard;
see [Sandryhaila and Moura](https://arxiv.org/abs/1210.4752).

A single detector collecting all first arrivals at the root misses the
contrast. With separately addressable incoming ports, parity records, a
clock and a specified two-/three-/four-hop binary protocol, two ports
instead give 313/624 and the other three 467/936; their average is 1/2.
These positive numbers are obtainable from nonnegative counts but the
selection/weighting of the protocol is extra apparatus. They are not charge
assignments for individual clicks.

## A passive, classical realization of the same relative signs

Put an equal positive mass at each vertex, an equal positive spring on each
edge, clamp the root and drive the marked point. In units of spring constant
over mass, the stiffness matrix is `5I−A`. Its highest squared resonance
frequency is 8. The signed phase-sensitive displacement residue of the
driven resonance is precisely `P e_t`: no complex quantum amplitude or local
charge weights enter. At the exact undamped pole there is no bounded
steady-state response. Finite two-sided detuning of 1/64 in squared-frequency
units still resolves the six calibrated levels by relative displacement in
the ideal array.

This analogy has sharp controls. A static positive force gives *positive*
free-site displacements; a free impulse excites all four frequencies, not
just the top one. Uniformly rescaling mass or spring constant shifts the
dimensional resonance, whereas changing just one spring can split it and
change the field. The supplied linear springs, calibration, pin, drive,
frequency sweep and phase-sensitive measurement are part of this route.

Weak equal viscous absorbers in the selected pure mechanical mode dissipate
mean energy in proportions `q_v²/120`. These are **energy fractions**, not
whole-event frequencies. Two partitioned detector banks can have the same
11/20 and 9/20 mean fractions whether the energy is divided every time or a
whole unit is allocated to just one bank. Coincidences distinguish them.

With one common random intensity, fixed splitting and conditionally independent
monotone detectors, the heralded coincidence ratio is at least one if both
marginals are nonzero. [Grangier, Roger and Aspect](https://doi.org/10.1209/0295-5075/1/4/004)
reported 0.18 ± 0.06, nine coincidences versus a corresponding classical
expectation of at least 50. Visibility above 98% was measured in a
**separate** gated interferometer configuration. [Chou et al.](https://doi.org/10.1103/PhysRevLett.92.213601)
reported 0.24 ± 0.05 at zero delay in an independent heralded source with
their own coincidence normalization. Neither paper tested the marked graph.
Correlated detector readiness, a second optical input or discarding nonclicks
can evade the simple common-intensity bound. The sign-sensitive mode and its
energy distribution still do not select a single event.

## Why the numbers are not yet a particle charge

For a candidate site observable `Q=diag(q)`, `[A,Q]_{uv}=A_{uv}(q_v−q_u)`.
On a connected graph only a constant diagonal readout commutes with its
full adjacency. Restoring the reference vertex for a separate transport
test, 34 of the 40 undirected edges change the signed value. The six
neutral edges form one six-cycle. The rank-one mode operator `q qᵀ` does
commute but has only two eigenvalues; it is **not** the six-valued site
observable.

Selecting only two-hop routes with equal endpoint readings produces a
triangular prism, two triangles, a pair and two isolated sites in the six
sectors. Equality was a **selection criterion**: this is neither a mechanism
for conservation nor a continuous gauge action. Even a supplied linear
virtual-hop model with intermediate energies `q` distinguishes the two
intermediate routes and whether the root is traversable. A compensating
six-level store can keep a fixed total along every hop, but on that sector
it merely records the endpoint potential; an independently initialized
finite store cannot permit every directed transfer at every level.

These are finite, executable tests of what particular readouts mean. They
do not establish a conserved physical hypercharge, electric charge, a gauge
boson, a single photon click, quantization of the mechanical array, or
universal quantum mechanics. The replay and immutable research controls are
under the `carrier_mode_conservation` bundle.
