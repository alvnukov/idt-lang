# What kind of space can the walk describe?

These are tests of candidate kinematics, not a derivation of spacetime.
Replay with `python3 -m unittest tests.test_transport_candidates`.

| Probe | What survives | Counterexample or missing input |
| --- | --- | --- |
| [Integer transport](probe_integer_transport_walk.py) | A local signed two-channel update followed by opposite shifts produces the three-step position counts (1,5,1,1)/8. | A dephased persistent walk agrees for two steps but gives (1,3,3,1)/8 on the third. A mean group velocity is not the causal front. |
| [Two-state cone](probe_shared_cone_origin.py) | A traceless, linear Hermitian crossing has a positive semidefinite momentum Gram matrix of rank at most three, or at most two with only real symmetric matrices. | This does not pick spatial dimension. Two species on the same lattice, even with coherent flavor mixing, can have distinct axial speeds inside the same travel bound. |
| [Weyl chirality](probe_weyl_walk_chirality.py) | Three supplied noncommuting spin shifts yield conical crossings with definite chirality. | A 2×2×2 grid misses every opposite-chirality cone in this example. Properly identifying the four connected lattice components leaves one of each sign per quasienergy on each component, not an isolated Standard Model chiral species. |
| [Clock rescaling](probe_universal_clock_rescaling.py) | In one band a coin defect can imitate a clock and ruler change in the gap and curvature. | A fourth-order diagnostic differs by an exact factor 43/39; a second species already asks for another ruler (2/9 vs 3/16 for its squared rescaling). In the strict relativistic continuum the ambiguity returns. |
| [Phase comparison on links](probe_phase_comparison_links.py) | An oriented quarter-turn on an integer plane gives four orientation-preserving integer isometries. Path comparison can read a loop phase independently of local frame names. | Local renaming alone creates no flux. Exhausting 65,536 link assignments on a 2×2 torus gives 1,024 classes and 16 flat sectors: a flat twist can survive a noncontractible loop. The connection itself is supplied. |

For transport, two exact count recurrences agree through 40 steps. Explicit
event trajectories are compared only through step three in that probe.
For the symmetric coin the matching choice can already change two of 16
individual histories at step four without changing the rail counts.
Discrete-time quantum walks as relativistic kinematic models are established
comparators, not new empirical predictions of this project; see [Strauch](https://doi.org/10.1103/PhysRevA.73.054302)
and [D’Ariano and Perinotti](https://arxiv.org/abs/1306.1934).

For the cone, the trace Gram matrix is Gᵢⱼ=Tr(AᵢAⱼ)/2 for the supplied
traceless two-by-two coefficients. Its rank bound does not require mutually
orthogonal axes. An identity part allows a tilted cone; a fourth external
momentum coordinate can be invisible. A full Pauli triplet has no nonzero
anticommuting mass matrix in two components; doubling with the opposite
action permits one in four. That does not select a mass or a fermion species.

For the clock, matching a band dispersion is not comparing rates of clocks
made of the same primitives. In the strict continuum, changing all masses
by N is indistinguishable in the dispersion alone from changing clock and
ruler by (N,1/N). The existing [weak-field clock](../sections/127-executable-weak-field-clock-calculator.md)
supplies calibrated gravitational inputs; these walks have not derived them.

For the link test, a four-port interferometer reads the four loop phases
using two fixed reference orientations. Preparation costs half the injected
trials, and an orthogonal which-arm marker removes the fringe. Conjugating
the whole apparatus changes no rates. A kinematic comparison or a finite
group of labels supplies neither Maxwell dynamics nor a coupling constant.

The [shared-link harmonic test](probe_link_phase_harmonics.py) distinguishes
reusing one phase twice from drawing two phases independently. Four positive
quarter-turn labels require m₂≥2|m₁|−1 for the signed cosine contrasts.
The supplied relative rotation (3+4i)/5 and its conjugate instead give
(m₁,m₂)=(3/5,−7/25) for reuse. This is incompatible with the four-label
model if both contrasts have absolute error strictly below 4/25. Exact
equality m₂=2m₁²−1 fixes the cosine on every supported phase: no root of
unity has 2cos(φ)=6/5. This does **not** exclude a finite hidden set:
two non-root-of-unity phase labels already reproduce the example.
Finite cycles can approximate the pair to arbitrary positive accuracy.
The values are a model comparison, not measurements of an electromagnetic field.
