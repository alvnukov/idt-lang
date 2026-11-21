# Shutter tests: what the detector and the blocked arm actually do

Replay: `python3 -m unittest tests.test_shutter_candidate_probes`.
These are conditional finite model comparisons. None fits data or changes
the scientific status of a primitive. The two probes use different levels
of description: actual gates and dumps in the first; a supplied addition
law for separately switchable contributions in the second.

### One occupied arm versus a wave

The [two-arm probe](probe_two_arm_shutters.py) runs all four shutter
settings from the same preparation in the [native record apparatus](REFERENCE_CHAIN_PROBES.md).
A closed arm swaps into **its own** initially empty dump, which never enters
the recombiner. The detector and the prepared reference do not change with
the shutters. Use yields per emission, not per survival. Write
`I2 = both − left-only − right-only + neither`, including the actual
closed-apparatus response.

| Open | Raw native detector (UV, VU) | Transmission | Transmitted and detected (UV, VU) |
| --- | --- | ---: | --- |
| Both | (1, 0) | 1 | (1, 0) |
| Left | (1, 1/2) | 1/2 | (1/2, 0) |
| Right | (1/2, 0) | 1/2 | (1/2, 0) |
| Neither | (1/2, 1/2) | 0 | (0, 0) |

These are rates for fair trial labels at **each** of 96 gate/background
settings. The zero I2 is stronger: it holds for each of the 192 labelled
trials. On a trial with occupied arm p and empty background v, a fixed
suffix F sees either the original state z or v. Its raw response is
`F(v) + [p open](F(z) − F(v))`. The vacuum response in this model
depends on the retained reference; it is not independent detector noise.
With neither arm open the survival-conditioned response is undefined.

With a **shared** dump the first closure can feed the second arm.
Closing left first gives an apparent raw I2 of (0, 1/2); reversing the
order gives (−1/2, 0). This is a leak, not an interference discovery.
Conversely the exact wave control, using the same separate-dump construction,
gives a real distinction under its supplied assumptions: bright/dark fringe
redistribution, with fixed-port I2 of −1/2 and +1/2. It supplies coherent
addition, the balanced complex mixer with coefficients (1±i)/2, and a
squared-norm readout; the calculation does not derive those assumptions.

### A held-out preparation for two smaller candidate laws

The [cyclic probe](probe_cyclic_shutter_holdout.py) compares addition on a
triangular integer lattice, read by Q(x,y)=x²−xy+y², with addition of two
bits modulo two, read by “nonzero residue.” For three separately switchable
arms a=(1,0), b=(0,1), c=(−1,−1), both laws agree on **all eight masks**:
the three singletons and three pairs have unit response; the full triple
and the empty mask both have zero response.
Neither pair interference nor the vanishing third-order difference separates
the two here.

Keep the readout, gain, and first two arms fixed; replace c by a separately
switchable copy of a. With a common gain of 1/4 the third-order difference
is now **0 versus 1/2**. That gain is admissible on these two bounded
experiments; it is not an unlimited click probability law. Physical
availability of coherent copies at the same gain is an open premise.

There is a general reason to vary the copy count. For a common scalar
readout W on an abelian carrier, I2 is its second finite difference at zero,
and I3(a,b,t) is the change in that difference from zero to t. When a has
additive order n, summing over t=ka telescopes to
`Σ I3(a,b,ka) = −n I2(a,b)`. This concerns the **whole additive cycle**,
not a short sequence of phase settings and not the order of a phase group.
A finite torus modulo 17 with a minimum-norm readout agrees with the
infinite lattice on all 127 sums obtainable with at most six signed unit
steps. It fails later. Keep it in the history rather than rejecting all
finite carriers from the two-bit candidate's failure.
