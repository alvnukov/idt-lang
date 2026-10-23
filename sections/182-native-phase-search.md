# Native phase search and rational extension leads

The fixed integer campaign retains all 52 supplied laws: 50 plane laws with
`k, eta in [-2,2]` and quadratic or quartic weights, plus two scalar controls.
Four have no counterexample within the native radius-one checks; 48 have a
witness against a selected law, not a rejection of every theory using a carrier.

## Integer campaign scope and results

Plane multiplication is `(a,b)*(c,d)=(ac+k*bd,ad+bc)`, with componentwise
addition. Write `Q(a,b)=a^2+eta*b^2`; the weights are `W=Q` or `W=Q^2`.
Scalar controls use `b=0`. Checks cover empty and unit weights, nonnegativity,
third-order interference `I3`, product weight, and existence of two-path
interference. Radius one supplies 729 plane triples, below the 1000-case cap;
universal checks exhaust their finite boxes unless a counterexample stops them.

The four laws without bounded counterexamples are quadratic plane laws
`(k,eta)=(-2,2),(-1,1),(0,0)` and the quadratic scalar control. Four surviving
carrier specifications do not establish four distinct physical theories.

Phase diagnostics select integer multipliers in the radius-two grid satisfying
`W(u)=1`, use plane seeds `(1,0)` and `(1,1)` or scalar seed `(1,0)`, and
compare ports `x+(1,0)` and `x-(1,0)` through
`p(x)=W(x+(1,0))/(W(x+(1,0))+W(x-(1,0)))`.
They retain five initial readouts and search for exact state repetition through
16 multiplications. This unit-weight filter favors Gaussian roots; it does not
establish physical selection or global weight preservation.

Two candidates hit `[1,1/2,0,1/2,1]`: the Gaussian plane laws `k=-1,eta=1`
with quadratic and quartic weights. Their off-axis seed `(1,1)` already
distinguishes them: initial readouts are `5/6` and `25/26`, respectively.
For three equal inputs `(1,0)`, their `I3` values are `0` and `36`; the quartic
trace hit does not override its native-law counterexample.

Across candidates, 38 have a nonbinary first-five readout, 15 have an invalid
first-five readout, and 21 have at least one orbit open within the cap. These
categories overlap. An absent cycle or an open orbit is not a failure verdict.
The 52 laws supply 464 orbit probes: 250 close exactly and 214 stay open within
the cap. These are synthetic finite calculations, not empirical observations.
In the quadratic Gaussian cycle, states `i=(0,1)` and `-i=(0,-1)` both read
`1/2`; multiplying each by `i` gives readouts `0` and `1`. Current readout alone
therefore does not determine subsequent readouts under this supplied map.

Implementation: [native phase search](../theory_experiments/native_phase_search.py);
fixed inputs: [campaign configuration](../data/native_phase_search_v1.json).
The [retained full report](../data/native_phase_search/campaign-v1.json.gz)
includes all 52 laws, bounded witnesses, and exact orbit evidence.
Reproduce without writes using
`python3 scripts/search_native_phases.py`. Saving a full report requires a new
`--output` path; archival additionally requires explicit `--record-history`.

## Rational extension leads

These separately supplied rational multipliers extend the integer domain; they
are not integer-screen passes. Exact observations and specifications are saved
in [rational extension leads](../data/native_phase_search/rational_extension_leads.json). Both leads have
status `synthetic_finite_rational_extension_hit`, unchanged candidate verdicts,
empirical status `not_tested`, and adapter status `not_registered`.
They are also retained as source-backed historical inputs with an unsupported
prediction adapter; archival retention does not upgrade their status.

### Weighted two rational lead

Candidate `rational_phase_weighted_two_v1` has carrier `Q^2`, componentwise
addition, zero `(0,0)`, unit `(1,0)`, product
`(a,b)*(c,d)=(ac-2bd,ad+bc)`, and weight `W(a,b)=a^2+2b^2`.
Start at `x0=(1,0)` and iterate `x[t+1]=x[t]*(1/3,2/3)`; reference is `(1,0)`
and `p(x)=W(x+(1,0))/(W(x+(1,0))+W(x-(1,0)))`.
Times `0..7` give `[1,2/3,1/9,2/27,49/81,242/243,529/729,338/2187]`.
The next state is `x8=(-5983/6561,-1904/6561)`. All visited weights through
`x8` are one; no state repeats through eight multiplications.

### Gaussian rational lead

Candidate `rational_phase_gaussian_v1` has carrier `Q^2`, componentwise
addition, zero `(0,0)`, unit `(1,0)`, product
`(a,b)*(c,d)=(ac-bd,ad+bc)`, and weight `W(a,b)=a^2+b^2`.
Start at `x0=(1,0)` and iterate `x[t+1]=x[t]*(3/5,4/5)`; reference is `(1,0)`
and `p(x)=W(x+(1,0))/(W(x+(1,0))+W(x-(1,0)))`.
Times `0..7` give `[1,4/5,9/25,4/125,49/625,1444/3125,13689/15625,77284/78125]`.
The next state is `x8=(164833/390625,354144/390625)`. All visited weights through
`x8` are one; no state repeats through eight multiplications.

### Exact reproduction and interpretation

Run this Python fragment for both leads; it prints each state, its weight,
both port weights, and the readout through time eight.

```python
from fractions import Fraction as F
for k, eta, u in [(-2, 2, (F(1, 3), F(2, 3))),
                  (-1, 1, (F(3, 5), F(4, 5)))]:
    x = (F(1), F(0))
    for t in range(9):
        a, b = x
        w = a*a + eta*b*b
        plus, minus = (a+1)**2 + eta*b*b, (a-1)**2 + eta*b*b
        print(k, t, x, w, plus, minus, plus/(plus+minus))
        c, d = u
        x = (a*c + k*b*d, a*d + b*c)
```

These finite traces supply no finite-orbit certificate or universal proof.
Over the reals, `z=a+i*sqrt(2)*b` identifies the weighted-two product with
ordinary complex multiplication; over the rationals the two quadratic fields
differ. Neither is a new real algebra on this evidence. Physical preparation,
the readout map, composites, full QM, SM, and gravity remain missing bridges.
No scientific status is upgraded.
