# Rational phase search and predictive information loss

Five fixed rational models extend the [integer campaign](182-native-phase-search.md).
Their complete selected one-step matrices distinguish information hidden by the
current readout from coordinates invisible to this probe. All five models remain
exploratory supplied laws, with no physical selection or proof-status upgrade.

## Fixed models and search domain

Plane carriers are `Q^2`, with componentwise addition, unit `(1,0)`, product
`(a,b)*(c,d)=(ac+k*bd,ad+bc)`, and weight `W(a,b)=(a^2+eta*b^2)^power`.
The scalar control restricts `b=0`. The models, operations, and readout are
supplied inputs, not primitives derived from IDT.

| Model | k | eta | power | Selected units | Matrix cells |
| --- | ---: | ---: | ---: | ---: | ---: |
| Scalar quadratic | 0 | 0 | 1 | 2 | 4 |
| Dual quadratic | 0 | 0 | 1 | 178 | 31,684 |
| Gaussian quadratic | -1 | 1 | 1 | 12 | 144 |
| Weighted two quadratic | -2 | 2 | 1 | 6 | 36 |
| Gaussian quartic control | -1 | 1 | 2 | 12 | 144 |

Coordinates are the 89 sorted unique fractions `n/d` with `1<=d<=8` and
`-2d<=n<=2d`: 89 scalar tuples or 7,921 tuples per plane. Every multiplier
satisfying `W(u)=1` is retained. Products are exact fractions, never clipped
back to the coordinate grid. Readout compares the two ports through
`p(x)=W(x+(1,0))/(W(x+(1,0))+W(x-(1,0)))`.

## Complete selected continuation matrices

For each model, matrix states and actions are its selected unit list. Each cell
is `p(x*u)`. The 210 states supply 32,012 cells. A response row contains the
next readout for every selected action; a current-readout class is ambiguous
when its states have different response rows.

| Model | Current readout classes | Distinct response rows | Ambiguous classes |
| --- | ---: | ---: | ---: |
| Scalar quadratic | 2 | 2 | 0 |
| Dual quadratic | 2 | 2 | 0 |
| Gaussian quadratic | 7 | 12 | 5 |
| Weighted two quadratic | 4 | 6 | 2 |
| Gaussian quartic control | 7 | 12 | 5 |

The Gaussian same-readout witness already appeared in the integer campaign.
The wider matrix coverage and contrast with the dual model extend that result:
178 dual unit states collapse to two response rows under this probe. Absence of
a witness establishes neither universal sufficiency nor observational
equivalence, and does not reject the dual carrier as a primitive.

Exact witnesses use `y=(a,-b)` and the same action `u=x=(a,b)`:

| Model | x | p(x)=p(y) | p(x*u) | p(y*u) |
| --- | --- | ---: | ---: | ---: |
| Weighted two quadratic | `(-1/3,-2/3)` | 1/3 | 1/9 | 1 |
| Gaussian quadratic | `(-4/5,-3/5)` | 1/10 | 16/25 | 1 |
| Gaussian quartic control | `(-4/5,-3/5)` | 1/82 | 256/337 | 1 |

Thus current readout loses predictive information under these supplied maps.
Ordinary deterministic classical hidden-state systems can do this too; this is
not a quantum-specific witness and establishes neither Bell nonlocality nor contextuality.

## Bounded traces and retained negative control

Each action is iterated from `(1,0)` and, for planes, `(1,1)`, retaining all nine
states at times `0..8`. Closure means exact state repetition, not repeated
readout. All 418 traces retain valid ports and preserve their seed weight at
every visited state; this is not a universal norm-preservation proof.
For seed `(1,0)` alone:

| Model | Closed | Open within eight steps | Nonbinary traces | Distinct readout traces |
| --- | ---: | ---: | ---: | ---: |
| Scalar quadratic | 2 | 0 | 0 | 2 |
| Dual quadratic | 2 | 176 | 0 | 2 |
| Gaussian quadratic | 4 | 8 | 10 | 7 |
| Weighted two quadratic | 2 | 4 | 4 | 4 |
| Gaussian quartic control | 4 | 8 | 10 | 7 |

The scalar and dual readout-trace sets coincide. Gaussian quadratic and weighted
two share only the two binary traces, as do weighted two and Gaussian quartic.
The two Gaussian laws share three traces: the binary pair and the quarter-turn
trace. Rational rotations distinguish their readouts (`1/10` versus `1/82` in
the witness above) where the quarter-turn pattern could not. For three equal
unit inputs, `I3=W(3)-3W(2)+3W(1)-W(0)` is `36` for the quartic control and
`0` for the quadratic models. The quartic pattern hit does not erase this
counterexample to the selected interference law. Open traces are not failures.

## Reproduction and scientific boundary

Implementation: [rational phase search](../theory_experiments/rational_phase_search.py).
The [fixed configuration](../data/rational_phase_search_v1.json) and
[full report](../data/rational_phase_search/campaign-v1.json.gz) retain all five
models, matrices, traces, and controls without ranking or truth scores.
Run `python3 scripts/search_rational_phases.py` without writes. Saving requires
a new `--output` path ending in `.json` or `.json.gz`; `--record-history`
additionally requires `--output`. Historical source proposals use an unsupported
prediction adapter, not a registered native rational prediction family.

Grid counts depend on coordinates and denominator bounds, not physical merit.
Over the reals, rescaling `b` by `sqrt(2)` identifies weighted two with the
complex algebra; rational trace differences do not establish distinct physical
theories. The `(1,1)` seeds also have unequal weights across families.
Physical preparation, the readout map, composites, and QM, SM, and gravity
closure remain outside this finite calculation. No formal proof is claimed.
