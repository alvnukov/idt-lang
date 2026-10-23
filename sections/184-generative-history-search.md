# Generative history search and supplied local arithmetic

Supplied local cancellation and composition rules generate scalar arithmetic
without choosing amplitude coordinates as the starting data. They do not yet
derive those rules from IDT primitives. The fixed campaign retains 27 detector
variants in 11 source collections and 90 additional kernel hypotheses. Its
useful results are conditional coefficient selection, exact counterexamples,
and identification of redundant arithmetic presentations, not physical selection.

## Supplied rules and induced coordinates

A bag `n=(n0,...,n_(m-1))` counts cyclic oriented labels in one supplied context.
Parallel combination adds counts. Serial composition forms all Cartesian pairs
and adds their labels modulo `m`. These are commutative scalar constructions,
not the full algebra of quantum measurement and dynamics operations. Contexts,
accessible operations, and the cyclic composition law remain supplied inputs;
global histories remain compatibility scaffold rather than new primitives.

For `m=2,4,6,8`, impose `e_j+e_(j+m/2) ~ 0`, giving signed coordinates
`d_i=n_i-n_(i+m/2)`. For `m=3`, impose `e0+e1+e2 ~ 0`, giving
`(d0,d1)=(n0-n2,n1-n2)`. The reduced serial implementation yields integer
scalar multiplication for C2, `(a,b)*(c,d)=(ac-bd,ad+bc)` for C4, and
`(ac-bd,ad+bc-bd)` for C3. These formulas are consequences of the chosen
quotient construction, not evidence that IDT has selected physical amplitudes.

The quadratic detector proposals count ordered pairs, including self-pairs:
`W(n)=sum_(i,j) n_i*n_j*K[(i-j) mod m]`. The even-cycle diagonal choice gives
`W=sum_i d_i^2`; C3 uses `K=[1,-1/2,-1/2]`, giving
`W=d0^2-d0*d1+d1^2`. Pairwise form, self-pair inclusion, cancellation, and
kernel symmetry are proposed inputs, not derivations of the detector or Born
probabilities. Raw cardinality, residual L1, squared quadratic, and C8 quartic
readouts remain as alternatives and controls.

## Fixed finite checks

Every nonnegative bag of total count at most two is retained: respectively
6, 10, 15, 28, and 45 bags for C2, C3, C4, C6, and C8. Every ordered pair and
triple is checked. Generator insertions and every bounded left and right
continuation test quotient descent. Intermediate outputs are never clipped;
C3 descent tests reach raw count ten. All tested normal-form operation and
continuation comparisons agree, but this is not an unbounded proof.

The table gives counterexample counts divided by cases performed. Product
weight multiplicativity is a selected diagnostic, not an axiom that arbitrary
admissible state maps must be algebra homomorphisms. `I3` is the usual alternating
sum over three supplied parallel alternatives, including the empty term.

| Detector family | Serial weight counterexamples | I3 counterexamples | Other scoped outcome |
| --- | ---: | ---: | --- |
| C2 diagonal | 0/36 | 0/216 | Signed scalar control |
| C3 triangle | 0/100 | 0/1,000 | Unit reference weights `[4,1,1]` |
| C4 diagonal | 0/225 | 0/3,375 | Quadratic plane control |
| C6 diagonal | 144/784 | 0/21,952 | Product witness below |
| C8 diagonal | 256/2,025 | 0/91,125 | Product witness below |
| C4 raw cardinality | 0/225 | 0/3,375 | All 30 cancellation insertions change weight |
| C4 residual L1 | 16/225 | 624/3,375 | Nonquadratic alternative retained |
| C4 squared quadratic | 0/225 | 1,668/3,375 | Three equal units give I3=36 |
| C6 kernel grid, nine variants | Zero only at `a=-1,1/2` | Zero for all nine | Every coefficient retained |
| C8 kernel grid, nine variants | 256/2,025 for each | Zero for all nine | Irrational coefficients remain untested |
| C8 quartic norm | 0/2,025 | 51,592/91,125 | Three equal units give I3=36 |

The two kernel grids use `a=-2,-3/2,...,2`, with
`K6=[1,a,-a,-1,-a,a]` and `K8=[1,a,0,-a,-1,-a,0,a]`.
The C8 quartic rule is `W=A^2-2*B^2`, where `A=sum_i d_i^2` and
`B=d0*d1-d0*d3+d1*d2+d2*d3`. Some grid kernels already give negative weights
on bounded inputs; the full report preserves those witnesses. Every variant
has zero empty weight. Nonzero two-alternative differences are failures of an
additivity null, not observations of empirical interference. Zero-case checks
are explicitly not applicable, never reported as successful calculations.

Exact witnesses isolate different failures. For C6 diagonal, take
`x=y=e4+e5`; their serial output is `e2+2e3+e4`, with weight 6 rather than
`W(x)*W(y)=4`. For C8 diagonal, `x=y=e6+e7` similarly gives weight 6 rather
than 4. Raw cardinality changes from 0 to 2 when the cancellation `e1+e3` is
inserted into the empty C4 bag. C4 L1 gives `I3(e3,e3,e1)=2`. For either
quartic rule, three copies of `e0` give `81-3*16+3=36`.

## Cancellation selects coefficients within a supplied detector class

The separate selection probe retains all nine C3 kernels `[1,a,a]` and all
81 C4 kernels `[1,a,b,a]` on the same half-integer grid. It requires
`W(n+c)=W(n)` for every bounded reference bag `n` and cancellation generator
`c`, not merely `W(c)=0`.

| Supplied class | Reference insertion checks | Unique invariant coefficients within grid |
| --- | ---: | --- |
| C3 symmetric ordered pair kernel | 90 | `a=-1/2` |
| C4 symmetric ordered pair kernel | 2,430 | `a=0,b=-1` |

For example, C4 `K=[1,-2,-1,-2]` gives zero weight to each isolated opposite
pair but fails 18 of 30 reference insertions. With `n=e3` and `c=e0+e2`,
weight changes from 1 to -7. The stronger condition checks the cancellation
against references, rather than treating a zero-weight bag as automatically
invisible. Coefficient selection here is conditional on the ordered quadratic
pair ansatz, diagonal inclusion, cyclic symmetry, `K0=1`, and imposed
cancellation. Quadratic `I3=0` is expected from that ansatz, not independent
evidence for physics or a derivation of the ansatz itself.

## Arithmetic presentations and remaining leads

The two C6 grid variants without bounded product counterexamples do not supply
two new independent arithmetics. At `a=-1`, their weights agree with
`(sum_j (-1)^j*n_j)^2`. At `a=1/2`, use C6 label coordinates
`[(1,0),(1,1),(0,1),(-1,0),(-1,-1),(0,-1)]`; C3 uses
`[(1,0),(0,1),(-1,-1)]`. Both coordinate presentations use the C3 product
above and weight `a^2-a*b+b^2`. Across these two maps and the signed-scalar
map, all 81 label products and 66 bounded bag weight comparisons agree.
These exact finite checks establish neither
universal physical equivalence nor equal resource bounds: `(1,1)` is one C6
history but requires two C3 histories under these maps.

The next inexpensive lead is C8 `a=+/-sqrt(2)/2`, retained as untested; failure
of the rational grid does not reject C8. Further useful work would seek a local
origin for cancellation and detector rules, then derive accessible contexts,
reference operations, normalized readout, and actualization. Physical
composites, continuum limits, QM, SM, and gravity closure remain open.

## Reproduction and retained evidence

Run `python3 scripts/search_generative_histories.py` for a read-only repeat.
The [fixed configuration](../data/generative_history_search_v1.json),
[implementation](../theory_experiments/generative_history_search.py), and
[full report](../data/generative_history_search/campaign-v1.json.gz) retain every
variant and kernel hypothesis without ranking. Saving requires a new `--output`
path ending in `.json` or `.json.gz`; `--record-history` additionally requires
`--output`. Archival adds 11 source collections, not 27 independent sources.
All source proposals remain `unsupported` because there is no registered
prediction adapter; standalone synthetic results do not change that status.

The authoritative research-direction data are in the
[Lean ledger](../Proofs/MetaLang/V8LowerPrimitiveGenerativeProbeLedger.lean),
including the report digest and archive identifiers. Completed probes are
`exploratory_finite`, the irrational lead is `not_tested`, and physical bridges
are `not_attempted`. No proof card, formal theorem, empirical status, manifest
claim, or QM closure status is upgraded.
