# A single echo selects the complex raw weight

On a supplied global complex algebra, a multiplicative real raw weight is
selected as `w(z) = Complex.normSq z` by continuity at one and one actual
nondegenerate normalized echo. The witness consists of two nonzero mathematical
inputs. Its physical availability requires an operational construction.

## The sufficient contract

Let `w : Complex -> Real` satisfy global multiplicativity and continuity at the
multiplicative unit. Supply one pair `a,b` with

```text
a != 0, b != 0,
w(a) + w(b) = 1,
w(a conj(a) + b conj(b)) = 1.
```

Then `w(z) = Complex.normSq z` for every complex input. The zero and unit values,
nonnegativity, strict positivity away from zero and conjugation invariance
follow. A supplied balanced witness `c` with `w(c)=1/2` and the echo of `(c,c)`
is a specialization. The theorem also derives raw response conservation for
the existing supplied native coordinate mixer.
[Single-echo classification and conservation](../Proofs/QMClosure/SingleEchoReadout.lean)

The weight is defined globally and can exceed one. Its value at the scalar two
is four. A normalized pair imposes a condition on its two responses, while
the weight's global domain retains the whole complex algebra.

| Condition | Earlier normalized-echo route | Single-echo route |
| --- | --- | --- |
| Complex algebra and serial multiplication | Supplied globally | Supplied globally |
| Continuity | Supplied globally | Supplied at one |
| Echo coverage | Every weight-normalized pair | One actual pair with both inputs nonzero |
| Zero and unit values, nonnegativity and conjugation invariance | Supplied weight laws | Derived consequences |
| Native coordinate mixer | Supplied | Supplied |
| Physical availability of contexts and operations | Separate obligation | Separate obligation |

The older theorem and its assumptions remain valid. The new theorem establishes
a weaker sufficient mathematical contract. Absolute minimality and the
physical realization of its witness remain open.
[Earlier normalized-echo route](189-normalized-echo-readout.md)

## Why continuity at one is enough

Multiplication against the normalized pair first gives `w(1)=1` and `w(0)=0`.
For every complex `z`, `exp(z)` is the square of `exp(z/2)`, so its response is
nonnegative. Its multiplicative inverse gives a nonzero response. Thus

```text
L(z) = log(w(exp(z)))
```

is defined with positive logarithm arguments. Multiplicativity makes `L`
additive. Continuity of `w` at one makes `L` continuous at zero, and a continuous
additive map between real vector spaces is real-linear. The exponential's
`2*pi*i` period removes the imaginary coefficient. Consequently

```text
w(z) = exp(p * log(norm(z)))       for z != 0
```

for one real exponent `p`.

The normalized nonzero pair excludes `p=0`. Write
`S = normSq(a) + normSq(b)`. Its echo gives `exp(p*log(S))=1`, hence `S=1`.
Both input norms therefore lie strictly between zero and one. If `p<2`, both
responses exceed their norm squares. If `p>2`, both responses are smaller.
Either strict comparison contradicts their normalized sum, leaving `p=2`.

This argument uses standard complex analysis and real linearity. Its formal
contract explicitly supplies the complex algebra, topology and multiplicative
weight law. The proof uses the raw-weight premises directly.
[Analytic character and exponent selection](../Proofs/QMClosure/SingleEchoReadout.lean)

## Controls separate the premises

| Control | Exact result |
| --- | --- |
| Norm square at `c=(1+i)/2` | A concrete nonzero balanced witness satisfies normalization and echo. |
| Quartic weight `normSq(z)^2` at `(1,0)` | Continuity at one, multiplicativity, normalization and echo hold, while the weight differs from norm square. The zero branch shows why this witness lacks nondegeneracy. |
| Quartic weight at an actual half-response input | Balanced normalization holds, and its echo response is four. |
| Nonzero-support indicator | It is continuous at one and satisfies every normalized echo. Every normalized pair has a zero branch, so the nondegenerate witness premise is unavailable. |

The support indicator's global discontinuity is compatible with its local
continuity at one. Together these controls distinguish deterministic echoes,
balanced normalization and the actual nondegenerate echo premise.
[Single-echo controls](../Proofs/QMClosure/SingleEchoReadoutControls.lean)

## Exact finite agreement on rational Gaussian inputs

The rational control uses the carrier `Q x Q` with named Gaussian operations

```text
(a,b) * (c,d) = (ac-bd, ad+bc),
conj(a,b) = (a,-b),
unit = (1,0),
N(a,b) = a^2+b^2.
```

For a prime `p`, define the rational-valued weight, then regard its value as a
real number,

```text
Wp(z) = N(z) * p^(v_p(N(z))).
```

The exponent is an integer. The valuation convention at zero gives zero
response there. For prime `p`, this weight is globally multiplicative,
nonnegative, unit-normalized and invariant under conjugation on the rational
Gaussian carrier.

For every finite set `S` of evaluated rational Gaussian points, choose an odd
prime greater than two and greater than the absolute numerators and positive
denominators of all norms in `S`. Their valuations vanish, so `Wp(z)=N(z)` at
every `z` in `S`. The same weight has the actual balanced input
`c=(1/2,1/2)`, with `Wp(c)=1/2` and balanced echo response one. It differs at
the real-prime coordinate, where `Wp(p,0)=p^4` and `N(p,0)=p^2`.

The quantifiers are `for every finite S, there exists p`. The chosen prime may
change with `S`, and each chosen weight retains its own disagreement point.
A fixed finite list of precomputed circuit nodes can be included in `S`.
The theorem's formal statement quantifies over the finite set of points.
[Prime family and finite readout wall](../Proofs/QMClosure/RationalEchoRegularityControl.lean)

## A discontinuity at the rational unit

For the fixed prime seven, `W7(7,0)=2401` while `N(7,0)=49`. The sequence

```text
z_n = (1 + 7^(-(n+1)), 0)
```

converges to `(1,0)` in the inherited Euclidean topology. Its responses satisfy

```text
W7(z_n) = (1 + 7^(-(n+1)))^2 * 7^(-2*(n+1)) -> 0,
W7(1,0) = 1.
```

Thus this weight fails continuity at the unit. The countable rational carrier
retains its inherited topology and nontrivial convergent sequences.
[Rational balanced control and discontinuity](../Proofs/QMClosure/RationalEchoRegularityControl.lean)

The finite-agreement result concerns exact evaluations at finitely many points
and fixed finite circuit nodes. Universally quantified law schemas, arbitrary
infinite algebraic closure, adaptive testing and statistical inference require
separate analysis. The rational construction's carrier is explicit. A
discontinuous full-complex Hamel construction remains an analytic proposal
outside the checked artifacts cited here.

## Reproducing the checks

Run the three proof targets and ledger sequentially from the repository root.

```bash
lake build Proofs.QMClosure.SingleEchoReadout
lake build Proofs.QMClosure.SingleEchoReadoutControls
lake build Proofs.QMClosure.RationalEchoRegularityControl
lake build Proofs.MetaLang.V8OperationalPrimitiveResearchLedger
```

All three registered proof-module builds passed on the frozen source. An
independent audit covered all 114 owning-module declarations across the three
proof modules, including generated declarations. The single-echo module
contributed 13 declarations, its controls 12, and the rational control 89.
There were zero private declarations, zero local axioms and zero unsafe
declarations. One shared dependency traversal found the exact transitive axiom
set `propext`, `Quot.sound` and `Classical.choice`.

The audit exited successfully in 42.13 seconds. The three proof-source hashes
and target-registration hash matched their approved values before and after
the audit. All 33 new declaration citations in the two updated research tasks
matched their audited owning modules. The earlier normalized-echo entry's 17
historical citations were preserved and checked separately.

## Remaining interpretation obligations

Physical identification of `Qraw`, Born readout, detector selection and event
actualization retain separate obligations. So do the spectral and Hilbert
representation, tensor and composite structure, dynamics, physical scales,
full QM and GR. The complex algebra and the actual pair's physical availability
remain supplied interpretation work. The rational witnesses establish
mathematical nonuniqueness on their stated carrier.

The bounded-likelihood process-rigidity theorem has proof artifacts for
one-way domination, essential-width elimination, density endpoints and
constancy for families absolutely continuous with respect to a finite atomic
internal reference, under its supplied exact process laws.
[Bounded likelihood process rigidity](192-bounded-likelihood-process-rigidity.md)

On the supplied rational Gaussian carrier, universal adjacent count order and
an actual nondegenerate normalized echo select the squared norm. Its direct
balanced specialization has a separate proof. The carrier, coherent
operations, reversal, universal order and physical echo preparation remain
supplied operational obligations. The signed and asymmetric controls remain
analytic proposals awaiting artifacts.
[Rational count-order readout](193-rational-count-order-readout.md)
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
