# Rational raw-weight selection from universal count order

On the supplied rational Gaussian carrier, universal adjacent count order and
one actual nondegenerate normalized echo select the squared norm as the real
raw weight. The result concerns `Q x Q` with its named coherent operations.
The real Archimedean codomain remains supplied.
[Rational count-order selection](../Proofs/QMClosure/RationalCountOrderReadout.lean)

## The sufficient contract

Write `z=(a,b)` and supply the rational Gaussian operations

```text
(a,b) * (c,d) = (ac-bd, ad+bc),
conj(a,b) = (a,-b),
unit = (1,0),
N(a,b) = a^2+b^2.
```

Let `w : Q x Q -> Real` satisfy

```text
w(z) >= 0,
w(0,0) = 0,
w(1,0) = 1,
w(z*t) = w(z)*w(t),
w(conj(z)) = w(z),
for every natural n, w(n,0) <= w(n+1,0).
```

Supply one actual pair `a,b` of nonzero carrier points with

```text
w(a)+w(b) = 1,
w(a*conj(a)+b*conj(b)) = 1.
```

Then `w(z)=N(z)` for every rational Gaussian point `z`. The pair can have
unequal responses. A balanced witness is a sufficient specialization with
its own direct proof. The general theorem's premises are exactly the displayed
weight laws and nondegenerate normalized echo.
[Weight laws, echo contracts and selection theorem](../Proofs/QMClosure/RationalCountOrderReadout.lean)

## The arbitrary-pair proof

For the scalar restriction `f(q)=w(q,0)`, adjacent natural-count order gives
monotonicity on all natural counts. Complete multiplicativity gives
`f(n^k)=f(n)^k`. Dyadic brackets compare the count and its response on the same
powers,

```text
2^m <= n^k <= 2^(m+1).
```

Taking logarithms gives one logarithmic slope on positive natural scalars.
Multiplicativity extends it to positive rational scalars,

```text
f(q) = exp(alpha * log(q))       for positive rational q.
```

Conjugation invariance gives `w(z)^2=f(N(z))`, and nonnegativity gives a radial
character

```text
w(z) = exp(p * log(N(z)))       for z != 0,
p = alpha/2.
```

The nondegenerate normalized pair excludes `p=0`. Its echo forces
`N(a)+N(b)=1`, placing both squared norms strictly between zero and one. If `p<1`,
both raw weights exceed their squared norms. If `p>1`, both are smaller. Each case
contradicts normalization, so `p=1` and the scalar exponent is `alpha=2`.
The argument uses the supplied real Archimedean structure and real logarithms.
[Scalar character, radial character and arbitrary-pair theorem](../Proofs/QMClosure/RationalCountOrderReadout.lean)

## A separate direct balanced proof

For an actual balanced witness `c` with `w(c)=1/2` and its normalized echo,
multiplicativity first gives `f(2)=4`. For each positive natural `n`, the same
dyadic bracket bounds both `f(n)^k` and `n^(2*k)` between `4^m` and
`4^(m+1)`. Both ratio powers are bounded by four for every `k`. Archimedean
unbounded powers force `f(n)=n^2`. Integer signs and rational denominators
extend this scalar identity to all rationals, and conjugation plus
nonnegativity gives `w(z)=N(z)`.

This direct balanced proof and the arbitrary-pair proof have separate exported
theorems. Both use universal count order. Continuity assumptions are absent
from their signatures.
[Balanced echo and dyadic square-character proof](../Proofs/QMClosure/RationalCountOrderReadout.lean)

## Finite agreement can coexist with a count drop

For every finite evaluation set `S` of rational Gaussian points, the existing
prime family supplies a prime `p>2` with

```text
Wp(z) = N(z)       for every z in S.
```

The selected weight retains nonnegativity, zero and unit normalization,
Gaussian multiplicativity, conjugation invariance and an actual nondegenerate
balanced normalized echo. Its adjacent count responses satisfy

```text
Wp(p,0) = p^4,
Wp(p+1,0) = (p+1)^2,
Wp(p+1,0) < Wp(p,0).
```

Thus every selected prime weight violates the universal adjacent count-order
schema at its own prime count. The quantifiers are `for every finite S, there
exists p(S)`. Finite agreement and the universal order premise have different
quantifier scopes.
[Finite agreement with count-order failure](../Proofs/QMClosure/RationalCountOrderReadoutControls.lean)
[Retained prime-family weight laws](../Proofs/QMClosure/RationalEchoRegularityControl.lean)

## Analytic controls awaiting artifacts

Two further controls remain analytic proposals with no checked artifact.
The proposed signed weight `N*(-1)^v_5(N)` would retain the stated scalar count
order and balanced echo while violating nonnegativity. The proposed asymmetric
Gaussian-prime weight `N*5^(v_(2+i)-v_(2-i))` would retain positive weights,
count order and the balanced echo while violating conjugation invariance.
Their valuations, retained laws and witness evaluations require separate
machine-checkable proofs. The two proof modules cited above establish the
selection routes and the prime-family count-order failure.
[Research task and future-control boundary](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Reproducing the checks

Run the proof targets and ledger sequentially from the repository root.

```bash
lake build Proofs.QMClosure.RationalCountOrderReadout
lake build Proofs.QMClosure.RationalCountOrderReadoutControls
lake build Proofs.MetaLang.V8OperationalPrimitiveResearchLedger
```

All seven frozen proof-module builds passed. A shared dependency audit across
the five bounded-likelihood modules and two rational count-order modules
covered all 205 owning-module declarations, including generated declarations
and one private declaration. It found zero local axioms and zero unsafe
declarations. The exact aggregate transitive axiom set was `propext`,
`Quot.sound` and `Classical.choice`.

The audit exited successfully in 47.964 seconds. All seven proof-source hashes
and the target-registration hash matched their approved values before and
after the audit. All 33 declaration citations across the two updated research
tasks matched their audited owning modules.

The rational count-order task cites 12 declarations across its two modules.

## Physical interpretation boundary

The conclusion identifies the raw weight on the supplied rational Gaussian
carrier. Extension to the full complex carrier requires additional premises.
The raw weight takes unbounded values, including `w(2,0)=4`, and its probability
interpretation requires a separate bridge.

The histories-to-carrier construction, coherent addition and serial
multiplication, physical reversal invariance, universal count order and the
availability of an actual nondegenerate echo remain operational obligations.
Physical identification of `Qraw`, Born readout, detector selection and event
actualization remain open. So do spectral and Hilbert representation, tensor
and composite structure, dynamics, physical scales, full QM and GR. The
research ledger records the mathematical result as a conditional kernel theorem.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The subsequent reversible echo controls distinguish actual undo, conjugate
return reciprocity and same-scale raw accounting. They also exhibit a finite
scalar obstruction to reflection descent and prove a one-row conditional echo
bridge. [Reversible echo and scalar reflection boundaries](194-reversible-echo-and-scalar-reflection-boundaries.md)
