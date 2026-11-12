# Surjective two-port quadratic reconstruction

The conditional reconstruction starts with an additive commutative monoid and a
transparent symmetric two-port operation. Separate branch coverage, exact
first-axis recovery and full conserved nonnegative real readout force additive
inverses and a symmetric biadditive diagonal on the original carrier.
The authoritative task is `surjective_two_port_quadratic_origin` in the
[operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean).

## Supplied contract

Let `V` carry a supplied additive commutative monoid, with additive branches
`a,b : V → V`. Transparency holds for every preparation,

```text
a(x) + b(x) = x.
F(x,y) = (a(x)+b(y), b(x)+a(y)).
```

Each branch is onto `V`. Exact first-axis recovery means that every `p : V`
has `x,y : V` with `F(x,y)=(p,0)`. For this symmetric additive mixer, first-axis
recovery is equivalent to coverage of every output pair.
The readout `W : V → ℝ` has `W(0)=0`, is nonnegative everywhere, and satisfies

```text
W(a(x)+b(y)) + W(b(x)+a(y)) = W(x) + W(y)
```

for every independent input pair `x,y` in the complete declared carrier.
These universal coverage, recovery and conservation premises are explicit
parts of the theorem. [Group interface](../Proofs/QMClosure/TransparentSurjectiveMixingGroup.lean)
and [expanded reconstruction theorem](../Proofs/QMClosure/SurjectiveMixingQuadraticReadout.lean)

## Additive inverse from a finite positive expression

For a target `p`, choose `t` with `a(b(t))=p`, then recover `(t,0)` as `F(x,y)`.
The checked inverse witness is the finite expression

```text
q = a(b(b(x))) + a(a(y)) + a(a(y)) + a(b(a(y))) + b(x).
p + q = 0.
```

Its construction uses addition and forward branch applications after the
preimage and recovery witnesses have been supplied. Coverage of the composite
`a ∘ b` suffices at this stage. Separate branch surjectivity supplies it.

The data interface supplies functions `ra,rb : V → V` and `R : V → V × V`
with `a(ra(p))=p`, `b(rb(p))=p` and `F(R(t))=(t,0)`.
Then `t=rb(ra(p))` and `(x,y)=R(t)` make `negRecipe` explicit.
The functions retain their stated right-preimage and recovery laws.

The existence-only interface chooses inverse witnesses using `Classical.choose`.
The resulting group preserves the complete original `AddCommMonoid` record,
including addition, zero and natural repetition. The compatibility theorem
`Gate.additiveGroup_toAddCommMonoid` compiles with proof `rfl`.
Physical access to the chosen preparations, implementation of the data functions
and finite resource bounds remain separate obligations.
[Inverse construction](../Proofs/QMClosure/TransparentSurjectiveMixingGroup.lean)

## Conservation pairing and the additive remainder

Full two-input conservation, branch coverage and first-axis recovery make the
second additive difference of `W` independent of its base preparation.
The centered real polarization therefore defines a symmetric biadditive pairing

```text
B(u,v) = (W(u+v) - W(u) - W(v) + W(0)) / 2.
Q(x) = B(x,x).
W(x) = Q(x) + L(x).
```

Here `L : V → ℝ` is additive. This pairing is derived inside the reconstruction.
Once the group is available, nonnegativity at both `x` and `−x` gives

```text
Q(x) = (W(x)+W(−x))/2 ≥ 0.
|L(x)| ≤ Q(x)  for every x.
```

The proof also derives quadratic column conservation and commutation of `a,b`.
[Conservation pairing](../Proofs/QMClosure/TwoPortConservationPairing.lean)
and [readout decomposition](../Proofs/QMClosure/SurjectiveMixingQuadraticReadout.lean)

## Arbitrarily accurate halving through positive branch words

For an opposite-branch preimage `b(u)=x`, the endpoint estimate is
`(n+1) Q(a^n(x)) ≤ Q(u)`. The corresponding estimate with branches exchanged
controls the other endpoint. Define additive-endomorphism words by

```text
R_n = a^(2^n) + b^(2^n),
Y_0 = 0,
Y_(n+1) = Y_n + R_n Y_n + a^(2^n)b^(2^n).
```

Their checked identity is `2Y_n+R_n=id`. Each word has a finite positive
construction from addition, branch application and composition.
Endpoint estimates make `Q(R_n(x))` arbitrarily small for each fixed `x`.
For every real `ε>0`, the proof obtains original-carrier elements `y,r` with

```text
x = y+y+r,     Q(r)<ε,     |4Q(y)−Q(x)|<ε.
```

This statement expresses approximate quadratic halving through numerical error
bounds. Exact carrier halves remain a separate selection question.

If one constant `C≥0` satisfies `|L(z)|≤C Q(z)` for every `z`, the construction
improves the all-preparation bound to `|L(x)|≤(C/2)Q(x)` for every `x`.
Iteration from `C=1` gives `|L(x)|≤Q(x)/2^n` for every natural `n`.
Real Archimedean arithmetic forces `L(x)=0`.
The numerical argument uses real inequalities and finite carrier words.
Continuity of `W`, a topology or completed carrier, and scalar carrier action
remain additional structures beyond the theorem's inputs.
[Endpoint bounds, word recurrence and remainder rigidity](../Proofs/QMClosure/SurjectiveMixingQuadraticReadout.lean)

## Checked conclusion and identities

The end-to-end theorem gives a symmetric real biadditive pairing `B` with
`W(x)=B(x,x)` on the original additive monoid.
Under its derived group, the readout is even and obeys the parallelogram identity
and integer-square repetition. The original-monoid `count_square` theorem gives
`W(n • x)=(n:ℝ)^2 W(x)` for each natural `n`.
The generic branch-orthogonality theorem gives `B(a(x),b(x))=0` under transparency
and quadratic column conservation.
The conclusion allows null directions. Faithfulness and positive definiteness
require further premises. [Readout theorems](../Proofs/QMClosure/SurjectiveMixingQuadraticReadout.lean)

## Unequal-gain model and transparency control

The complex model adapts the existing unequal branches to the new gate.
Its normalized positive state has branch readouts `4/5` and `1/5`, with
`W(z)=Complex.normSq(z)`. It satisfies the reconstruction contract while
`a^n ≠ b^n` for every positive natural `n`.
Balanced gains and positive finite rejoin therefore retain separate selection
obligations under this contract.

The omission control uses finite multisets of finite binary words. Branch `A`
keeps the empty word and removes an initial `false`. Branch `B` removes an initial
`true`. Each branch discards words belonging to the other branch.
Prefixing supplies both branch preimages and exact recovery of every output pair.
The real cardinality readout is nonnegative and fully conserved.

Transparency fails on the original labels. A positive singleton `e` carrying
the empty word has `W(e)=1` and `W(e+e)=2`, and it has no additive inverse.
Its count readout admits no real biadditive diagonal.
For the singleton `p` carrying `[true]`, the raw readings agree at
`W(A(p)+B(p))=W(p)`. Applying the native `B` context gives readings `0` and `1`,
respectively. This witnesses observable failure of transparency in a branch
context. [Control contracts](../Proofs/QMClosure/SurjectiveMixingQuadraticReadoutControls.lean)

## Remaining origin and closure obligations

The independent physical origins of additive preparation, transparent branches,
universal coverage, exact recovery and lossless full-domain conservation remain
open. Physical reversal and executable preparation access require operational
contracts. Equal halves, Gaussian arithmetic, universal operator gain, normalized
paired echo retain their own obligations.
The older finite-rejoin continuation retains its pending formalization tasks.

Born actualization, Hilbert representation, dynamics, composite closure, full QM,
GR and physical-scale origins remain open. The overall research goal stays active.
