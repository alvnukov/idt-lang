# Local history algebra and conditional destructive selection

Two exact local history identities now give a checked algebraic classification in an arbitrary semiring. They derive commutation of the selected pair, a canonical idempotent and finite inverse words. Additional readout assumptions select destructive cancellation and duplication gain four. The physical source of the grammar, history identities and readout assumptions remains open. [Research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## What the two history identities give

Assume a semiring carrier and two elements satisfying

\[
a+b=1,\qquad a^4=b^4.
\]

These are equalities in the carrier, usable inside every algebraic context. Their physical justification requires that contextual identification. Agreement of a few measured responses leaves that obligation open.

The supplied grammar includes associative sequential composition, commutative parallel composition, distributivity, zero, unit and natural counting. Within that grammar, positive geometric words give two-sided inverses for the generators and establish `Commute a b`. The result concerns this selected pair. Serial commutation with unrelated carrier elements remains a separate question. [Pure two-relator core](../Proofs/QMClosure/FourthRejoinIdempotentCore.lean)

Set

\[
T=a^2+b^2,\qquad e=2T.
\]

The checked identities include `2T²=T`, `e²=e`, `eT=T` and `ae=be=ea=eb=T`. They give `e=0` exactly when `T=0`, and `e=1` exactly when `a=b`. Consequently, at least one of the following holds.

| Alternative | Algebraic content |
|---|---|
| Destructive | `T=0` |
| Equal generators | `a=b` |
| Mixed | `e` is an idempotent distinct from zero and one |

This is a disjunction. In a trivial semiring its alternatives may overlap. The pure classification assumes the supplied semiring operations and two relators. It assumes no readout, positivity, continuity or additive cancellation. The selected readout contracts also assume no additive cancellation. [Classification core](../Proofs/QMClosure/FourthRejoinIdempotentCore.lean)

The following elements have explicit two-sided inverse words.

| Element | Inverse word |
|---|---|
| `a` | `2b+e` |
| `b` | `2a+e` |
| `ab` | `2+2e` |
| `2` | `ab+T²` |

These are formal generated histories under the supplied grammar. Their availability as laboratory protocols requires a physical interpretation and implementation. Arbitrary normalized echoes require further obligations. [Inverse-context theorems](../Proofs/QMClosure/FourthRejoinIdempotentCore.lean)

Concrete complex, real and product models realize the three alternatives. A restricted product carrier also has additive cancellation and no zero divisors while retaining a nontrivial idempotent. Its ambient complement and generator difference lie outside the carrier. Coefficient-idempotent purity therefore remains an additional structural premise. With unequal generators, that explicitly supplied purity forces `T=0`. Its scope is the coefficient carrier, and its physical selection remains open. [Three algebraic controls](../Proofs/QMClosure/FourthRejoinIdempotentControls.lean) · [Positive-carrier control](../Proofs/QMClosure/FourthRejoinPositiveCarrierControl.lean)

## Two conditional readout routes

The checked routes expose different supplied assumptions and conclusions.

| Route | Supplied inputs | Checked outcome |
|---|---|---|
| Fixed unknown duplication gain | Semiring carrier, `a+b=1`, `a^4=b^4`, explicit `Commute a b`, `W(1)=1`, global zero detection, global column conservation, one input-independent gain `k`, and `W(2) ≠ 2` | `T=0`, `2ab=1`, both global half laws, `k=4`, finite algebraic inverse witnesses |
| Common natural reciprocal cross | Semiring carrier, `a+b=1`, a natural `d` with `d*(a*b)=1`, `W(1)=1`, both global half laws, and one uniform mixed-increment sign on natural count bags | Either `d=2` and quadratic counts, or `d=4` and linear counts |

The installed unknown-gain contract retains an explicit pair-commutation field. The pure two-relator theorem supplies that field separately. Its public zero-detection premise is global. A finite-context helper localizes the proof at `T`, while physical justification of global zero detection remains an open obligation. Positivity, continuity and mixed-increment signs are absent from this route's contract. Selection of a unique norm remains open. [Unknown-gain core](../Proofs/QMClosure/DuplicationGainDestructiveCore.lean)

The common-natural-scalar route classifies the responses to natural bags `n*a+m*b`. It requires no fourth-rejoin equality `a^4=b^4`.

\[
\begin{aligned}
d=2&:\quad W(na+mb)=(n^2+m^2)/2,\\
d=4&:\quad W(na+mb)=(n+m)/2.
\end{aligned}
\]

Finite contrast `W(2a) ≠ W(1)` selects the quadratic branch. Additional global zero detection then gives `T=0` and additive inverses throughout the carrier. The universal sequence recurrence has a complete checked classification, including exclusion of `d=3`. The cubic-relator adapter itself works in an arbitrary semiring. A formula for responses outside the natural-bag family requires further premises. [Sequence classification](../Proofs/QMClosure/IntegerReciprocalCountClassification.lean) · [Semiring adapter and pure cubic helper](../Proofs/QMClosure/SemiringReciprocalCrossClassification.lean)

The standard complex pair with norm-squared response inhabits both selected contracts. Separate omission controls exhibit the roles of finite contrast, global zero detection and fixed gain. Distinct dual-number generators still realize the linear reciprocal-cross branch, so unequal generators alone leave that branch available. This dual control belongs to the reciprocal-cross family. [Unknown-gain inhabitants and omission controls](../Proofs/QMClosure/DuplicationGainDestructiveControls.lean) · [Complete quadratic witness](../Proofs/QMClosure/ReciprocalCrossQuadraticWitness.lean) · [Classical and dual controls](../Proofs/QMClosure/ReciprocalCrossClassificationControls.lean)

## Carrier choice and physical origin

A checked obstruction already applies whenever a carrier is supplied with a real semiring homomorphism sending both generators to `1/2`. That shadow sends `T` to `1/2`, excluding the full unknown-gain contract on that carrier. Grammar and the two relators therefore leave a carrier-selection question. [Provided-shadow obstruction](../Proofs/QMClosure/DuplicationGainDestructiveCore.lean)

The ledger records a future initial-presentation construction with only the two relators. Its universal map property, real shadow and nontriviality await proofs. A further planned obligation identifies its `e=0` quotient with the existing destructive initial presentation through opposite universal maps and generator extensionality. This new initial object and quotient equivalence remain unimplemented. [Initial-carrier and quotient obligation](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

Physical sources for the grammar, exact fourth rejoin, contextual transparency, fixed gain, zero detection, columns, mixed-sign constraint and echo availability remain open. Born actualization, Hilbert reconstruction, full QM, GR and physical-scale closure also remain open. [Physical scope boundary](150-physical-scope-boundary.md)
