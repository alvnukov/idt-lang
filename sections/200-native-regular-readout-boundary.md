# A continuous faithful native-readout boundary

A checked family on the existing initial history presentation satisfies
normalized native transfer, reflection invariance and natural-count order, and
has a continuous ambient extension. For positive parameter values it is
nonnegative and faithful, while its fixed-corner pair sufficiency, general mixer
conservation and global multiplicativity fail at explicit inputs. Continuity,
faithfulness and scalar-count order therefore leave a readout-selection
obligation under this contract.
[Regular countercontrol source](../Proofs/QMClosure/NativeRegularReadoutCountercontrol.lean)
[Native selector and its supplied pair law](199-native-generator-half-mixture-readout.md)

## The concrete family and its carrier

Use the existing initial semiring quotient with \(a+b=1\) and
\(a^2+b^2=0\), its Gaussian-dyadic normal forms, and its faithful algebraic
map \(\operatorname{complexEval}\). On the ambient complex plane define

\[
\begin{aligned}
N(z)&=|z|^2,\\
H(z)&=\operatorname{Im}(z^4)
     =4xy(x^2-y^2),\qquad z=x+iy,\\
Q(z)&=\frac{H(z)^2}{N(z)^3},\qquad Q(0)=0,\\
F_c(z)&=N(z)+cQ(z),\\
W_c(p)&=F_c(\operatorname{complexEval}(p)).
\end{aligned}
\]

The Lean definition uses total division, which gives the stated zero value.
This explicitly defined family is a concrete control on the same carrier as
the native selector.
[Regular countercontrol source](../Proofs/QMClosure/NativeRegularReadoutCountercontrol.lean)
[Initial-presentation source](../Proofs/QMClosure/NativeInitialHistoryPresentation.lean)

The identity

\[
N(z)^4=\operatorname{Re}(z^4)^2+H(z)^2
\]

gives \(0\le Q(z)\le N(z)\). For every real parameter \(c\), the checked
ambient function \(F_c\) is globally continuous, including at the origin.
`counterWeight_has_continuous_extension` records the exact extension statement

\[
\exists F\colon\mathbb C\to\mathbb R,\quad
\operatorname{Continuous}(F)\ \land\
\forall p,\ W_c(p)=F(\operatorname{complexEval}(p)).
\]

Continuity here is an ambient extension property. A topology on the abstract
initial presentation remains an additional contract.
[Regular countercontrol source](../Proofs/QMClosure/NativeRegularReadoutCountercontrol.lean)

## Exact parameter-dependent contracts

For every real \(c\), the family has \(W_c(0)=0\), \(W_c(1)=1\),
\(W_c(a)=W_c(b)=1/2\), and the two universal native transfer laws

\[
W_c(ap)=\tfrac12W_c(p),\qquad
W_c(bp)=\tfrac12W_c(p)
\quad\text{for every presentation element }p.
\]

It is invariant under syntactic reflection. Its ambient real-axis values are
\(F_c(t)=t^2\) for every real \(t\). On the presentation, natural counts
satisfy \(W_c(n)=n^2\) and
\(W_c(m)\le W_c(n)\iff m\le n\). The checked dyadic scaling statement is
\(W_c(h^kp)=W_c(p)/4^k\), with \(h=1/2\).
[Regular countercontrol source](../Proofs/QMClosure/NativeRegularReadoutCountercontrol.lean)

For \(c\ge0\), the exact bounds are

\[
N(z)\le F_c(z)\le(1+c)N(z).
\]

Consequently \(W_c\) is nonnegative and \(W_c(p)=0\iff p=0\), using the
faithful algebraic evaluation. These are global statements on every presented
history under the stated parameter condition.
[Regular countercontrol source](../Proofs/QMClosure/NativeRegularReadoutCountercontrol.lean)

The canonical raw echo retains strictly positive intermediate weights
\(1/2,1/2\) and normalized total one. The grammar gives
\(T(1,0)=(a,b)\) and \(T(a,b)=(0,1)\), with
\(T(p,q)=(ap+bq,bp+aq)\). Its weight statements hold for every real \(c\)
through the native-transfer contract. The following finite controls concern
additional universal readout laws.
[Regular countercontrol source](../Proofs/QMClosure/NativeRegularReadoutCountercontrol.lean)

## Finite witnesses for every positive parameter

Let \(c>0\) and \(\alpha=576c/125>0\). On the prescribed four corner
probes of the integer restriction, both seed pair sums equal \((2,2,2,2)\).
After translating the four sources by \(+1\), the sums are

\[
(2,6,2,6+\alpha),\qquad(2,6+\alpha,2,6).
\]

This is an exact counterexample to the universal single-continuation pair law.
Its native generator normalization and transfer laws remain satisfied at every
presentation input.
[Regular countercontrol source](../Proofs/QMClosure/NativeRegularReadoutCountercontrol.lean)

The same parameter gives all the following checked values.

- \(W_c(2+u)=5+\alpha\), while the ordinary squared norm there is five.
- At mixer input \((1,2)\), total raw weight changes from \(5\) to
  \(5+\alpha\).
- Raw third-order inclusion-exclusion at \((1,1,u)\) equals \(\alpha\).
- The multiplication defect is

\[
W_c(2+u)^2-W_c((2+u)^2)
=\frac{1152c(527+288c)}{15625}>0,
\qquad u^2=-1.
\]

Each witness holds for every positive \(c\). They supply an exact boundary for
replacing the selector's universal pair-sufficiency premise by continuity,
faithfulness and natural-count order. The total canonical raw echo and the
all-input conservation obligation retain their stated quantified scopes.
[Regular countercontrol source](../Proofs/QMClosure/NativeRegularReadoutCountercontrol.lean)

## Analytic regularity and vacuum questions

Stronger regularity claims have parent-reviewed analytic arguments and await
Lean artifacts. The proposed ambient result is global \(C^{1,1}\) regularity
with gradient Lipschitz bound \(2+32|c|\), real analyticity away from zero, and
failure of twice Fréchet differentiability at zero when \(c\ne0\).
For \(c=1/32\), the analytic argument also gives global strong convexity using an off-origin
Hessian lower bound \(17/16\), and a two-dimensional real Banach norm
\(\sqrt{F_c}\).
Its squared-norm parallelogram defect at \(1,2i\) is \(36/125\). The scalar
field for this norm claim is \(\mathbb R\). These claims are recorded in an
analytic ledger task with empty checked evidence.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

A second analytic task considers a common quadratic vacuum expansion. Supply one
common homogeneous real quadratic form \(q\), an expansion
\(R(z)=q(z)+o(|z|^2)\) at zero, and exact dyadic scaling
\(R(z/2)=R(z)/4\). The contraction argument proposes \(R=q\) globally.
The values at \(1,i,1+i\) would then select \(q=N\). The common quadratic
tangent is a supplied structural assumption with an open physical origin.
Directional second derivatives alone do not supply the common quadratic
expansion, even with exact dyadic scaling and native calibration. For
\(c\ne0\), the analytic family has those directional derivatives with
nonbilinear dependence. The vacuum selector and its regularity comparison
remain awaiting formalization.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Verification and physical scope

The registered target compiled successfully with lint warnings. Its exact-origin
audit covered 84 declarations, including 14 private declarations, with zero
local axioms and zero unsafe declarations. Its aggregate transitive axiom set
was exactly `propext`, `Quot.sound` and `Classical.choice`. Source hashes remained
unchanged through the audit.

Targeted dependency profiles compared this artifact's closure against a named
list of 17 prior modules, with explicit permitted definitions and native-transfer
and echo lemmas. They reported zero forbidden dependencies under that policy.
The ambient-continuity profile reached zero declarations from those listed
modules. The operational ledger keeps the checked continuity boundary and the
stronger analytic regularity tasks at their respective stages.
[Regular countercontrol source](../Proofs/QMClosure/NativeRegularReadoutCountercontrol.lean)
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The family is an algebraic raw-readout control. Physical origins of the grammar,
readout and operational sufficiency remain open, together with event frequencies,
Born actualization, Hilbert representation, full QM closure and physical scales.
[Physical scope boundary](150-physical-scope-boundary.md)
