# Native readout from adjacent-square continuation

On the existing initial history presentation, a readout selector uses
one normalization, two universal native-generator transfers and a continuation
rule restricted to adjacent squares. Its independent argument propagates a
zero mixed difference across the integer lattice, then uses the native
quadratic recurrence and Gaussian-dyadic normal forms. A companion route starts
with a universal pair law on two fixed translated probes.
[Local-square source](../Proofs/QMClosure/NativeLocalSquareReadout.lean)
[Two-probe source](../Proofs/QMClosure/NativeTwoProbeContinuationReadout.lean)

## Common native premises

The carrier is the existing initial presentation with
\(a+b=1\) and \(a^2+b^2=0\), together with its ring, phase \(u\), half
\(h\), and faithful Gaussian-dyadic representation. Supply an arbitrary real
readout \(W\) satisfying

\[
W(a)+W(b)=1,\qquad
W(ap)=W(a)W(p),\qquad W(bp)=W(b)W(p)
\quad\text{for every presentation element }p.
\]

The published native-transfer lemmas give unit and zero readings,
\(W(a)=W(b)=1/2\), phase invariance and diagonal scaling under these premises.
Set \(f(m,n)=W(m+nu)\), \(e=(1,0)\), and prescribe

\[
P_2(z)=\bigl(f(z),f(z+e)\bigr).
\]

These coordinates are fixed translates of the same integer restriction.
External pair-sum arithmetic expresses equal-half ensemble means. Its physical
preparation interpretation remains supplied.
[Native transfer source](../Proofs/QMClosure/NativeGeneratorMixtureReadout.lean)
[Two-probe source](../Proofs/QMClosure/NativeTwoProbeContinuationReadout.lean)

## Universal two-probe continuation and its scalar limit

The two-probe premise quantifies every source quadruple
\(x,y,v,w\in\mathbb Z^2\)

\[
P_2(x)+P_2(y)=P_2(v)+P_2(w)
\ \Longrightarrow\
P_2(x+e)+P_2(y+e)=P_2(v+e)+P_2(w+e).
\]

Applying it at heights zero and one transports the full four-corner probe
vector under \(+e\). The existing native four-corner selector then supplies
\(W(p)=\operatorname{normSq}(\operatorname{complexEval}(p))\) on every
presented history. The norm-model witness satisfies the exact two-probe
contract.
[Two-probe source](../Proofs/QMClosure/NativeTwoProbeContinuationReadout.lean)
[Published four-corner selector](../Proofs/QMClosure/NativeSingleContinuationReadout.lean)

The companion scalar obstruction concerns one fixed translate
\(z\mapsto f(z+t)\) with arbitrary offset \(t\). Duplicate the sources
\(e-t,e-t\) and \(-e-t,-e-t\). Native calibration gives equal initial sums
\(2=2\). After \(+e\), the sums are \(8\) and \(0\). Thus within fixed
scalar translates carrying this universal source-quadruple contract, two probes
are sufficient and one is impossible under the native premises.
[Two-probe source](../Proofs/QMClosure/NativeTwoProbeContinuationReadout.lean)

## The restricted adjacent-square rule

The independent route supplies the continuation implication only for the
quartet \((z,z+e+i,z+e,z+i)\), for every integer-lattice base point \(z\)

\[
\begin{aligned}
P_2(z)+P_2(z+e+i)&=P_2(z+e)+P_2(z+i)\\
&\Longrightarrow\\
P_2(z+e)+P_2(z+2e+i)&=P_2(z+2e)+P_2(z+e+i).
\end{aligned}
\]

Define the mixed square difference

\[
D(z)=f(z)+f(z+e+i)-f(z+e)-f(z+i).
\]

The antecedent is exactly \(D(z)=D(z+e)=0\). The restricted rule is therefore
equivalent to

\[
\forall z,\quad D(z)=0\ \land\ D(z+e)=0
\quad\Longrightarrow\quad D(z+2e)=0.
\]

Native quarter-turn invariance gives \(D(Kz)=-D(z)\) for
\(Kz=iz-e\), and native calibration supplies \(D(0)=0\). The map
\(K^2z=-z-e-i\) preserves \(D\), allowing the forward rule to propagate
backward as well. Two adjacent zeros fill a row. The seed and its transformed
copies give rows zero and minus one, then columns minus one and zero. Every
row consequently has the adjacent zeros needed for \(D\equiv0\).
[Local-square source](../Proofs/QMClosure/NativeLocalSquareReadout.lean)

The resulting rectangle identity separates coordinates. Native diagonal scaling
supplies the axis parallelogram law and integer quadratic recurrence. The
independent core therefore gives \(f(m,n)=m^2+n^2\), followed by

\[
W\bigl(h^k(m+nu)\bigr)=\frac{m^2+n^2}{4^k}.
\]

Only after this selection, the source reconstructs universal two-probe and
four-corner pair laws. The existing full native/pair contract then supplies
global multiplication, syntactic-reflection invariance, nonnegativity,
faithfulness and all-input mixer conservation. Its published natural-count and
raw \(I_3=0\) theorems retain their actual full-contract hypotheses.
[Local-square source](../Proofs/QMClosure/NativeLocalSquareReadout.lean)
[Native consequences](../Proofs/QMClosure/NativeGeneratorMixtureReadout.lean)

## Contract comparisons away from the native premises

For these comparisons, \(P_4\) is the four-corner vector
\((f(z),f(z+e),f(z+i),f(z+e+i))\), with the universal \(+e\) pair law.
The checked artifacts provide exact controls on arbitrary real lattice
functions.

- Universal \(P_2\) continuation implies both \(P_4\) continuation and the
  restricted square rule. The function \(x^3+xy\) satisfies the \(P_4\) law
  while violating the \(P_2\) law. [Two-probe source](../Proofs/QMClosure/NativeTwoProbeContinuationReadout.lean)
- The separable quartic \(x^4+y^4\) has \(D\equiv0\) and satisfies the
  restricted rule, while violating universal \(P_4\) and \(P_2\)
  continuation. At the quartet \((0,1),(-1,-2),(1,0),(-2,-1)\), both initial
  \(P_4\) sums are \((18,18,18,18)\). After \(+e\), coordinate one is
  \(34\) and \(82\). [Local-square source](../Proofs/QMClosure/NativeLocalSquareReadout.lean)
- The projected quartic \(q(x+2y)\), with \(q(t)=t^4-4t^2\), satisfies
  \(P_4\) continuation. Its successive square differences at
  \((-2,0),(-1,0),(0,0)\) are \(0,0,48\), violating the restricted rule.
  Thus restricted and \(P_4\) continuation are incomparable on arbitrary
  lattice readouts. [Local-square source](../Proofs/QMClosure/NativeLocalSquareReadout.lean)

Under the common native premises, the restricted rule and universal
\(P_2\) law are each equivalent to the squared-norm readout. The published
\(P_4\) selector and norm witness give the corresponding native
characterization for \(P_4\).
[Local-square source](../Proofs/QMClosure/NativeLocalSquareReadout.lean)
[Published four-corner selector](../Proofs/QMClosure/NativeSingleContinuationReadout.lean)

## The continuous faithful family still meets a finite obstruction

For the published regular family with \(c>0\) and
\(\alpha=576c/125>0\), the new exact calculation gives

\[
D(-1,-1)=D(0,-1)=0,\qquad D(1,-1)=-\alpha.
\]

At base point \((-1,-1)\), both initial \(P_2\) square-pair sums are
\((2,2)\). Their continued sums are \((2,6)\) and \((2,6+\alpha)\).
This controls the restricted premise while preserving the family's published
native transfer, ambient continuity and faithfulness contracts.
[Local-square source](../Proofs/QMClosure/NativeLocalSquareReadout.lean)
[Continuous faithful boundary](200-native-regular-readout-boundary.md)

## Analytic original-occurrence and resource obligations

A linked successor to the finite-history frontier records an accepted analytic
route using the original tagged \(a,b\) occurrences. Supply one finite order
\(K\), fixed signed coefficients \(\kappa_{jk}\), dependence only on the two
label counts, and compatibility with evaluation of every additive bag

\[
W(na+mb)=\sum_{j+k\le K}\kappa_{jk}
 {n\choose j}{m\choose k},\qquad n,m\in\mathbb N.
\]

Counting tagged subsets produces a bivariate polynomial. Native doubling selects
degree two, and the values at \(a,b,a+b\) select \((n^2+m^2)/2\).
The phase action \(ua=-b\), \(ub=a\) covers the four sign quadrants.
The identity \(m+nu=(m+n)a+(m-n)b\), followed by half scaling, extends the
proposed formula to the generated carrier. The accepted v2 compiler, selector
and insertion-only polynomial adapter remain uncompiled with empty checked
evidence. A planned adapter applies that analytic selector to the published
regular family, excluding a compatible finite original-occurrence kernel for
positive parameters. Newton-basis coefficient uniqueness remains a separate
artifact obligation. A uniform original-ancestry bound is a supplied regularity
premise whose physical origin remains open.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

A separate analytic resource argument starts from native unit calibration and
doubling, which give \(W(2^k)=4^k\). This subsequence excludes a uniform affine
upper bound on \(W(n)\). The argument uses the native transfer contract
independently of the subset compiler and full norm-selection route. Its accepted
`NativeBoundedResourceWall.lean` draft remains uncompiled.

At token size \(N\), every firing must be reachable from at most \(AN+H\)
initial roots in a dependency graph with input-independent finite depth and
outgoing degree bounds. The constant \(H\) permits fixed background roots.
Every firing and all its events are counted, with uniform event-count and
nonnegative event-weight ceilings. Repeated uses of the same component are
distinct firing occurrences. These assumptions give an affine bound on the
complete event total in \(N\).

For original \(a,b\) inputs, scalar \(n\) is the diagonal
\(\operatorname{bag}(n,n)=n(a+b)=n\), containing \(2n\) tagged tokens.
A linear/affine physical assembly-cost bridge therefore uses input size
\(2n\). An additional fixed nonnegative ceiling
\(W(n)\le\omega\,\operatorname{events}(2n)\) would impose an affine raw
readout bound, conflicting with the native power-of-two subsequence. Exact
positive-calibration identification is a special case. History occurrences are
syntactic objects. Their interpretation as physical inputs, roots, firing
occurrences or events requires the additional model. The subset-kernel
representation permits growing subset participation as input size increases.
Binary arity alone leaves uniform original ancestry unresolved.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Verification and physical scope

Both registered targets compiled successfully. Their joint exact-origin audit
covered 73 declarations, with 24 from the two-probe module and 49 from the
local-square module, including zero private declarations. It reported zero
local axioms and zero unsafe declarations, with exactly `propext`, `Quot.sound`
and `Classical.choice` as the aggregate transitive axiom set. Source hashes
remained unchanged through the audit.

The independent restricted-core profile traversed 14,365 constants and reached
35 permitted prior declarations, with zero rejected under its closed policy.
The P2/scalar and countercontrol profiles also passed. A separate postselection
profile covers the adapters using the recovered full-pair contract and permits
the later selector APIs involved there.

The policy retains a structural `NativeTransfer.*` allowance. Two individually
inspected generated arithmetic helpers have exact-name permissions, and the
regular-control origin is permitted in its dedicated countercontrol profile.
The ledger records these conditional results alongside the uncompiled analytic
successors.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The common native grammar, real normalized readout, universal transfer contexts,
restricted external pair arithmetic and physical sufficiency remain supplied
contracts. Event frequencies, Born actualization, Hilbert representation, full
QM closure and physical scales retain open obligations. Existing analytic
regularity and vacuum tasks keep their current status.
[Physical scope boundary](150-physical-scope-boundary.md)
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
