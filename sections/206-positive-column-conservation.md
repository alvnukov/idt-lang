# Positive column conservation and native transfer

## Current status

The checked conditional result derives the two native half-transfer laws from real nonnegative column conservation throughout a forward-closed source family. The generic core, native adapter, controls and exact cross-increment composition have accepted registered Lean builds, complete actual-origin/type/body auditing and independent final review. The relative-error branch bound, every-natural-depth absolute-error branch bound and their native lower controls now have the same accepted checks. The column, relative-error and checked absolute-error records have stage `conditionalKernelTheorem`, review `parentAccepted` and exact checked citations. The finite-depth, optimized integer-depth square-root upper, norm-drift and dyadic stability records retain `analyticAwaitingFormalization`, `notYetKernelChecked` and empty checked evidence.

## Exact source-local contract

Let \(M\) be a commutative monoid with distinguished \(a,b\) satisfying \(a^4=b^4\). Let \(W:M\to\mathbb R\), fix \(p\in S\subseteq M\), and assume that \(S\) is closed under multiplication by each generator. Require, for every \(x\in S\),

\[
W(x)\ge0,\qquad W(ax)+W(bx)=W(x).
\]

The checked conclusion is

\[
W(ap)=W(bp)=\tfrac12W(p).
\]

The source family may be just the forward orbit of the chosen preparation. Arbitrarily long finite generator words remain in its quantified contract. Every slot used at the intermediate source \((ab)^2p\) is a forward word from \(p\). Real Archimedean order and arbitrary serial depth remain inputs to the argument.
[Generic source](../Proofs/QMClosure/PositiveColumnConservationCore.lean)

The generic statement is `PositiveColumnConservationCore.local_branch_balance`. Its four-cycle proof uses the readings at

\[
(ab)^na^4p,\quad(ab)^na^3bp,\quad
(ab)^na^2b^2p,\quad(ab)^nab^3p.
\]

Two conservation expansions give a four-cycle recurrence. Total mass scales by four and opposite-slot differences scale by two. Nonnegativity bounds each absolute difference by the total. Thus \(2^n|d|\le C\) for every natural \(n\), and Archimedean real order forces \(d=0\). The cycle's parity identity equalizes all four slots. Expanding each first branch three further times then yields equal branch readings.
[Generic source](../Proofs/QMClosure/PositiveColumnConservationCore.lean)

An illustrative analytic control takes ordinary nonnegative real sources, \(a=b=1/2\) and \(W(x)=x\). It satisfies equal fourth powers, forward closure, positivity and exact column conservation, and the conclusion is immediate. Its addition gives \(a^2+b^2=1/2\). The native destructive relation would require this sum to vanish. This elementary model records the limited generic conclusion. The native algebra and the later quadratic count selector have their own additional contracts. This illustration has analytic status and empty checked evidence.

The native adapter uses the existing presented-history algebra. Its supplied destructive grammar gives the equal fourth histories. Globally nonnegative column conservation together with \(W(1)=1\) then gives `NativeTransfer W`, whose fields require

\[
W(1)=1,\qquad W(ax)=W(x)/2,\qquad W(bx)=W(x)/2
\quad\text{for every presented history }x.
\]

Consequently the native predicates are equivalent,

\[
\begin{aligned}
&[W\ge0]\ \land\ [W(1)=1]\ \land\
 [\forall x,\ W(ax)+W(bx)=W(x)]\\
&\qquad\Longleftrightarrow\quad [W\ge0]\ \land\ \operatorname{NativeTransfer}(W).
\end{aligned}
\]

Nonnegativity occurs on both sides. The source-local argument requires neither unit normalization nor a separate unattenuated phase-availability premise. The normalized adapter obtains individual half transfers as conclusions. The grammar, forward composition, nonnegativity, conservation and unlimited serial scope retain explicit supplied roles.
[Native source](../Proofs/QMClosure/PositiveColumnConservation.lean)

## Countercontrols and surviving readouts

Write \(z=\operatorname{complexEval}(p)\) and \(N(p)=|z|^2\). The native complex generators are \((1+i)/2\) and \((1-i)/2\).

The readout \(W(p)=\operatorname{Re}z\) is normalized and column-conserving. Its response on the original a,b bag cone is \((n+m)/2\), which is nonnegative and has zero mixed increments. The checked serial witness uses the native `phase`, whose reading is zero and whose two branch readings are \(-1/2\) and \(1/2\). Positivity restricted to the original bag cone therefore leaves an explicit countercontrol to the serial theorem's conclusion.
[Control source](../Proofs/QMClosure/PositiveColumnConservationControls.lean)

The quartic readout \(N^2\) is positive and unit-normalized. At the unit source its two column values sum to \(1/2\), demonstrating failure of conservation. Without normalization, scalar multiples of a solution and the zero readout preserve the source-local equations.
[Control source](../Proofs/QMClosure/PositiveColumnConservationControls.lean)

An ordered-vector control takes values in lexicographically ordered real pairs,

\[
L(p)=\bigl(N(p),\operatorname{Re}z-N(p)\bigr).
\]

It is normalized at \((1,0)\), faithfully lex-positive and column-conserving. Its phase reading is \((1,-1)\) and its first phase-branch reading is \((1/2,-1)\), which differs from half the phase reading. The positive pair \((0,1)\) remains below \((1,0)\) after every dyadic rescaling. The value space here has its ordered additive and real-vector structure. Any ordered-ring or ordered-field interpretation would require a separate construction. This control records the role of the real-valued Archimedean contract.
[Control source](../Proofs/QMClosure/PositiveColumnConservationControls.lean)

For every fixed finite serial depth \(K\), the normalized perturbation
\(N+2^{-K}\operatorname{Im}z\) stays nonnegative through that depth and has unequal first-column values. Its later serial behavior is part of the finite-depth boundary.
[Control source](../Proofs/QMClosure/PositiveColumnConservationControls.lean)

The existing positive regular native counterfamily satisfies `NativeTransfer` and hence column conservation. It continues to distinguish the column theorem from the subsequent readout selector. Adding the uniform cross-increment sign contract of section 205 selects \(N\) under the supplied native algebra and normalization. The physical origin of that sign remains open.
[Cross-increment route](205-local-cross-increment-readout.md)

The separate checked `ConservativeCrossIncrementReadout` module states this composition for a global sign and for one eventual uniform sign. Both theorems assume global nonnegativity, \(W(1)=1\), and exact conservation at every presented source. They first construct `NativeTransfer W` through the native column adapter, then invoke the checked selector. The generic monoid core retains its own source-local contract.
[Composition source](../Proofs/QMClosure/ConservativeCrossIncrementReadout.lean)

The complete column/bridge audit covers 57 actual origins, including private and generated declarations, with zero local axiom declarations and zero unsafe origins. Its aggregate transitive axioms are `propext`, `Quot.sound` and `Classical.choice`. The generic core has zero prior project declaration dependencies. The native adapter uses only the transfer structure and equal-fourth-history interface from the older generator-readout module. The separate bridge uses the checked cross-increment selector and excludes the older polynomial, positive-selection and fixed-corner selector conclusions from its actual type/body dependencies.

## Finite-depth exact conservation

The following finite-depth results are accepted analytic statements awaiting Lean artifacts. Fix \(K\ge1\), require nonnegative readout on every forward word of length at most \(K\) from \(p\), and write

\[
\Delta_p=|W(ap)-W(bp)|.
\]

With exact conservation at every forward source, the sharp bound is

\[
\Delta_p\le r_KW(p),\qquad
r_{2m}=\frac1{2^m-1}\ (m\ge1),\qquad
r_{2m+1}=2^{-m}\ (m\ge0).
\]

Normalized attaining native controls at \(p=1\) are

\[
W=N+2^{-m}\operatorname{Im}z\quad(K=2m+1),
\qquad
W=\frac{2^mN-\operatorname{Re}z+\operatorname{Im}z}{2^m-1}
\quad(K=2m).
\]

Their required positivity extends through depth \(K\). Positivity at later depths is a separate condition.

If conservation is supplied only at depths strictly below \(K\), the sharp constants become

\[
\widetilde r_1=1,\qquad
\widetilde r_{2m}=2^{1-m}\ (m\ge1),\qquad
\widetilde r_{2m+1}=\frac1{2^m-1}\ (m\ge1).
\]

Terminal mass concentrated in one residue class modulo four, with values above it determined by recursive summation, attains the finite-only bound. For \(K\ge3\), one additional conservation layer forces terminal parity \(v_0+v_2=v_1+v_3\) and recovers the global-conservation bound. The depth-two case requires its separate missing-residue treatment. Its argument must retain the actual available positivity constraints.

## Uniform relative conservation error

The relative branch estimate is a checked conditional theorem. Its contract uses a commutative monoid with \(a^4=b^4\), a real readout \(W\), and a source family \(S\) closed under multiplication by each generator. For every \(q\in S\), require nonnegativity and the uniform relative defect bound

\[
|W(aq)+W(bq)-W(q)|\le\varepsilon W(q).
\]

Assume \(\varepsilon\ge0\) and \(\eta=2\varepsilon+\varepsilon^2<1\), and set \(R=2\eta/(1-\eta)\). For every \(p\in S\), the checked estimate is

\[
\Delta_p\le
\left[R(1+\varepsilon)^4+(1+\varepsilon)^4-(1+\varepsilon)\right]W(p).
\]

In particular, \(\Delta_p\le9\varepsilon W(p)\) for
\(0\le\varepsilon\le1/20\). The order in \(\varepsilon\) has a matching control,

\[
W(p)=N(p)+\tau\operatorname{Im}(z^2),\qquad
\tau=\frac\varepsilon{1+\varepsilon}.
\]

This control is globally nonnegative, faithful and unit-normalized for \(\varepsilon\ge0\), has column sum \(N(p)\), satisfies the relative defect bound, and has imbalance \(\tau\) at the unit source. For \(0\le\varepsilon\le1\), its imbalance is at least \(\varepsilon/2\). The numerical upper coefficient is an available estimate. Sharpness concerns the linear order. The source-family contract includes arbitrarily long finite forward words.
[Checked branch estimates](../Proofs/QMClosure/ColumnConservationRobustness.lean) · [Checked native controls](../Proofs/QMClosure/ColumnConservationRobustnessControls.lean)

## Uniform absolute conservation error

Use the same commutative-monoid, equal-fourth-power, real-readout and forward-closed source-family contract. For every \(q\in S\), require nonnegativity and

\[
|W(aq)+W(bq)-W(q)|\le e\qquad(e\ge0).
\]

For every \(p\in S\) and every natural \(n\), the checked conditional estimate is

\[
\Delta_p\le\frac{W(p)+7e}{2^n}+20e\,2^n+2e.
\]

For unit \(W(p)=1\), optimizing the integer depth gives an accepted analytic upper bound of order \(\sqrt e\) as \(e\) tends to zero. This corollary has its own `analyticAwaitingFormalization` record, `positive_column_absolute_defect_sqrt_upper`, with review `notYetKernelChecked` and empty checked evidence.

The checked clipped native control

\[
W_\delta(p)=\max\{N(p)+\delta\operatorname{Im}z,0\},
\qquad0<\delta\le1,
\]

is nonnegative and unit-normalized, has imbalance \(\delta\), and has column defect between zero and \(\delta^2/4\) at every source. The checked positive-part defect bound gives the defect estimate, and the squared imbalance equals \(4(\delta^2/4)\). This supplies the square-root lower order. Sharp upper constants remain a separate question.
[Checked every-depth estimate](../Proofs/QMClosure/ColumnConservationRobustness.lean) · [Checked clipped control](../Proofs/QMClosure/ColumnConservationRobustnessControls.lean)

The three robustness modules have accepted registered Lean builds and independent final review. Their complete type/body audit covers all 98 actual origins, including private and generated declarations, with zero local axiom declarations and zero unsafe origins. Their aggregate transitive axioms are `propext`, `Quot.sound` and `Classical.choice`. The generic recurrence core and monoid adapter have zero prior project declaration dependencies. The control module uses the existing faithful native complex model. The optimized integer-depth square-root upper corollary remains a separate formalization obligation.
[Checked recurrence core](../Proofs/QMClosure/ColumnConservationRobustnessCore.lean) · [Authoritative task records and exact declarations](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Branch stability and global norm drift

The relative estimate controls \(|W(ap)-W(bp)|\). Uniform approximation of \(W\) by \(N\) requires a further theorem. Two independently accepted analytic counterfamilies preserve exact branch equality and the mixed-sign selector's count-grid condition while allowing unbounded norm drift under arbitrarily small relative column error. Their artifacts remain planned with empty checked evidence.

For \(\delta>0\), put \(q=2+\delta\) and, with \(z=x+iy\), define

\[
W_\delta(z)=\frac{|x+y|^q+|x-y|^q}{2},\qquad
A(z)=|x|^q+|y|^q.
\]

This readout is globally nonnegative and faithful, with unit value one and both generator values \(1/2\). Both branch readings equal \(A(z)/2\). Its original-count response is \((n^q+m^q)/2\), with zero mixed increments and coordinatewise monotonicity. The inequalities

\[
2^{-\delta}W_\delta(z)\le A(z)\le W_\delta(z)
\]

give a uniform relative column-error bound \(\varepsilon=1-2^{-\delta}\) tending to zero. At positive integer sources,

\[
\frac{W_\delta(n)}{n^2}=n^\delta,
\]

which is unbounded.

The stronger finite-window control fixes any \(T\ge2\) and sets

\[
H_T(0)=0,\qquad
H_T(t)=t^2\max\{\log(|t|/T),0\}\quad(t\ne0),
\]

\[
g(t)=t^2+\delta H_T(t),\qquad
W(z)=\frac{g(x+y)+g(x-y)}2\quad(\delta>0).
\]

It is globally nonnegative and faithful, unit-normalized, calibrated to \(1/2\) at both generators, exactly branch-balanced, and monotone on original counts with zero mixed increments. It agrees exactly with \(N\) on the entire window

\[
|x+y|\le T,\qquad |x-y|\le T.
\]

Any bounded calibration window fits inside such a window after choosing \(T\). In particular \(W(2)=4\). Each native generator preserves the whole box \(|x+y|\le T\), \(|x-y|\le T\). The control therefore agrees with \(N\) throughout the entire serial closure of this bounded preparation region, including every serial descendant of the unit.

Write \(A_H=H_T(x)+H_T(y)\) and
\(W_H=[H_T(x+y)+H_T(x-y)]/2\). The accepted analytic entropy estimate gives

\[
|A_H-W_H|\le(\log2)N\le(\log2)W.
\]

The relative column defect is therefore at most \(\delta\log2\) everywhere, while for positive integers \(n>T\),

\[
\frac{W(n)}{n^2}=1+\delta\log(n/T),
\]

which is again unbounded. Bounded calibration data, including exact scalar-two calibration and all serial unit descendants, leave this global drift available.

Both families lose the exact all-input law \(W(2p)=4W(p)\). The separate analytic repair below adds that law and exact vanishing mixed increments. Robust selection from only one global or eventual mixed-increment sign remains open.

## Analytic repair with exact all-input scaling

The parent-accepted analytic repair has the following full native contract,

\[
\begin{gathered}
W\ge0,\qquad W(1)=1,\qquad
\forall p,\ W(2p)=4W(p),\\
\forall n,m\in\mathbb N,\ d(n,m)=0,\\
\forall p,\ |W(ap)+W(bp)-W(p)|\le\varepsilon W(p),\qquad
0\le\varepsilon\le1/1000.
\end{gathered}
\]

It gives the full-carrier bound

\[
\forall p,\qquad
|W(p)-N(p)|\le100\varepsilon N(p).
\]

The constant is unoptimized. Exact zero mixed increments is the supplied count-grid premise. The one-sign robust version remains an independent question. Exact all-input scaling retains its operational role.

The analytic route sets \(\eta=2\varepsilon+\varepsilon^2\), \(d_*=2\eta\), and compares all four phases with factor \((1+d_*)/(1-d_*)\). Auxiliary reflection averaging produces a separable scalar comparison with an even real-axis function. The effective scalar parallelogram error is

\[
\delta_*=d_*+(1+d_*)\varepsilon
=5\varepsilon+6\varepsilon^2+2\varepsilon^3.
\]

Finite dyadic-denominator induction and a three-quarter contraction give scalar error coefficient \(\tau=16\delta_* /(1-2\delta_*)\). With

\[
\alpha=\frac{(1-d_*)^2}{1+d_*},\qquad
\beta=\frac{(1+d_*)^2}{1-d_*},
\]

the full comparison is \(\alpha(1-\tau)N\le W\le\beta(1+\tau)N\), yielding the stated coefficient 100. These are accepted analytic conclusions awaiting `DyadicScaledColumnStability.lean`, its complete checks and final review. The proof route uses dyadic finite induction and auxiliary averaging. Its supplied premise list is exactly the displayed native contract.

## Scientific boundary

The exact-column, composition, relative-error and every-natural-depth absolute-error bounds have accepted checked artifacts and independent final review, together with the cited controls. The finite-depth, optimized square-root upper, norm-drift and dyadic stability statements retain analytic task records with their respective formalization obligations. The robustness theorems bound first-branch imbalance under their full source-family contracts. Approximate norm selection, physical interpretation and QM closure retain independent obligations.

The result reduces the native readout premise to normalized positive column conservation on unlimited forward histories. Physical availability of that serial family, detector interpretation, conservation and positivity origins, the cross-increment sign, echo accessibility, Born/Hilbert origin, full QM/GR closure and physical scales remain open obligations under the existing public boundary.
