# Local cross-increment readout selection

## Current status

The checked conditional result reduces a native readout-selection premise to one four-count increment sign, translated over every natural background. The generic grid, native selector and control modules have passed registered Lean builds and a complete actual-origin/type/body dependency audit, with independent acceptance. The two proposed research records have stage `conditionalKernelTheorem`, review `parentAccepted` and exact checked declaration citations. Their hypotheses retain their supplied mathematical and operational scope.
[Generic source](../Proofs/QMClosure/CountCrossIncrementRigidity.lean)
[Native selector](../Proofs/QMClosure/NativeCrossIncrementReadoutSelection.lean)
[Control source](../Proofs/QMClosure/NativeCrossIncrementReadoutControls.lean)

## The sign contract

Use the existing presented-history algebra with its native generators `a,b`. Supply `NativeTransfer W` for a real-valued readout `W`, meaning

\[
W(1)=1,\qquad W(ap)=W(p)/2,\qquad W(bp)=W(p)/2
\quad\text{for every presented history }p.
\]

Define the count response and its mixed increment by

\[
\begin{aligned}
f(n,m)&=W(na+mb),\\
d(n,m)&=f(n+1,m+1)-f(n+1,m)-f(n,m+1)+f(n,m).
\end{aligned}
\]

Either of the following single sign conditions suffices for the norm readout,

\[
(\forall n,m\in\mathbb N,\ d(n,m)\ge0)
\quad\text{or}\quad
(\forall n,m\in\mathbb N,\ d(n,m)\le0).
\]

The checked conclusion is

\[
W(p)=\operatorname{normSq}(\operatorname{complexEval}(p))
\quad\text{for every presented history }p.
\]

The sign condition can be weakened to one eventual uniform sign,

\[
(\exists D\in\mathbb N\ \forall n,m,\ n+m>D\Rightarrow d(n,m)\ge0)
\quad\text{or}\quad
(\exists D\in\mathbb N\ \forall n,m,\ n+m>D\Rightarrow d(n,m)\le0).
\]

The threshold is uniform over all backgrounds with sufficiently large total count. A row-dependent threshold requires a separate theorem. The four-point stencil is translated over every background. Finitely many measured stencils supply finite checks of that quantified premise.

The supplied native algebra and all-history half-transfer laws carry the structural input. The additional sign premise requires no readout positivity, reflection, continuity, polynomiality, canonical coefficient positivity, finite support cutoff or event-atom representation.

## Why the increments vanish

Native transfer gives, for every natural `N`,

\[
f(N,N)=W(N),\qquad
f(N,0)=f(0,N)=W(N)/2,\qquad f(0,0)=0.
\]

These identities precede the quadratic count formula. Rectangular telescoping therefore gives the saturated square identity

\[
\sum_{n<N}\sum_{m<N}d(n,m)
=f(N,N)-f(N,0)-f(0,N)+f(0,0)=0.
\]

If every summand has one sign, every cell in that square is zero. Taking arbitrarily large squares yields `d=0` everywhere. The response separates as `f(n,m)=g(n)+g(m)` with `g(n)=W(n)/2`.

The subtraction-free native bag identity

\[
\operatorname{bagEval}(k+2,k)
=(2a)\operatorname{bagEval}(1,k+1)
\]

then gives

\[
g(k+2)+g(k)=2g(k+1)+1,\qquad g(0)=0,\quad g(1)=1/2.
\]

Finite induction gives `g(n)=n²/2` and hence `f(n,m)=(n²+m²)/2`. The checked whole-carrier argument transports this count formula through quarter-turn cone transport and dyadic normal forms. It also constructs compatible original-subset pair-kernel data as a separate derived conclusion.

The source imports `OriginalOccurrenceNormSelection` for existing algebra and transport interfaces. Its actual whole-carrier dependencies use the count formula, cone transport and half-normal-form arithmetic. The accepted transitive type/body profile excludes the older finite-kernel polynomial selectors, positive-selection conclusions and fixed-corner pair-law selector from the final native norm route. The generic grid profile has no prior project declaration dependencies. The complete origin audit covered 93 declarations, including generated and private origins, with zero local axiom declarations and zero unsafe origins. Its aggregate transitive axioms are `propext`, `Quot.sound` and `Classical.choice`.
[Generic source](../Proofs/QMClosure/CountCrossIncrementRigidity.lean)
[Native selector](../Proofs/QMClosure/NativeCrossIncrementReadoutSelection.lean)

## Eventual signs and persistent counterincrements

Native count doubling gives `f(2n,2m)=4f(n,m)`. The mixed increments therefore satisfy

\[
\sum_{i,j\in\{0,1\}}d(2n+i,2m+j)=4d(n,m).
\]

A positive parent has a child at least as positive, and a negative parent has a child at most as negative. Native transfer also gives `d(0,0)=0`. Every nonzero parent has positive total background count, so finite repetition sends a child beyond every total-count threshold while preserving its signed magnitude. This makes an eventual uniform sign sufficient to eliminate every increment of the opposite sign. Square saturation then gives `d=0`.

Conversely, under the supplied native transfer contract, every readout that differs from the norm has both increment signs arbitrarily far out with one fixed positive magnitude,

\[
\exists\varepsilon>0\ \forall D\in\mathbb N\ \exists n,m,r,s,
\quad n+m>D,\quad r+s>D,\quad
d(n,m)\ge\varepsilon,\quad d(r,s)\le-\varepsilon.
\]

The sign witnesses may occur at different backgrounds for each threshold. Fixed-ray or adjacent-cell alternation would need separate results.

## Comparison and countercontrols

### All-order canonical positivity

For a general count grid, nonnegative canonical coefficients at every order imply nonnegative mixed increments through the finite Newton transform. The OR grid

\[
f_{\mathrm{OR}}(n,m)
=\tfrac12\mathbf1_{\{n>0\}}+\tfrac12\mathbf1_{\{m>0\}}
\]

has zero mixed increments, coordinatewise monotonicity, zero vacuum and values `f(1,0)=f(0,1)=1/2`, `f(1,1)=1`. Its canonical axis coefficients are

\[
\kappa(j,0)=\tfrac12(-1)^{j+1}\qquad(j\ge1).
\]

This establishes strictness of the predicate comparison on unrestricted count grids. The OR grid fails native doubling, since `f(2,0)=1/2` whereas `4f(1,0)=2`. The comparison concerns positivity at every canonical order. Eventual canonical positivity with a signed head has a separate scope.

Thus the native selector can use the four-count sign contract in place of all-order positive-event data. Its theorem requires the given native transfer contract and the uniform sign premise.

### Ordinary monotonicity

The existing regular native family has count-coordinate extension

\[
F_c(x,y)=\frac{x^2+y^2}{2}
+8c\frac{x^2y^2(x^2-y^2)^2}{(x^2+y^2)^3},
\]

with zero vacuum value. For `0<c≤1/16`, its checked derivative certificate gives coordinatewise nondecreasing response on the entire nonnegative real quadrant. The proof treats positive denominators by calculus and handles the axes directly.

Its mixed increments include

\[
d(0,1)=288c/125>0,\qquad d(1,1)=-576c/125<0.
\]

This family satisfies native transfer and differs from the norm. Ordinary coordinatewise monotonicity therefore permits a native counterreadout. The countercontrol uses first-derivative certificates and direct axis formulas. Vacuum second-order regularity is outside the claim.

## Scientific boundary

The route supplies checked conditional assumption-reduction theorems and explicit controls. The physical origin of a uniform cross-increment sign remains open.

The native composition/cancellation relations and half-transfer laws retain their supplied algebraic and operational roles. Their physical realization, echo availability, any cloning interpretation, detector actualization, Born origin, Hilbert origin, full QM/GR closure and physical scales remain independent open obligations. The existing public claim boundary applies.
