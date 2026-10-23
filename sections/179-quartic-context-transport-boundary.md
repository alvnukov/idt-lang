# Separable quartic coordinates, local contexts, and the coherent-merge boundary

## Result and scope

`Proofs/QMClosure/QuarticContextTransport.lean` constructs a separable quartic
coordinate description by transporting supplied real quadratic geometry. It
includes finite joint probabilities, commuting local actions, and independent
product preparations and actions. Its purpose is to test whether continuity,
reversibility, product factorization, and no-signalling alone select a quadratic
**coordinate formula**. They do not: those requirements leave the operational
coherent-history merge unspecified.

This is not an inequivalent quartic physical theory, an IDT-native derivation of
the real carrier or available orthogonal operations, a classification of all
response functions, or a completed derivation of QM. There is no claim that real
and integer native domains are interchangeable. All continuity statements below
mean continuity only; smoothness or local Lipschitz behavior at coordinate nodes
is not asserted.

## Explicit transport

For real coordinates define

\[
\phi(x)=x|x|,\qquad
\psi(y)=\sqrt y-\sqrt{-y},\qquad
Q_4(x)=\sum_i x_i^4.
\]

Here square root uses Lean's totalized convention, mathematically
\(\sqrt{\max(y,0)}\), so it is zero on negative arguments.
Lean proves both scalar inverse identities, continuity of both maps,
\(\phi(xy)=\phi(x)\phi(y)\), and \(\phi(x)^2=x^4\). Entrywise encoding
\(\Phi\) therefore satisfies \(\sum_i\Phi(x)_i^2=Q_4(x)\).

Given a supplied map \(U\), define

\[
F_U(x)=\Psi(U\Phi(x)).
\]

The module proves universal transport statements: continuity transfers from
\(U\), a supplied inverse transfers to an inverse, and preservation of the
sum of squares transfers to preservation of \(Q_4\). These hypotheses are
explicit, not derived from IDT primitives.

They are nonvacuous. The module proves a continuous reversible two-dimensional
rotation family and its quartic conservation, and supplies the genuine mixing
matrix

\[
U=\begin{pmatrix}3/5&-4/5\\4/5&3/5\end{pmatrix}
\]

with verified square preservation and an explicit inverse. For the basis vectors
\(u=(1,0)\), \(v=(0,1)\), let \(r=\sqrt{3/5}\),
\(s=\sqrt{4/5}\). Then \(F_Uu=(r,s)\) and \(F_Uv=(-s,r)\).
The Lean witness establishes

\[
Q_4(u+v)=2,\qquad Q_4(F_Uu+F_Uv)=194/25.
\]

Since \(F_U\) conserves \(Q_4\), it cannot preserve ordinary vector addition.

## Finite joint tables

For a real table \(T_{ij}\), the local actions are

\[
F_R(T)_{ij}=\psi\!\left(\sum_k R_{jk}\phi(T_{ik})\right),\qquad
F_L(T)_{ij}=\psi\!\left(\sum_k L_{ik}\phi(T_{kj})\right).
\]

Together these represent \(\Psi(L\Phi(T)R^\mathsf T)\). The module proves
that the two actions commute for arbitrary finite real coefficient matrices.
It proves continuity and inverse transfer for both action families, with concrete
inverse witnesses for the mixing matrix above.

For square-preserving \(R\), every row's quartic mass is invariant; for
square-preserving \(L\), every column's quartic mass is invariant. Hence the total
quartic mass is invariant. For a nonzero table with
\(Z=\sum_{ij}T_{ij}^4>0\), define the normalized readout

\[
p_{ij}=T_{ij}^4/Z.
\]

Lean proves nonnegativity, normalization, invariance of the row marginal under
the right action, and invariance of the column marginal under the left action.
This is no-signalling for the **declared local-operation and readout family**,
not for arbitrary enlarged operations. Algebraic marginal identities also hold
at zero because of Lean's totalized division, but zero is not a normalized
physical state; the packaged no-signalling statement explicitly requires
\(Z>0\).

For rank-one preparations \(T_{ij}=a_i b_j\), both the probabilities and the
actions factor. In particular,

\[
F_LF_R(a\otimes b)=F_L(a)\otimes F_R(b).
\]

These are distinct proved results: probability factorization alone would not
establish independent product dynamics.

## Exactly what remains missing

Transporting coherent merge as

\[
x\mathbin\oplus y=\Psi(\Phi(x)+\Phi(y))
\]

makes transported linear maps preserve that merge. Lean proves the corresponding
universal compatibility theorem. With this merge and correspondingly transported
observables, the construction is isomorphic to its supplied quadratic
description; it supplies no new physical predictions.

Keeping ordinary addition instead gives a different merge law. The scalar
equal-history witness has third-order residual
\(3^4-3\,2^4+3\,1^4=36\), proved in Lean, while the explicit transported mixing
map fails ordinary additivity. Thus this alternative cannot silently retain the
quadratic description's composition rule.

The missing operational requirement is that an independently specified coherent
union of disjoint histories commute with a remote context action. If that union
is ordinary vector addition, and the compatibility requirement applies to all
vectors through an adequate disjoint-history realization/accessibility bridge,
it forces additivity. Together with continuity, additivity would force real
linearity; the existing `LinearMixingCoordinateBoundary.lean` then excludes a
genuinely mixing real linear quartic-preserving map. The continuity-to-linearity
extension and the operational realization/compatibility bridges are explicitly
listed as pending in this module, not claimed as proved here.

In particular, a detector-output row merge is **not** assumed to be an accessible
deterministic coherent channel. No operational signalling experiment follows
from this construction alone. Classical probabilistic coarse-graining and
coherent history union must remain distinct.

## Evidence and prior context

The Lean module is included in the default `Proofs` target. Its local
`openBridges` and `paperOnlyOrOpen` lists make the remaining operational and
formalization boundaries machine-visible. No manifest proof status is upgraded.

The conceptual issue of nonlinear descriptions requiring correspondingly
transported observables has prior literature: Nattermann (1997),
[sections V–VI](https://arxiv.org/html/quant-ph/9703017v1). That reference supplies
conceptual context, not a proof of this specific finite quartic construction.
No novelty claim is made.
