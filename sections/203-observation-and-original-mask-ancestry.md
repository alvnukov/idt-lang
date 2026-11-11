# Observation rules and original-mask ancestry

A short polynomial controller can use aggregate coordinates and an observation
rule to produce a nonquadratic native readout. Finite original-mask ancestry
adds a different condition on the complete dependence of each reported
contribution on individual original inputs. With a separately supplied
all-mask readout agreement, that condition yields the finite-order kernel
used by the original-occurrence selector.

The observation-controller, original-mask, circuit-ancestry and low-order
resource results below have registered and audited Lean artifacts under their
supplied mathematical contracts. Relaxation has checked pointwise convergence,
while its uniform absolute-output convergence extension remains analytic.
The asymptotic, common-output C1 and branch-specific-output obligations retain
analytic status and empty checked evidence.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Three supplied observation mechanisms

Write \(z=x+iy\), \(N=x^2+y^2\), \(H=\operatorname{Im}(z^4)\), and
\(Q=H^2/N^3\), with \(Q(0)=0\). The native generators attenuate the
squared norm by one half. Three controller constructions examine which
additional observation contracts preserve the regularity needed for norm
selection.

- Polynomial relaxation \(q'=H^2-N^3q\), initialized to zero, has trajectory
  \(q(z,t)=Q(z)(1-e^{-N(z)^3t})\). Native transfer rescales time,
  \(q(gz,t)=q(z,t/8)/2\) for \(g=a,b\). For \(q\) itself, a positive common
  observation time gives a transfer defect whenever \(H\ne0\). The output
  \(N+cq\) inherits that defect for \(c>0\). Equilibrium gives the regular
  family \(F_c=N+cQ\). Uniform absolute-output convergence is an analytic result
  awaiting its artifact. A positive-threshold timer has time \(\tau/N^3\)
  away from vacuum and diverges near vacuum. Its stopped readout has regular
  parameter \(c(1-e^{-\tau})\). At vacuum it needs a separate output convention.
- For the polynomial flow \((q,r)=(x^2t,t)\), set
  \(A=16y^2(x^2-y^2)^2\) and use the guard \(N^3r-A=0\). Its least
  nonnegative hit occurs at \(T=A/N^3\), with the vacuum value zero and
  \(0\le T\le16\). Terminal output is \(N+cQ\). Immediate hits are included,
  and the guard's time slope \(N^3\) degenerates at vacuum.
- Put
  \[
  m=\min\{x^2,y^2,(x+y)^2/2,(x-y)^2/2\},\qquad R_c=N+cm.
  \]
  One register \(q=(1+N)t\) and four polynomial guards
  \(q-(1+N)-Q_j=0\) give the earliest hit
  \[
  T=1+\frac{m}{1+N}\in[1,3/2).
  \]
  Every guard starts strictly negative and has time slope \(1+N\ge1\).
  All four tie at vacuum at time one. The output
  \(N+c(q-(1+N))\) equals \(R_c\) at every active branch's first hit.
  For \(c\ge0\) this response is faithful. It is continuous and has native
  half transfer and real-axis square calibration for every real \(c\).
  For \(c>0\), its raw third-order-interference defect
  at \((1,1,i)\) and its mixer-conservation defect at \((1,2)\) both equal
  \(c/2\).

Aggregate coordinates, ideal real registers and time, exact event detection,
and interpretation of the analog output are supplied. The competing-guard
construction leaves regularity of the complete stopping and selection
operation as an additional obligation. Claims of \(C^1\), \(C^2\), a common
quadratic vacuum expansion, and a physical detector realization each require
their own hypotheses and artifacts.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

Two further research obligations remain analytic and await Lean artifacts. With
finitely many C2 branch times coinciding at the origin and one common C2
scalar output, the proposed mechanism result requires the complete response
to be C1 throughout a neighborhood. Exact local dyadic scaling and
quarter-turn symmetry then select a multiple of the squared norm. Nonzero
local real-axis calibration fixes the multiple. A paired countermodel changes
the common-output premise to branch-specific polynomial outputs. Its
sixteen transverse rational guards produce a globally C1,1, strongly convex
native response in one first-event stage, with nonzero interference and
mixer defects. This records the role of the common output contract even
under strong response regularity. Ambient transfer laws, persistent first-hit
branches, aggregate preparation, exact detection and physical interpretation
retain their explicit bridges.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Frozen dependence on individual original masks

For each tagged original universe
\(U=\operatorname{Fin}(n)\sqcup\operatorname{Fin}(m)\), supply a finite
output set \(E\), supports \(A_e\subseteq U\), and real functions \(f_e\).
All are fixed while the retained mask \(S\subseteq U\) varies. Supply one
finite \(K\) uniform over every universe and require

\[
|A_e|\le K,\qquad
g_U(S)=\sum_{e\in E}f_e(S\cap A_e)
       =W(\operatorname{bag}(S))\quad\text{for every }S\subseteq U.
\]

The same \(W\) reads the coherent bag of retained original occurrences.
Boolean Möbius inversion then makes every coefficient on a subset larger
than \(K\) vanish. The all-mask agreement makes the remaining coefficients
depend only on the subset's two label counts, giving one fixed finite-order
kernel \(\kappa\). Conversely, a compatible original-subset kernel supplies
such a frozen local apparatus. Together with native calibration and transfers,
this conditional characterization feeds the existing carrier-wide norm
selector. The physical meaning of masks and the all-mask agreement are
supplied bridges.
[Original-occurrence selector](202-original-ab-occurrence-readout.md)
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

A complete finite circuit can supply the support bound. Its inputs are
individual original mask bits and mask-independent constants. Nodes are
indexed in one finite ranked acyclic graph, with arbitrary total real gate
functions and shared nodes allowed. Fanin at most \(r\ge1\) and depth at
most \(D\) give support at most \(r^D\) for each terminal contribution.
The arbitrary-fanin wrapper uses \(\max(1,r)^D\).
Every dependency affecting that contribution belongs in its circuit,
including input aggregation, event presence, control, stopping, normalization,
and output selection. The final additive collector is explicitly exempt
from the fanin/depth bound, and its terminal count is unrestricted.

The circuit supplies finite ancestry. Same-\(W\) all-mask retained-bag
calibration remains an independent premise. The nonnegative order-two norm
witness uses singleton contributions \(1/2\) and same-type pair contributions
one. A single empty-support constant can reproduce any chosen full-mask
value, showing how little that single calibration determines. The positive
regular family requires unbounded support across universes under all-mask
agreement. Physical shutter/preparation realization and interpretation of
the additive collector remain supplied.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## An independent low-order resource wall

Only the empty, singleton, and same-type-pair masks are needed for a separate
coverage argument. Their native readouts are respectively \(0,1/2,2\), so
the pair finite difference is one. Each same-type pair must therefore occur
together in some fixed support. Writing \(a_e,b_e\) for the two support
populations gives

\[
{n\choose2}+{m\choose2}
\le\sum_{e\in E}\left({a_e\choose2}+{b_e\choose2}\right)
\le |E|{K\choose2}.
\]

At order zero every frozen local contribution is constant across masks.
The native empty and singleton readings already exclude that case in every
nonempty original universe.

If every original input participates in at most \(M\) output contributions,
each nonempty type population is at most \(1+M(K-1)\). The argument allows
arbitrary real contribution magnitudes. Its premises involve only these
low-order mask readings. A circuit fanout bound supplies an incidence bound
only after endpoint copies, repeated terminal references, and output ports
are accounted for.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## The next analytic robustness question

Fix finite \(K\) and a readout \(W\) satisfying native normalization
\(W(a)+W(b)=1\) and the universal generator transfers
\(W(ap)=W(a)W(p)\), \(W(bp)=W(b)W(p)\) for every \(p\).
For every finite base universe \(U\), suppose one sequence
of frozen \(K\)-local apparatuses acts on \(2^k\) copies of its original
tokens. At each \(k\), that single apparatus serves every base mask
simultaneously. Let \(\operatorname{inflate}_k(S)\) retain all copies of
exactly the tokens in \(S\). The proposed sufficient fidelity condition is

\[
\frac{g_k(\operatorname{inflate}_k(S))
 -W(2^k\operatorname{bag}(S))}{4^k}\longrightarrow0
\quad\text{for every }S\subseteq U.
\]

Native dyadic growth, restriction to copied blocks, and a finite Möbius-sum
limit would then make the base readout's coefficients above order \(K\)
vanish. The existing kernel and norm-selection route would apply. A uniform
raw error ceiling \(C(L+1)^p\), with fixed \(C\ge0\), token count \(L\), and
\(0\le p<2\), is sufficient for this analytic argument. A quadratic ceiling
with an arbitrarily small positive coefficient is insufficient. The regular
family \(F_c\) and the norm apparatus have raw discrepancy at most
\(cL^2/2\).

More quantitatively, if a base subset \(T\) has nonzero Möbius coefficient
\(\mu_UW(T)\) and \(|T|>K\), every such replicated \(K\)-local apparatus
has some base-mask error of magnitude at least

\[
\frac{4^k|\mu_UW(T)|}{2^{|T|}}.
\]

For the regular family with \(c>0\), the analytic proposal gives an
existential finite witness for each \(K\). No witness-size bound uniform
in \(K\), or positive lower bound uniform in \(K\) and \(c\), is asserted.

An exact mask-independent affine calibration with nonzero gain can be
normalized. For approximate gain \(\lambda_k\), the required error scale is
\(|\lambda_k|4^k\). Nonzero gain alone is insufficient, as the choices
\(g_k=0\), \(\lambda_k=2^{-k}\) illustrate. With probability normalization
\(|\lambda_k|\) of order \(4^{-k}\), the raw calibrated error itself must
tend to zero. Mask-dependent gain evades the fixed calibration contract even
when the apparatus is entirely frozen. A frozen norm apparatus can match
\(F_c\) through a mask-dependent ratio. Per-mask retuning evades the frozen
simultaneous-apparatus premise.

This extension awaits its Lean source. Raw fidelity, replicated preparation,
finite ancestry, and their physical meanings remain assumed. Physical
readout origin, detector actualization, Born interpretation, Hilbert
reconstruction, full QM closure, and physical scales remain open.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
