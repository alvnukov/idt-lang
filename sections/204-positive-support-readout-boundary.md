# Positive support and the readout boundary

An unrestricted original-occurrence kernel can have coefficients at every
subset order. The positive-kernel theorem states that universal count
doubling and an eventually nonnegative coefficient tail force this kernel to
have order at most two. Three small calibrations then select the exact pair
kernel and, through the earlier native carrier extension, the squared-norm
readout. A frozen positive-event model supplies the coefficient condition on
the original tagged a,b preparation family.

The generic positive-kernel result and the original-event/native adapter have
registered Lean artifacts with accepted build and origin/dependency evidence
under their supplied contracts. The two stochastic-query tasks and the
support-resource extension remain analytic with empty checked evidence.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Unrestricted coefficients and exact duplication

Let \(\kappa_{jk}\in\mathbb R\) be defined for every pair of natural
indices and write

\[
F_\kappa(n,m)=\sum_{j=0}^{n}\sum_{k=0}^{m}
{n\choose j}{m\choose k}\kappa_{jk}.
\]

Every evaluation is a finite sum. Finite Newton inversion identifies a unique
signed kernel for each count response. The registered inversion artifact supplies
this unrestricted coefficient-uniqueness statement and the exact duplication
operator

\[
(D\kappa)_{jk}=
\sum_{r=0}^{j}\sum_{s=0}^{k}
{j\choose r}{k\choose s}
2^{j-r}2^{k-s}\kappa_{j+r,k+s}.
\]

The identity \(F_{D\kappa}(n,m)=F_\kappa(2n,2m)\), together with
inversion, makes universal doubling
\(F_\kappa(2n,2m)=4F_\kappa(n,m)\) imply \(D\kappa=4\kappa\).
Inversion and the duplication identity are checked results in the generic
artifact.
[Generic source](../Proofs/QMClosure/PositiveUnboundedKernelDuplication.lean)

For a nonnegative kernel, the \(r=s=0\) term gives
\(2^{j+k}\kappa_{jk}\le(D\kappa)_{jk}=4\kappa_{jk}\).
Every coefficient above total order two therefore vanishes. The weaker
condition

\[
\exists D\in\mathbb N\ \forall j,k\in\mathbb N,\qquad
D<j+k\ \Longrightarrow\ \kappa_{jk}\ge0
\]

also suffices. It first eliminates the high tail and then descends through
the finite signed head. This finite argument supplies the cutoff from the
coefficient condition and universal doubling. It uses finite differences,
binomial identities, positivity and finite descending induction.
[Generic source](../Proofs/QMClosure/PositiveUnboundedKernelDuplication.lean)

The calibrations
\(F(1,0)=F(0,1)=1/2\) and \(F(1,1)=1\) fix exactly

\[
\kappa_{10}=\kappa_{01}=\tfrac12,\qquad
\kappa_{20}=\kappa_{02}=1,
\]

with every other coefficient zero. The resulting count response is
\((n^2+m^2)/2\). The generic count argument has its own mathematical
contract. Native normalization and the two universal generator transfers
supply its doubling and calibration premises in the adapter.
[Generic source](../Proofs/QMClosure/PositiveUnboundedKernelDuplication.lean)
[Native adapter](../Proofs/QMClosure/NativePositiveSupportReadout.lean)

## What positive events supply

For each finite original a,b universe, supply a finite set of events, with a
fixed support \(T_e\) and fixed score \(w_e\ge0\) for every event. All
fields stay frozen as the retained mask \(S\) varies. An event occurs
exactly when \(T_e\subseteq S\), and its contribution is

\[
g(S)=\sum_{e:T_e\subseteq S}w_e.
\]

Require agreement on every mask with the same readout of the coherent bag of
retained original occurrences. The Boolean coefficient of an actual subset
\(T\) is then \(\sum_{e:T_e=T}w_e\ge0\). Conversely, one event per
subset realizes any nonnegative canonical coefficient family. Distinct event
identities may share a support and split its total weight. The unique object
is the canonical coefficient family. Event counts and support sizes can grow
with the universe. This characterizes a supplied
operational contract. The physical origins of frozen events, principal-support
activation, all-mask agreement and analog scores remain open.
[Event source](../Proofs/QMClosure/PersistentOriginalEventAtoms.lean)

The native adapter obtains the finite compatible pair kernel and explicitly
uses the earlier carrier-extension theorem. The initial history algebra,
local relators and native half-transfer laws remain supplied earlier
contracts. The argument leaves Born actualization, Hilbert origin, physical
detector realization and physical scales open.
[Native adapter](../Proofs/QMClosure/NativePositiveSupportReadout.lean)
[Earlier carrier extension](202-original-ab-occurrence-readout.md)

## Controls and the signed-cancellation wall

Positivity alone permits infinite support. The all-one kernel has response
\(2^{n+m}\) and fails doubling. A stronger control
\(\kappa^*=\kappa^{\mathrm{pair}}+\mathbf1_{\{j+k\ge3\}}\)
keeps the vacuum and all three small calibrations, but gives
\(F(2,0)=2\), \(F(4,0)=13\), violating doubling because \(13\ne8\).
[Generic source](../Proofs/QMClosure/PositiveUnboundedKernelDuplication.lean)

Any native readout differing from the norm has negative canonical
coefficients above every finite total-degree threshold. For the regular
family with \(c>0\), one explicit coefficient is
\(\kappa_{31}=-288c/125\). The principal-support trigger is substantive.
A monotone two-input OR event has pair Möbius coefficient \(-1\), despite
its positive score and persistent occurrence.
[Native adapter](../Proofs/QMClosure/NativePositiveSupportReadout.lean)
[Control source](../Proofs/QMClosure/NativePositiveSupportReadoutControls.lean)
[Event source](../Proofs/QMClosure/PersistentOriginalEventAtoms.lean)

Extending the same positive-atom model to arbitrary signed original
preparations meets a cancellation wall. Adding \(-a\) to a positive
\(a\) preparation gives zero, contradicting the model's inclusion
monotonicity. The native \(a,-a\) pair has Möbius coefficient \(-1\).
The positive-event characterization consequently applies to the original
tagged a,b family. A universal extension with these same fixed positive principal-support rules
conflicts with this signed-preparation control.
[Control source](../Proofs/QMClosure/NativePositiveSupportReadoutControls.lean)

## Analytic mechanism frontiers

A separate analytic question concerns one fixed iid-label query protocol,
almost-sure halting including vacuum, one bounded nonnegative normalized
output \(w\), and exact dyadic scaling of its expectation. Uniform second
query moments are insufficient. The accepted analytic countermodel has
\(\mathbb EQ\le10\), \(\mathbb EQ^2\le180\), rare long query tails,
a raw universe gain \(L^2\), and output variance growing with padded universe
size. Uniform integrability of \(wQ(Q-1)\), or a uniform
\((2+\delta)\)-moment bound near vacuum for some \(\delta>0\), suffices
for quadratic effective expected output within this protocol class.
A uniform conditional chance of stopping before each query, including the
first, bounded below by \(1-\rho>0\) for fixed \(0<\rho<1\), supplies
that uniform integrability with bounded normalized gain and finite internal
transitions. The exact expected dyadic and native laws remain assumptions.
Uncompensated added termination requires their verification.

Compensated independent kill coins preserve the nonquadratic expectation with
uniform exponential actual-query tails by allowing unbounded normalized gain.
With-replacement sampling presupposes replay or repeated label access. Two
observations may revisit the same original, and long traces remain permitted.
An actual-subset adapter needs singleton and distinct-pair contributions.
Physical echo availability remains an origin obligation, and the protocol
supplies no cloning conclusion. This sampling model covers original a,b preparations. Indexed-mask queries
and real aggregate oracles require separate contracts. Its
original-count response needs an explicit ambient native-gate adapter.
All these frontier statements remain analytic and await Lean artifacts.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The separate analytic resource extension makes a polynomial bound on
canonical absolute support variation equivalent to a finite cutoff over
unbounded balanced dyadic counts. Its principal-support atom score/count
budgets characterize that cutoff. Frozen ordinary events triggered by exact
count-table entries can give polynomial event and score budgets for a
nonquadratic regular readout. Such global count triggers have a different
activation contract. Canonical support variation concerns an explicit atom
expansion. Computational complexity requires its own resource model. This
extension and its signed-budget growth corollary remain analytic obligations.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The physical preparation, sampling, gain, event and readout bridges retain
independent obligations. Born/Hilbert origin, full QM closure, gravity and
physical-scale derivations remain open under the existing public boundary.
