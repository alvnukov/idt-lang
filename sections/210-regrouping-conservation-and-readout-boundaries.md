# Regrouping conservation and readout boundaries

An arbitrary semiring with exact `a+b=1` and `a^4=b^4` supports a conditional readout route from two supplied conservation columns. Define `T=a²+b²` and `c=2ab`. For a real response `W` and one preparation-independent real gain `k`, supply all of the following laws for every right preparation `p`. [Regrouping contract](../Proofs/QMClosure/RegroupingGainSelection.lean)

\[
\begin{aligned}
W(1)&=1, & W(2)&\ne2,\\
W(ap)+W(bp)&=W(p), & W(2p)&=kW(p),\\
W(Tp)+W(cp)&=W(p).
\end{aligned}
\]

Pair commutation follows from the two coefficient identities. The displayed contract keeps the second column, fixed gain and contrast as independent supplied inputs. Its semiring argument uses real readout arithmetic without a zero-detection, positivity, continuity, multiplicativity or additive-cancellation premise. [Pure coefficient identities](../Proofs/QMClosure/FourthRejoinIdempotentCore.lean) · [Explicit-hypothesis adapter](../Proofs/QMClosure/RegroupingGainSelection.lean)

## Readout consequences

Using the two coefficient identities, the first column, fixed gain, unit and contrast give `W(Tp)=0` for every `p`. The second column then gives `W(cp)=W(p)`. Together they yield both global half laws and `k=4`.

\[
W(ap)=W(bp)=\frac{W(p)}2,\qquad W(2p)=4W(p).
\]

These conclusions concern readout values in all right contexts. Carrier equalities `T=0` and `c=1`, factorization through a destructive quotient, and uniqueness of a norm require additional arguments. The controls below exhibit the corresponding boundaries. [Null contexts, readout transparency and gain selection](../Proofs/QMClosure/RegroupingGainSelection.lean)

## A continuous response with a surviving sector

Use the supplied carrier

\[
S=\{(0,0)\}\cup\{(z,q)\in\mathbb C\times\mathbb R:q>0\}
\]

with its inherited topology and standard coefficients `a=((1+i)/2,1/2)` and `b=((1-i)/2,1/2)`. Set `N(z)=|z|²`, `W(0)=0`, and

\[
W(z,q)=N(z)\left[1+\frac12\sin\left(\frac{2\pi\log q}{\log2}\right)\right]
\]

on the nonzero part of the carrier. The response is nonnegative, normalized and continuous, including the origin, with `W(z,q)≤(3/2)N(z)`. It satisfies both global half laws, both columns and fixed gain four. The carrier still has `T≠0` and `c≠1`, with a nonzero readout-null sector `e`. [Concrete response and continuity](../Proofs/QMClosure/RegroupingNullContextControls.lean)

The strict witness `W(1+T)<W(1)` gives a universal factorization exclusion. For every semiring homomorphism `f:S→R` satisfying `f(e)=0`, every function `V:R→Real` fails the identity `W=V∘f`. Thus nullity in every `T` context leaves an additional readout-descent obligation. Continuity on this carrier and extension to an ambient completion are separate conditions. The proposed continuous-extension obstruction at the missing ambient point `(1,0)` remains analytic and unformalized. Its separate ledger task has empty checked evidence. [Factorization exclusion](../Proofs/QMClosure/RegroupingNullContextControls.lean)

## Two omission controls

The two supplied operational laws have separate controls.

| Supplied law under examination | Concrete response | Established boundary |
|---|---|---|
| Second conservation column | `W8(z,q)=N(z)²/q` on the same positive-second-coordinate carrier, with value zero at the origin | Unit, nonnegativity, multiplicativity, half laws, first column, contrast and fixed gain eight coexist with failure of the second column at the unit preparation |
| One fixed global gain | `theta*N(z)+(1-theta)*abs(q)` on `C×R`, with `0<theta<1` | Both columns, unit, nonnegativity, global zero detection, unit contrast and `T≠0` coexist with absence of any one global duplication gain |

For the gain-eight response, `W8(Tp)=0` but `W8(c)=2`. Its source carries no origin-continuity assertion. The mixed-weight second-column identity holds for every real `theta`; its aggregate omission control specializes to `0<theta<1` and reuses the existing mixed-weight theorem. The aggregate source statement carries no continuity assertion. [Gain-eight and mixed-weight adapters](../Proofs/QMClosure/RegroupingNullContextControls.lean)

## Analytic continuations remain separate

A proposed family on the intended exact normal-form carrier uses

\[
W_\alpha(z,q)=N(z)^\alpha q^{1-\alpha},\qquad 0<\alpha\le1,
\]

with value zero at the origin. The analytic obligations include continuity, multiplicativity, half laws, gain `2^(1+alpha)` and the null ideal `eP`. For `0<alpha<1`, the proposed witness `Walpha(1+e)=2^(1-alpha)≠1` separates null-ideal closure from quotient descent. These obligations retain empty checked evidence. [Power-response obligations](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The exact initial normal form and the `e=1` classical quotient now have kernel-checked artifacts. A separate calibrated criterion combines serial `c` transparency, `W(T)=W(0)` and one global fixed-`T` inequality to prove null insertion and unique set-function descent through the destructive quotient. General positive-power rejoining, higher-cyclotomic families and faithful arbitrary-target generated conjugation keep their existing analytic status. [Normal form and calibrated descent](211-initial-normal-form-and-null-passivity.md) · [Finite-cycle and conjugation boundaries](208-finite-cycle-degree-and-physical-origin-boundaries.md)

The physical origins of the second column, fixed gain, contrast, grammar and exact relators remain open. Readout actualization, Hilbert reconstruction, full QM, GR and physical-scale closure retain their independent obligations. [Physical scope boundary](150-physical-scope-boundary.md)
