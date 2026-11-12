# Eighth rejoin and local null-coalescence descent

The checked literal eighth-rejoin carrier supports distinct readouts satisfying the six all-depth word schemas. For each given response satisfying a separate five-premise local contract, there is a unique descended function on the fourth-rejoin carrier. Its exact zero-coalescence test concerns two fixed positive summands whose sum is one. [Local descent](../Proofs/QMClosure/EighthRejoinNullClosureDescent.lean) [Research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Carrier and concrete readouts

`P8` is the initial positive natural-coefficient algebra with exactly

\[
a+b=1,\qquad a^8=b^8.
\]

A generic checked theorem constructs positive two-sided inverse words and derives `ab=ba` from transparency and any two positive rejoin powers. On `P8`, induction over the generated syntax extends pair commutation to the whole carrier. The generic theorem also applies inside an arbitrary semiring, where its conclusion concerns the supplied pair. [Positive-power core](../Proofs/QMClosure/TransparentPositivePowerRejoin.lean) [Initial P8 presentation](../Proofs/QMClosure/EighthRejoinInitialPresentation.lean)

Three explicit complex evaluations descend through the two relators. Write `X=normSq(E2)` for the Gaussian evaluation and `Y=normSq(E1) normSq(E3)` for the quartic product evaluation. The checked responses are

\[
W(p)=\min(X(p),Y(p)),\qquad
V(p)=\begin{cases}0&Y(p)=0,\\X(p)&Y(p)\ne0.\end{cases}
\]

Set `h=ab`, `c=2ab`, `T=a²+b²`, `s=a⁴+b⁴`, `z=2a⁴+b⁴` and `B(n,m)=na+mb`. Both readouts satisfy `W(0)=V(0)=0`, `W(1)=V(1)=1`, nonnegativity, forward serial increase, natural-count order at every preparation, the all-depth word-grid formulas, raw word mixed zero at every depth and adjacent cell, and `T`-nullity. Both also satisfy the two global half laws, first-column conservation, generator-swap invariance and self-echo. The `V` certificate additionally gives exact serial `c` invariance, global multiplicativity, quadratic natural gain and mixed zero at every preparation. [Readout contracts and certificates](../Proofs/QMClosure/EighthRejoinReadoutCountermodels.lean)

The exact anchors expose the remaining boundary. At `s`, `W(s)=V(s)=0` while `X(s)=1/4`. Both readouts differ from `X` and fail factorization through fourth rejoin. On the literal source, `s≠0`, `T≠0` and `a⁴≠b⁴`. For `W`, the four count-cell values at preparation `z` are

| Counts | Response |
| --- | --- |
| `(4,1)` | `153/32` |
| `(4,0)` | `144/32` |
| `(3,1)` | `82/32` |
| `(3,0)` | `81/32` |

Their mixed difference is `1/4`, and `W(z)<W(cz)`. These are exact checked anchors. The concrete quotient evaluations establish their stated algebraic models. The number-field faithfulness and complete cyclotomic-family claims retain separate analytic tasks. [Concrete countermodel certificate](../Proofs/QMClosure/EighthRejoinReadoutCountermodels.lean) [Research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## The separate local contract

The descent module constructs natural-coefficient words `A=certificateA` and `B=certificateB` with

\[
TA+sB=(a+b)^9=1,\qquad sa^4=sb^4.
\]

For a real-valued response `R` on `P8`, `LocalCoalescenceContract` supplies exactly five premises.

1. `R(1)≠0`.
2. `R(T)=0`.
3. The single multiplication equality `R(TA)=R(T)R(A)`.
4. `R(sp)=R(s)R(p)` for every actual preparation `p`.
5. The single conditional implication `R(TA)=0 → R(sB)=0 → R(TA+sB)=0`.

Given `R(TA)=0` and `R(1)≠0`, the fifth premise excludes `R(sB)=0`. This supplies a separation test at the fixed certificate pair. The fourth premise still ranges over every actual preparation. Physical origins of these supplied tests remain open. [Local contract](../Proofs/QMClosure/EighthRejoinNullClosureDescent.lean)

The certificate forces `R(s)≠0`. The congruence defined by `sx=sy` contains fourth rejoin, and each fiber of the canonical surjection `π:P8→P4` lies in this congruence. Cancellation of the nonzero real factor `R(s)` then gives a unique function

\[
R_4:P4\to\mathbb R,\qquad R=R_4\circ\pi.
\]

The separate global corollary transfers normalization, multiplication, `T`-nullity and additive null closure under its stronger supplied global contract. [Local contract, positive certificate and unique factorization](../Proofs/QMClosure/EighthRejoinNullClosureDescent.lean)

The same certificate pinpoints a failure of both concrete controls. Its summands have norm pairs

\[
(X(TA),Y(TA))=(0,1),\qquad
(X(sB),Y(sB))=(1,0).
\]

Thus `W(TA)=W(sB)=0` and `V(TA)=V(sB)=0`, while both responses equal one on `TA+sB`. Each fails the exact fifth premise. The distinction between additive closure of the null set and arbitrary null insertion continues to matter for later routes. [Certificate values and local coalescence failures](../Proofs/QMClosure/EighthRejoinNullClosureDescent.lean)

## Remaining scope

The checked conclusion is unique function-level readout factorization under the local contract. Literal fourth rejoin on the source, equality of the continuation congruence with the canonical kernel, arbitrary null insertion, destructive `T=0` quotient descent and selection of the Gaussian norm remain separate obligations. The Lean ledger records the generic core, concrete `P8` controls and local descent as three distinct checked tasks. [Research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The next analytic tasks cover general finite-cycle null selection with residue-characteristic countermodels, first-column balance with real Archimedean bounds, a null-closed `P8` echo countercontrol, and an alternate conservation/order/echo reconstruction route on exact `P4` geometry. Their checked-evidence fields remain empty while formalization is pending. The older scalar and word reconstruction tasks retain their own outstanding proofs. [Research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

Physical origins and operational availability of the grammar, rejoin relations and response tests remain open alongside Born actualization, Hilbert representation, dynamics, composites, full QM, GR and physical scales. [Physical scope boundary](150-physical-scope-boundary.md)
