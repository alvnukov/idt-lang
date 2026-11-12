# Branch balance and readout-order boundaries

Two Lean artifacts isolate the roles of first-column conservation and real-valued readout on the original initial two-relator carrier. Four independently reviewed analytic results add relative omission controls, calibration-replacement countercontrols and one-sided scalar and word reconstructions. Their authoritative task records retain separate evidence and stages. [Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

| Result | Mathematical evidence |
|---|---|
| Positive real first-column balance and gain four | Conditional Lean theorem |
| Lexicographic additive-pair readout control | Explicit Lean construction |
| Six-schema relative nonredundancy | Analytic, awaiting formalization |
| Unit-orbit calibration replacement boundary | Analytic, awaiting formalization |
| One-sided scalar-dyadic reconstruction | Analytic, awaiting formalization |
| One-sided word-only reconstruction | Analytic, awaiting formalization |

## 1. Positive first-column balance

Let P be the literal initial positive Nat algebra with exactly a+b=1 and a^4=b^4. Put c=2ab. For W:P→Real, supply global nonnegativity and the two universally quantified response laws

W(ap)+W(bp)=W(p),

W(cp)=W(p).

The checked theorem derives, at every preparation,

W(ap)=W(bp)=W(p)/2,

W(2p)=4W(p).

Its pure algebraic proof constructs bInv=2a+e, half=ab+T² and ρ=a bInv within P. The checked identities give b bInv=1, 2 half=1, ρ⁴=1, bInv=1+ρ and c bInv²=2ρ. Applying the supplied response laws in these inverse contexts gives four doubling equations on the ρ orbit. The orbit sum S has gain four, two opposing difference modes D have gain two, and the alternating mode vanishes. Inverse dyadic scaling transports |D(p)|≤S(p) to 2^n|D(p)|≤S(p) for every n at a fixed preparation. Real Archimedean reasoning forces D(p)=0. Orbit equality then gives branch balance and gain four. The central declarations are `orbit_balance`, `column_balance_and_double_gain` and `vanishing_difference`. [Checked balance module](../Proofs/QMClosure/TransparentFourthColumnBalance.lean)

The prepared-count adapter derives its needed nonnegativity. First-column conservation at zero gives W(0)=0. Comparing counts (0,0) and (1,1) at every p gives W(0)≤W(p). Thus this single comparison family suffices for the adapter, and universal coordinatewise prepared-count order includes it. Unit normalization is needed only for the additional conclusion W(2)=4. The theorem uses the initial algebra directly. The full five-schema W=N route additionally depends on the separate analytic weak reconstruction and its checked exact combined-coordinate normal-form prerequisite. That reconstruction retains empty checked evidence. [Checked prepared-count adapter](../Proofs/QMClosure/TransparentFourthColumnBalance.lean) · [Authoritative task scopes](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## 2. A supplied lexicographic additive-order boundary

Let E:P→Complex be complex evaluation and N(p)=|E(p)|². Supply the response carrier Real×Real with componentwise addition, distinguished unit (1,0), and explicit lexicographic relation

(x₁,x₂)≤lex(y₁,y₂) iff x₁<y₁ or (x₁=y₁ and x₂≤y₂).

Lean checks reflexivity, transitivity, antisymmetry, totality and translation compatibility for this relation. Define

L(p)=(N(p), Re E(p)−N(p)).

This L is lexicographically nonnegative and satisfies vacuum zero, unit normalization, exact universal c transparency, universal prepared natural-count order, all word-scaled raw mixed-zero tests and L(T)=0. Its mixed-zero identity holds at every preparation, so it includes every externally supplied scalar scale family. It also satisfies first-column conservation and null insertion. [Checked ordered-response module](../Proofs/QMClosure/TransparentFourthOrderedReadoutBoundary.lean)

The exact checked values include

L(2)=(4,−2),

L(ab)=(1/4,1/4),

L(a)=(1/2,0), L(a²)=(1/4,−1/4).

Thus L differs from the norm pair (N,0), and L(a²) differs from componentwise half(L(a)). The difference L(ab)−(N(ab),0)=(0,1/4) is strictly positive, while every natural multiple of it lies below (1,0). This supplies a concrete non-Archimedean additive-order control. The response retains the initial carrier's nonzero T with L(T)=0. Its first coordinate is N. The contract supplies the displayed additive order and makes no ordered-field or faithful-readout assumption. [Exact witnesses and infinitesimal bound](../Proofs/QMClosure/TransparentFourthOrderedReadoutBoundary.lean)

The result identifies failure of the displayed real-readout conclusions under this specific enlargement of the response carrier. A necessity or completeness characterization for real order remains a separate question. The real-valued reconstruction continues to have its actual real-valued hypotheses. [Scalar reconstruction contract](212-scaled-count-readout-reconstruction.md)

## 3. Six-schema relative nonredundancy

For the equality-based scalar reconstruction, write δ(p)=1 when E(p)=0 and q(p)>0, and δ(p)=0 otherwise. Here q is the nonnegative real-shadow evaluation. Use exactly the original schemas S0 for vacuum zero, S1 for unit normalization, Sc for universal exact c transparency, So for universal prepared count order, Sm for adjacent mixed zero at every scalar preparation 2^(−k), and ST for W(T)=0.

Each row below satisfies all five retained schemas and violates its omitted schema. These are independently accepted analytic certificates awaiting formalization. Their checked-evidence lists remain empty. [Analytic reconstruction and exact schema quantifiers](212-scaled-count-readout-reconstruction.md) · [Omission task](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

| Omitted schema | Response | Exact failure |
|---|---|---|
| S0 | 2N−1+δ | W(0)=−1 |
| S1 | 2N | W(1)=2 |
| Sc | q indicator(E≠0) | W(c)=1/2, W(1)=1 |
| So | Re E | At preparation a², counts (0,0)≤(1,0) give 0>W(a³)=−1/4 |
| Sm | N² | The unscaled origin mixed defect is 1/2 |
| ST | N+δ | W(T)=1 |

The universal retained-schema checks reduce to exact prepared formulas. Put C(n,m)=(n²+m²)/2, Q(n,m)=(n+m)/2 and J(n,m)=indicator(n+m>0). For B(n,m)=na+mb,

N(B(n,m)p)=C(n,m)N(p),

q(B(n,m)p)=Q(n,m)q(p),

δ(B(n,m)p)=J(n,m)δ(p).

C,Q,J are nonnegative and coordinatewise nondecreasing. They prove So for its retained rows. The Re E response is linear in n,m, the q control is Q(n,m) times its prepared value, and each raw δ term vanishes. Consequently the retained raw mixed-zero arrays separate into sums of one-variable functions. The N² omitted mixed defect is already 1−1/4−1/4=1/2 at scale zero. These arguments use the evaluation maps and their elementary values. [Authoritative analytic certificate scope](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The exact-transparency alternative uses word preparations (ab)^k and replaces ST by the single T-origin mixed-zero test. Its omission table is verified separately. The S0 control becomes 2N−1, and the remaining five controls above still apply. The scalar/word equivalence uses Sc, while the ST/T-origin equivalence uses Sc and S0. Omitting one of these premises therefore requires its own retained-test verification. [Exact-transparency reformulation](212-scaled-count-readout-reconstruction.md)

Positivity boundaries depend on the chosen family. In the original family, adding global positivity makes S0 follow from So and ST through 0≤W(0)≤W(T)=0. For the alternative T-origin family, the positive normalized response (N+1)/2 still violates S0 while retaining its other five schemas. Relative independence here concerns these precise quantified schema families. The physical origins and globally minimal choices of response principles remain open. [Analytic omission task and limits](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## 4. Calibrating the entire unit orbit leaves a universal gap

For R≥1 define the real-valued response

H_R(p)=max(N(p), q(p) max(0,√N(p)−R)).

This independently accepted analytic control satisfies vacuum zero, unit normalization, universal prepared count order, W(T)=0, and every scalar and word raw mixed-zero test. It also has zero response on every E-null preparation and passes the T-origin test. Prepared order follows because its prepared formula is

max(C N(p), Q q(p) max(0,√C √N(p)−R)),

whose nonnegative factors are coordinatewise nondecreasing. On each raw family q≤√N, making the second maximum branch at most N. Thus H_R=N directly on both raw families. Universal c transparency is unnecessary for this calculation. [Analytic calibration task](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

For every integer j, N(c^j)=1, giving H_R(c^j)=1. The response therefore passes every positive and negative unit-orbit calibration. Nevertheless for H_1 and the actual generated preparation p=2(1+e)²,

N(p)=N(cp)=4, q(p)=8, q(cp)=4,

H_1(p)=8, H_1(cp)=4.

The formula is continuous as a function of its ambient complex and real coordinates. It agrees exactly with N throughout N≤1, so the displayed deviation lies beyond that entire region. For p=2(1+e), it additionally gives H_1(p)=4, H_1(T)=0 and H_1(p+T)=9/2. Thus vanishing on all E-null preparations leaves a null-insertion obligation. [Exact analytic countercontrol task](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

Taking R=2^J gives agreement with N on the larger region N≤4^J and still has H_R(2R(1+e)²)=8R², H_R(c 2R(1+e)²)=4R². For each fixed finite set F of actual preparations, a sufficiently large J puts all of F in that region. Every finite transparency test on F then passes since c preserves N. The quantifiers are “for every finite F there exists a counterresponse.” Each response also passes both infinite raw families and the complete integer unit orbit. [Calibration replacement task](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

A separate cap family A_J=min(N,4^J q²), J≥1, preserves the scalar raw tests and satisfies A_J(c^j)=1 for 0≤j≤J, with A_J(c^(J+1))=1/4. Its word-family origin defect at preparation (ab)^J is 4^(−J)/2>0. This exact failure records the dependence of scalar/word test equivalence on the original exact-transparency premise. Both cap and threshold families remain analytic awaiting formalization. [Analytic task with family-specific premises](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## 5. Direction of the supplied serial law

The stronger scalar theorem replaces universal W(cp)=W(p) by universal W(cp)≥W(p), retaining the other scalar-grid schemas. It derives the same first-five κ classification, with W(T)=0 selecting W=N. Its proof derives exact transparency at the end. The four changes to origin continuity, upper landing, inverse-context lower landing and positive-null equality are recorded with their directions in the reconstruction section. [One-sided scalar proof](212-scaled-count-readout-reconstruction.md)

H_1 satisfies the opposite universal inequality H_1(cp)≤H_1(p), since c fixes N and halves q. Its displayed 8-to-4 failure therefore shows that the opposite direction leaves extra responses even when both raw families and the null test are supplied. The word-only reconstruction under the forward one-sided law is now independently accepted analytically. It forms an exactly transparent orbit supremum, invokes the original exact scalar theorem on that supremum and transfers a lower bound back to W by uniform raw convergence. Cellwise scalar/word inequalities alone supply insufficient information to transfer a vanishing alternating mixed defect. [Analytic task records](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Evidence and physical scope

The balance and ordered-response modules supply the two checked results. The new relative omission, calibration-replacement and one-sided scalar and word results have empty checked evidence. Their proof obligations retain their analytic stages. Physical availability of inverse contexts, detector realization, probability actualization and origins of the response laws remain separate obligations. Hilbert representation, dynamics, composites, full QM, GR and physical scales retain their existing public boundaries. [Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean) · [Physical scope boundary](150-physical-scope-boundary.md)
