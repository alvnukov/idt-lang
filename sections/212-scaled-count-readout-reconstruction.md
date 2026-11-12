# Scaled-count readout reconstruction

This analytic conditional reconstruction awaits Lean formalization. Its checked-evidence list remains empty. It uses the exact initial normal form and six supplied response schemas. The strongest accepted analytic version supplies the one-sided serial law W(cp)≥W(p) and raw mixed tests only at word preparations (ab)^k, deriving serial equality and scalar-grid tests. The exact-transparency and one-sided scalar-grid arguments below are established intermediate results. The final section gives the word-grid theorem. [Analytic task](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean) · [Checked initial normal form](../Proofs/QMClosure/TransparentFourthInitialNormalForm.lean)

## Exact premises

P is the initial positive Nat algebra with a+b=1 and a^4=b^4, with exact combined-coordinate identification {0} union {(z,q): z Gaussian dyadic, q positive dyadic} supplied as a separate prerequisite. This includes equality reflection and exact image, not just two evaluation maps. Let a=((1+i)/2,1/2), b=((1-i)/2,1/2), c=2ab=(1,1/2), T=a^2+b^2=(0,1/2), and N=normSq E.

For a real-valued response W on P, supply the following six schemas.

1. W(0)=0.
2. W(1)=1.
3. W(cp)=W(p) for every p in P.
4. For every p in P and n,m,nprime,mprime in Nat with n≤nprime and m≤mprime,
   W((na+mb)p)≤W((nprime a+mprime b)p).
5. For every k,n,m in Nat, put d=2^(-k). Then
   W(d B(n+1,m+1))-W(d B(n+1,m))-W(d B(n,m+1))+W(d B(n,m))=0.
6. W(T)=0.

Compared with the original vacuum-replacement question, schema 5 strengthens raw natural mixed zero to the same adjacent four-cell test at every common inverse-power-of-two scale, and schema 6 adds a single null witness calibration. These are different operable tests. The norm-selection route supplies six response schemas.

No first-column, half, scalar gain, multiplicativity, conjugation invariance, null insertion, response continuity or supplied raw calibration is assumed.

For a real-valued response W, the first five schemas classify exactly W(p)=N(p)+kappa*indicator(E(p)=0 and q(p)>0), with one kappa>=0. Every such kappa response satisfies those five schemas. Schema 6 selects kappa=0, giving W(p)=N(p) for every p.

Under c transparency, the raw response tests at scalar preparation 2^(-k) have the same values as those at preparation (ab)^k. The coordinate identities give (ab)^k=c^k 2^(-k), so repeated transparency supplies the response equality for every raw bag. The two preparations have different shadow coordinates for k>0. The equivalence concerns the tested response values. [Checked coordinate normal form](../Proofs/QMClosure/TransparentFourthInitialNormalForm.lean)

## 1. Raw separation and zero-origin continuity

The scalar inverse powers of two are algebraic P units, independently of response laws. Prepared natural-count order extends to any coordinatewise dyadic count comparison by changing preparation to 2^(-k)p. It also gives W(p)≥0 by comparing (0,0) and (1,1).

For nonnegative dyadic d put U(d)=W(da), V(d)=W(db). Common-grid telescoping of schema 5 gives

W(B(s,t))=U(s)+V(t), B(s,t)=sa+tb,

for all nonnegative dyadic s,t. Both U,V are nondecreasing, U(0)=V(0)=0. In particular w(d)=W(d)=U(d)+V(d).

Because c(d/2)=dab, c transparency gives W(dab)=w(d/2). Prepared comparisons at da and db give

w(d/2)≤U(d), and w(d/2)≤V(d).

The monotone right limits A=U(0+), B=V(0+) exist and are finite/nonnegative. Passing through positive dyadics d→0 gives A+B≤A and A+B≤B. Thus A=B=0. This establishes the relevant origin continuity from the response schemas.

Use the following right envelopes on nonnegative reals.

f(s)=inf{U(d): d dyadic, d>s}, h(t)=inf{V(d): d dyadic, d>t}.

They are finite, nonnegative, nondecreasing and right-continuous, with f(0)=h(0)=0. If dyadics d_j>s tend to s, then U(d_j)→f(s), and similarly for V. For arbitrary dyadic d_j→s, limsup U(d_j)≤f(s).

## 2. Only the upper wedge geometry is needed for calibration

The finite upper raw-landing construction in Appendix A uses only c transparency, prepared count order, finite dyadic/rational-overhead programs and combined-coordinate equality reflection. The endpoint construction uses no half-response or gain premise.

For p=(x+iy,q), x>|y|, x>0, it produces response-increasing M_j and exact raw endpoints M_jp=B(s_j,t_j), where s_j→x+y and t_j→x-y. Therefore

W(p)≤f(x+y)+h(x-y).

No lower envelope, continuity point, half law or gain enters this upper inequality. For later notation put H(s,t)=f(s)+h(t) for s,t>0.

## 3. Every local rotation inequality holds on the real envelope

For dyadic 0<epsilon<1/2 the finite program F_plus=(1+i epsilon,1+epsilon) is response-increasing at every preparation. Indeed represent epsilon=m/L with L a power of two and use the natural comparison (0,L)≤(m,L) at (Lb)^(-1)p. F_minus is analogous with a.

For real s,t>0 with s+epsilon t>0 and t-epsilon s>0, choose dyadic s_j,t_j with each approximation error lying between delta_j and 2 delta_j, delta_j→0. Such approximations exist on sufficiently fine dyadic grids. Both transformed errors

(s_j-s)+epsilon(t_j-t),
(t_j-t)-epsilon(s_j-s)

are positive. The raw element p_j=B(s_j,t_j) has response U(s_j)+V(t_j)→H(s,t). Its F_plus image lies in the strict wedge eventually, and its two wedge arguments are s_j+epsilon t_j and t_j-epsilon s_j. The upper wedge inequality and right continuity give

H(s,t)≤H(s+epsilon t,t-epsilon s).

The same argument gives the opposite-sign inequality whenever its endpoint remains positive. No exceptional continuity-point choices are necessary.

## 4. Envelope rotational invariance and quadratic calibration

Take two points in the open positive quadrant with the same Euclidean radius. Their angle difference theta stays within that quadrant. Choose dyadic epsilon_n>0 with n epsilon_n→abs(theta) and n epsilon_n^2→0. For sufficiently large n, n successive signed local-rotation steps remain in the quadrant. Their endpoint is

(1+epsilon_n^2)^(n/2) times the rotation by signed n arctan(epsilon_n),

so it converges to the target. Repeated section 3 inequalities give H(start)≤H(endpoint_n). To obtain limsup H(endpoint_n)≤H(target), bound each endpoint coordinate by the target coordinate plus a common positive tolerance and apply monotonicity and right continuity. Thus H(start)≤H(target). Reverse the angle to obtain equality.

In particular H(s,t)=H(t,s), so f(s)-h(s) is constant. Letting t decrease to zero and using section 1 gives f=h.

Define K(x)=f(sqrt(x)) for x≥0. Radiality applied to the positive-coordinate pairs (sqrt(x+y),sqrt(z)) and (sqrt(x),sqrt(y+z)) gives

K(x+y)+K(z)=K(x)+K(y+z), x,y,z>0.

Let x decrease to zero. Right continuity gives K(y)+K(z)=K(y+z). Monotone Cauchy therefore gives K(x)=kappa x. Hence f(s)=h(s)=kappa s^2. Since continuous left and right envelopes squeeze every dyadic value, U(d)=V(d)=kappa d^2. W(1)=U(1)+V(1)=1 gives kappa=1/2.

This gives the exact raw dyadic calibration

W(B(s,t))=(s^2+t^2)/2.

## 5. Gain-free lower-transfer rule

Suppose a response-increasing finite program M, natural raw r0, and natural A,B with H0=max(A,B)>0 satisfy the actual P identity

M r0=B(A,B)p.

For positive dyadics d_j increasing to 1/H0, one has d_j A≤1 and d_j B≤1. Extended dyadic prepared order gives

d_j^2 N(r0)=W(d_j r0)≤W(M(d_j r0))=W(B(d_j A,d_j B)p)≤W(p).

Numerical limiting gives W(p)≥N(r0)/H0^2. This invokes no scalar law at the arbitrary preparation p.

## 6. Upper bound for every nonzero complex direction

Raw calibration and section 2 give W(p)≤N(p) on the strict right wedge. For arbitrary E(p)≠0, finite products of F_plus/F_minus rotate its complex coordinate into that wedge with squared modulus tending to 1. Their response-increasing property gives

W(p)≤W(L_jp)≤N(L_jp)→N(p).

Only numerical calibrated upper bounds are passed to a limit.

## 7. Direct general-direction lower construction, with no virtual P elements

Fix p=(z,q), z≠0. Choose a finite response-increasing rotation program A=(alpha,beta) so that the Gaussian-rational design coordinate

z/alpha=u+iv

has u>|v|>0. Such programs can have abs(alpha)^2 arbitrarily close to 1 by small Euler rotations to a fixed interior nonaxis angle. Division here supplies rational design parameters. The construction uses actual P preparations throughout.

Change the actual target p by a power of c^(-1) so that q>beta u. This preserves W and z. Set lambda=q/(beta u)>1. The paired finite programs of Appendix A2 give (R,Q), with R→1 and Q/R→lambda from below. Define the rational number

eta=(u-qR/(beta Q))/v→0.

For sufficiently small paired steps, all coefficients below are positive. Choose a positive integer X clearing denominators in

Acount=X(1+eta), Bcount=X(1-eta),

and in the two raw counts belonging to the Gaussian-rational coordinate

z0=(X/R)(u+iv)(1+i eta).

This yields natural Acount,Bcount and a natural raw element r0 with complex coordinate z0 and shadow q0=Re(z0). The definition of eta gives q0=Xq/(beta Q). Both coordinates therefore satisfy the following exact identity.

(A (R,Q)) r0=B(Acount,Bcount)p.

Indeed the complex coordinate is X(1+i eta)z and the shadow coordinate is Xq. Every element in this identity is an actual P element, so combined-coordinate equality reflection applies. The rational quotient z/alpha is never treated as a preparation.

With H0=X(1+abs(eta)),

N(r0)/H0^2 = [N(p)/abs(alpha)^2] (1+eta^2)/[R^2(1+abs(eta))^2].

The gain-free transfer gives a lower bound approaching N(p)/abs(alpha)^2. Thus W(p)≥N(p)/abs(alpha)^2 for each rotation A. Taking rotation programs with abs(alpha)^2→1 proves W(p)≥N(p). Combined with section 6 this gives W=N for every nonnull complex coordinate.

## 8. Positive null sector

For p=(0,q), prepared scalar dyadic order makes its response monotone in positive dyadic q. c transparency preserves response under q↦q/2. Any two positive dyadic q are sandwiched between power-of-two multiples of one another, so all positive-null responses equal one common constant kappa_null. Schema W(T)=0 makes this constant zero. W(0)=0 covers the actual vacuum.

Without W(T)=0, the same argument still reconstructs W=N on every E(p)≠0 and allows a constant nonnegative positive-null response. This is an exact residual freedom, already exemplified by the null-sector countermodel.

### Equivalent presentation of the null witness as the same local test

Within the explicit algebraic prerequisites, cT=aT=bT. The combined-coordinate normal form checks all three as (0,1/4). The pure identities e=2T and ea=eb=T also give cT=2abT=a(2bT)=aT, and cT=b(2aT)=bT.

Consequently c transparency implies W(aT)=W(bT)=W(T). With vacuum zero, the additional origin-cell mixed test at the single preparation T is

W((a+b)T)-W(aT)-W(bT)+W(0)=0,

which is exactly -W(T)=0. Thus schema 6 can equivalently be stated as this one additional instance of the same adjacent four-cell test. The test family is the raw scalar preparations 2^(-k), for all k, plus this single T preparation at the origin cell. This is not universal prepared mixed zero and does not assume the first-column equation for arbitrary p. The equivalent presentation retains the physical availability and origin obligations for these tests and keeps six schemas.

## 9. Two exact controls for the repair boundary

These controls establish the need for the two stated repairs relative to the displayed retained schemas. They do not prove global minimality, independence of every schema, or uniqueness of the chosen repairs.

### 9.1 Natural scale alone remains insufficient even with W(T)=0

Define f0(t)=t+t(1/2-t) for t≤1/2, and f0(t)=t for t>1/2, and W_A(p)=f0(N(p)). On nonnegative inputs f0 is continuous and strictly increasing. When u≤v≤1/2 its difference is (v-u)(3/2-u-v)≥(v-u)/2. It fixes zero and every natural half-integer. Thus W_A has vacuum zero, unit normalization, c transparency, universal prepared natural-count order, raw NATURAL mixed zero, and W_A(T)=0. It even descends through complex evaluation and has null insertion invariance.

But W_A(ab)=5/16 while N(ab)=1/4. At dyadic scale d=1/2 and the origin cell, the mixed difference is

f0(1/4)-2f0(1/8)=5/16-2(11/64)=-1/32.

Hence the scaled schema genuinely excludes a control that all the other repaired premises plus the old natural mixed test permit. No normal-form theorem is needed for this control, only complex evaluation.

### 9.2 All dyadic raw tests leave an independent null constant

For any kappa>0, define W_B(p)=N(p)+kappa times the indicator of E(p)=0 and q(p)>0. This obeys W(0)=0, W(1)=1, c transparency and universal prepared count order. For every nonnegative dyadic raw bag B(s,t), its exceptional indicator is zero because s=t=0 gives the actual vacuum and every remaining raw bag has nonzero complex coordinate. Therefore W_B satisfies exact dyadic raw calibration, and in particular all-scale raw mixed zero.

Nevertheless W_B(T)=kappa, so W_B differs from N. Taking kappa=1 supplies an exact rational witness. The same construction for every kappa>=0 supplies the converse in the first-five-schema classification, including kappa=0. Its scalar norm term and exceptional term are nonnegative and count-monotone, c transparency preserves both, and the exceptional term vanishes on every raw dyadic bag. For the universal count-order verification, at any preparation p,

W_B(B(n,m)p)=((n^2+m^2)/2)N(p)+kappa delta(p) indicator(n+m>0).

Both count factors are coordinatewise nondecreasing and both coefficients nonnegative. This control also needs only the evaluation homomorphisms, not exact normal form.

### 9.3 No fixed finite prefix of raw dyadic scales suffices

Fix K in Nat and let delta=(1/2)4^(-K). Define f_K(t)=t+t(delta-t) for t≤delta, and f_K(t)=t for t>delta. Since 0<delta≤1/2, for u≤v≤delta its difference is

(v-u)(1+delta-u-v)≥(v-u)(1-delta)≥(v-u)/2.

The pieces agree at delta. Thus f_K is continuous and strictly increasing. The response W_K=f_K composed with N has vacuum zero, unit normalization, c transparency, universal prepared natural-count order, W_K(T)=0 and null insertion invariance.

For every scale k≤K and natural n,m, a nonzero raw squared norm 4^(-k)(n^2+m^2)/2 is at least delta. Hence all raw values at those scales are calibrated exactly, and every adjacent mixed difference at each such scale vanishes.

But for p=2^(-K)ab, N(p)=delta/2 and W_K(p)-N(p)=delta^2/4>0. Already the origin cell at the next scale K+1 has defect

f_K(delta/2)-2f_K(delta/4)=-delta^2/8.

Therefore no fixed finite initial set of scale tests establishes the universal all-scale premise, even with the null calibration and the other retained schemas. A rule propagating scale tests to all depths would require its own independent justification. This is an analytic boundary, not a machine-checked finite-depth theorem.

### 9.4 A scale-independent relative discrepancy after every finite prefix

The normalized variant replaces the bump by `t*(delta-t)/(2*delta)` below `delta`, retaining the identity above `delta`. Its real scalar remapping is continuous and strictly increasing, with secant slopes between `1/2` and `3/2` on `[0,delta]`. It retains all the preceding finite-prefix premises. At `N(p)=delta/2`, it gives `W(p)=5*delta/8`, an exact relative excess of `1/4` for every `K`. The next-scale origin-cell defect is `-delta/16`. Thus a finite prefix supplies no uniform relative-error guarantee strictly below `1/4` over all generated scales. This quantitative boundary remains analytic awaiting formalization.

## Appendix A. Self-contained finite program geometry used above

The following numerical and exact-coordinate constructions supply the finite geometry used in the proof.

### A1. Dyadic and rational-overhead monotonic programs

For dyadic t=m/L≥0, L a power of two, define F_plus(t)=(1+it,1+t), F_minus(t)=(1-it,1+t). The formula F_plus(t)=B(m,L)(Lb)^(-1), with the analogous formula using a, gives actual P elements. The inverses of a,b and powers of two are supplied algebraic units. Prepared count order at (Lb)^(-1)p, comparing (0,L)≤(m,L), gives W(p)≤W(F_plus(t)p).

For rational tau=h/d>0 and positive dyadic tolerance eta, choose L a sufficiently large power of two and n the least multiple of d with n≥L. Put m=n tau and alpha=n/L. Then m,n are naturals, 1≤alpha<1+d/L, and both alpha and alpha tau are dyadic. Comparing (0,L)≤(m,n) at (Lb)^(-1)p gives the actual response-increasing program

D(alpha,tau)=(alpha(1+i tau),alpha(1+tau)).

One can require alpha<1+eta by choosing L>d/eta. No odd-denominator inverse preparation is used.

### A2. Paired programs with prescribed shadow-to-real ratio

Fix rational lambda>1. For dyadic 0<t≤1 put K=(1+t)^2/(1+t^2)>1, and choose the largest natural n with K^n<lambda. Zero is admissible and Bernoulli bounds the admissible set, so its largest n exists. Then lambda/K≤K^n<lambda. The product

M=(F_plus(t) F_minus(t))^n=(R,Q),
R=(1+t^2)^n, Q=(1+t)^(2n),

is response-increasing, and Q/R=K^n approaches lambda from below as t→0. Since K-1=2t/(1+t^2)≥t, Bernoulli gives nt<lambda-1 and nt^2<(lambda-1)t. For small t, nt^2<1 and the binomial bound choose(n,j)≤n^j gives

1≤R≤1/(1-nt^2).

Thus R→1 and Q→lambda. Only finite programs and numerical limits occur.

### A3. Exact upper raw landing

Let p=(x+iy,q), x>|y|, x>0. Apply a positive power of c to its actual preparation so that q<x while preserving W and z. Take lambda=x/q>1 and the paired programs (R,Q) above. Put gamma=qQ, so gamma<Rx, gamma→x and R→1. Eventually gamma+Ry>0. Define the positive rational

tau=(Rx-gamma)/(gamma+Ry)→0.

Choose the rational-overhead D(alpha,tau) with alpha→1. Then D M p has complex coordinate

alpha R((x-tau y)+i(y+tau x))

and shadow alpha gamma(1+tau). The defining equation for tau gives gamma(1+tau)=R(x-tau y), so its shadow equals the real part of its complex coordinate. The real part exceeds the absolute imaginary part for sufficiently small t. Its exact dyadic raw counts are

s=alpha R((x-tau y)+(y+tau x)),
u=alpha R((x-tau y)-(y+tau x)).

Both counts are positive dyadic because alpha and alpha tau are dyadic, and s→x+y, u→x-y. Combined-coordinate equality reflection identifies D M p=B(s,u) in actual P. This proves the upper endpoint construction used in section 2 without any response scaling law.

### A4. Explicit finite rotation approximation

For a desired real angle theta, choose positive dyadic epsilon_n with abs(epsilon_n-abs(theta)/n)≤1/n^2, for sufficiently large n, and use the sign of theta. Then n epsilon_n→abs(theta), n epsilon_n^2→0, and n arctan(epsilon_n)→abs(theta). The actual program

L_n=F_sign(epsilon_n)^n

has complex coordinate (1+sign(theta)i epsilon_n)^n, with squared modulus (1+epsilon_n^2)^n→1 and argument converging to theta. Its shadow is positive dyadic. When theta=0, the identity program suffices. To derive radiality in section 4, the fixed start and target angles lie strictly within the positive quadrant. For all sufficiently large n the monotone intermediate angle path remains inside it. For arbitrary preparation rotations, universal prepared count order applies throughout the intermediate path.

## Dependency and verification boundaries

The argument uses the exact initial combined-coordinate normal form (including equality reflection, exact image, commutative coordinate operations and the required algebraic units), the six explicitly quantified response schemas, ordinary real order/Archimedean completeness, monotone-envelope facts and elementary finite-program numerical limits. Appendix A states the finite geometry in full with its minimal response dependencies. Rational divisions in section 7 are parameter design only, followed by integer clearing and equality of actual P elements.

The resulting W=N mathematically yields the first-column equation, both half responses, scalar quadratic gain, multiplicativity and null insertion/destructive-quotient descent. The original initial carrier retains its nonzero element e. The analytic response factorization selects equality of readout values along the destructive quotient. Physical availability of preparations and inverse contexts, detector realization, probability interpretation and the origins of all six response schemas remain separate obligations. [Physical scope boundary](150-physical-scope-boundary.md)

## One-sided serial strengthening on scalar grids

The supplied serial equality in the scalar-grid theorem can be weakened analytically to

W(cp)≥W(p) for every p in P.

Retain vacuum zero, unit normalization, universal prepared count order and every scalar-dyadic raw mixed-zero test exactly as quantified above. The first five schemas still classify exactly

W(p)=N(p)+κ indicator(E(p)=0 and q(p)>0), κ≥0.

The sixth schema W(T)=0 selects W=N. Exact serial equality follows from the classification. This strengthened theorem is independently reviewed and awaits Lean formalization, with empty checked evidence. The equality-based theorem above is its corollary. [Authoritative analytic and open tasks](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

### Directed changes to the proof

The raw separation and scalar-order arguments use the same scalar grids. For section 1, the necessary origin estimate becomes

w(d/2)≤W(c(d/2))=W(dab)≤U(d), V(d).

The first inequality is the supplied serial law. The algebraic identity and the two prepared-count comparisons give the remaining steps. The same monotone origin limits satisfy A+B≤A and A+B≤B, forcing A=B=0.

For upper landing in section 2 and Appendix A3, choose a nonnegative integer j so that c^j p has shadow smaller than its positive real complex coordinate. The serial law supplies W(p)≤W(c^j p). All subsequent finite programs are response-increasing by prepared order, so their calibrated endpoints still bound W(p) from above. Sections 3 and 4 then derive the same rotationally invariant scalar envelopes and exact raw quadratic calibration. Section 6 derives the same nonnull upper bound.

For lower landing in section 7, replace the target by the actual inverse context p′=c^(−h)p with sufficiently large shadow. Universality of the supplied inequality gives

W(p′)≤W(c^h p′)=W(p).

The denominator-cleared finite construction and section 5 transfer give numerical lower bounds for W(p′), hence for W(p). The numerical limits therefore yield W(p)≥N(p), completing nonnull reconstruction. Rational design parameters and actual P preparations retain their roles in section 7.

For a positive-null p=(0,q), the carrier identities give cp=ap=bp=(0,q/2). Prepared order supplies W(cp)=W(ap)≤W(p), while the serial hypothesis supplies W(cp)≥W(p). Thus equality holds on the positive-null sector. Monotonicity and power-of-two sandwiching make its response a constant κ≥0. Every displayed κ response satisfies the five supplied schemas by the same prepared-count formula as section 9.2, proving the converse. Since aT=bT=cT, the T-origin mixed defect is −W(T). The single local test and the null calibration are again equivalent under these deduced null-sector facts.

### Scope of the raw test family

The strengthened theorem supplies mixed tests at scalar preparations 2^(−k). Before reconstruction, the identity (ab)^k=c^k 2^(−k) and the one-sided law yield only

W((ab)^k B(n,m))≥W(2^(−k) B(n,m)).

A mixed defect has coefficients of both signs, so these cellwise inequalities supply no equality of defects. The final section independently proves reconstruction with mixed tests supplied only at (ab)^k, using an orbit supremum and the original exact-transparency scalar theorem. After either reconstruction, deduced exact serial equality gives equality of both raw test families. The earlier scalar/word equivalence continues to apply with its stated exact-transparency premise. [Word-grid analytic task](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

### Opposite orientation and calibration boundary

The reverse universal inequality W(cp)≤W(p) leaves additional responses. An explicit analytic control is

H(p)=max(N(p), q(p) max(0,√N(p)−1)).

It has vacuum zero, unit normalization, universal prepared count order, W(T)=0, every scalar and word raw mixed-zero test, and H(c^j)=1 for every integer j. At p=2(1+e)^2 it gives H(p)=8 and H(cp)=4, with N(p)=N(cp)=4. Throughout N≤1 it agrees exactly with N. The complete retained-schema proof and further calibration and omission boundaries are recorded in the companion section. These controls remain analytic awaiting formalization. [Branch balance and readout-order boundaries](213-branch-balance-and-readout-order-boundaries.md)

## Word-grid reconstruction with one-sided serial order

The strongest accepted analytic contract uses actual word preparations h^k=(ab)^k for its raw tests. Let u=2^(−1) be the actual scalar inverse of two. Retain the same initial carrier, exact combined-coordinate normal form, equality reflection, exact image and actual units from the preceding arguments. For W:P→Real supply these five schemas.

1. W(0)=0.
2. W(1)=1.
3. W(cp)≥W(p) for every actual p.
4. Universal natural-count coordinatewise order at every actual preparation.
5. For every k,n,m in Nat, the adjacent mixed defect at preparation h^k is zero.

Then exactly the responses W=N+κ indicator(E=0 and q>0), κ≥0, satisfy the five schemas. The optional sixth schema W(T)=0 selects W=N. Exact serial transparency and scalar-grid mixed zero follow from the classification. This theorem is independently reviewed analytically and awaits Lean formalization with empty checked evidence. Its dependency is the original exact-transparency scalar first-five classification established analytically above. [Authoritative word-grid task](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

### Finite orbit bounds from uncalibrated raw landing

Dyadic prepared order follows by clearing powers of two in the counts and changing the actual preparation. It gives W≥0. For a positive-null p, cp=ap=bp, and count order gives W(cp)≤W(p). The supplied forward inequality therefore gives equality. Dyadic scalar order and power-of-two sandwiching make W one nonnegative constant κ on this sector.

The finite programs F_plus, F_minus, D and the paired (R,Q) construction from Appendix A remain response-increasing by count order alone. For a strict right-wedge preparation p=(x+iy,q), first choose j≥0 so that p₀=c^j p has shadow q₀<x. The serial inequality gives W(p)≤W(p₀). Choose paired programs with λ=x/q₀, put γ=q₀Q and τ=(Rx−γ)/(γ+Ry), and use D(α,τ) with α tending to one. The actual endpoint is a raw bag B(s,t), with s→x+y and t→x−y. Every step increases response, giving an arbitrarily close raw upper landing without using raw calibration.

For any fixed nonnull p, choose one fixed finite rotation L with E(Lp)=x+iy in that strict wedge. Since c preserves E, the same x,y apply to Lc^k p for all k. Choose a natural M>max(x+y,x−y)+1. Landing each Lc^k p with count tolerance one and applying dyadic count order gives

W(c^k p)≤W(Lc^k p)≤W(B(s_k,t_k))≤W(B(M,M)).

The right side is one finite real bound independent of k. The individual landing programs may depend on k. Zero and positive-null preparations already have constant orbits. Thus every c orbit is bounded above.

### The orbit supremum has exact transparency

Put W_k(p)=W(c^k p). These sequences are nonnegative, nondecreasing and bounded above. Define the finite real value

V(p)=sup over k in Nat of W_k(p).

Pointwise monotone convergence gives W_k(p)→V(p). The sequence and its one-step tail have the same supremum, so V(cp)=V(p). Also V(0)=0, W≤V, and V inherits universal prepared count order term by term. On positive-null preparations V=W=κ. Put v=V(1), so 1≤v<∞.

Fix a scalar depth j and natural n,m. For every k≥j put M_k=2^(k−j). The actual identity

c^k u^j=M_k h^k

follows from h=cu and 2u=1. Telescoping the supplied word mixed equation over an M_k-by-M_k rectangle gives its four-corner equality at the counts M_k n, M_k m. The identity converts these terms into the four values

W_k(u^j B(n+1,m+1)), W_k(u^j B(n+1,m)),

W_k(u^j B(n,m+1)), W_k(u^j B(n,m)).

Each preparation in this display is fixed while k tends to infinity. Their four finite limits give scalar-dyadic mixed zero for V. This is an exact rectangle identity followed by convergence at four fixed inputs.

Apply the original exact-transparency scalar first-five theorem to V/v. Its unit value is one, v is positive, and every other hypothesis has just been established. The conclusion gives V=vN on nonnull preparations and V=κ on positive-null preparations. In particular, on all nonnegative dyadic raw bags,

V(B(s,t))=F(s,t)=v(s²+t²)/2.

At this stage v remains an unknown number at least one. This application uses the original equality-based theorem directly, keeping the analytic dependency acyclic.

### Uniform convergence for changing raw inputs

For every fixed natural R≥1, W_k(B(s,t)) converges uniformly to F(s,t) over all dyadic (s,t) in [0,R]². The needed argument uses a finite grid and count order.

Given ε>0, choose a dyadic mesh δ with 2vRδ<ε/2 and grid endpoints including R. Pointwise convergence on this finite grid yields an index K such that every grid corner (a,b) has

0≤F(a,b)−W_k(B(a,b))<ε/2

for k≥K. For any dyadic (s,t) in the box, take its lower grid corner, with 0≤s−a<δ and 0≤t−b<δ, allowing equality at the box boundary. The quadratic formula gives

0≤F(s,t)−F(a,b)≤vR((s−a)+(t−b))<ε/2.

Spatial monotonicity and W_k≤V therefore give

0≤F(s,t)−W_k(B(s,t))

≤F(s,t)−F(a,b)+F(a,b)−W_k(B(a,b))<ε.

The estimate holds at every dyadic point of the box, including changing inputs with arbitrarily large denominators. It supplies the convergence needed for the following varying-source transfer. Continuity belongs to the deduced quadratic F in this argument. The response W retains precisely its supplied order laws.

### Quantitative paired programs for growing shadow ratio

Fix a nonnull p=(z,q) and one finite response-increasing rotation A=(α,β) so that the rational design coordinate z/α=u₀+iv₀ satisfies u₀>|v₀|>0. This quotient supplies design parameters. All preparations below are actual P elements.

For large k let p_k=c^(−k)p=(z,2^k q), q_k=2^k q, and λ_k=q_k/(βu₀)>1. Choose ε_k→0, 0<ε_k<1, and a positive dyadic t_k≤1 so small that

(λ_k−1)t_k<ε_k/(1+ε_k),

2u₀t_k/|v₀|<ε_k.

Apply the finite paired construction with λ_k and t_k, obtaining (R_k,Q_k), and define

η_k=(u₀−q_k R_k/(βQ_k))/v₀.

Its quantitative estimates give

n_k t_k²<(λ_k−1)t_k<ε_k/(1+ε_k),

1≤R_k<1+ε_k,

|η_k|≤(u₀/|v₀|)(K_k−1)≤2u₀t_k/|v₀|<ε_k.

Here K_k=(1+t_k)²/(1+t_k²) and λ_k/K_k≤Q_k/R_k<λ_k. Thus R_k→1 and η_k→0 even while λ_k grows. Each construction is finite. Its required program length may grow with k.

### An actual varying-source lower transfer

For large k, clear all rational denominators with a positive integer X_k so that

A_k=X_k(1+η_k), B_k=X_k(1−η_k)

and the two raw counts corresponding to

z_k=(X_k/R_k)(u₀+iv₀)(1+iη_k)

are positive natural numbers. Let r_k be that natural raw bag. Its shadow is

q(r_k)=Re z_k=(X_k/R_k)(u₀−v₀η_k)=X_k q_k/(βQ_k).

Both coordinates then prove the actual identity

A(R_k,Q_k) r_k=B(A_k,B_k)p_k.

Multiplying this identity by the actual c^k gives

A(R_k,Q_k)(c^k r_k)=B(A_k,B_k)p.

Every identity concerns actual P elements after integer denominator clearing. Set H_k=max(A_k,B_k)=X_k(1+|η_k|). Choose a positive dyadic d_k with

1−ε_k<d_k H_k≤1,

and put x_k=d_k r_k. Then d_k X_k→1 and

E(x_k)=(d_k X_k/R_k)(u₀+iv₀)(1+iη_k)→u₀+iv₀.

The raw counts of x_k converge to u₀+v₀ and u₀−v₀, both positive, so all sufficiently late x_k lie in one fixed compact raw box. Scaling the actual identity by d_k, using the response-increasing program and then prepared order with d_k A_k,d_k B_k≤1, gives

W_k(x_k)≤W(A(R_k,Q_k)(c^k x_k))

=W(B(d_k A_k,d_k B_k)p)≤W(p).

The c powers have been moved inside an algebraic identity. The proof uses the actual response values at c^k x_k.

Uniform raw convergence on that fixed box now gives

W_k(x_k)−vN(x_k)→0,

W_k(x_k)→vN(p)/|α|².

For this fixed rotation A, W(p)≥vN(p)/|α|² follows. Choose a sequence of finite Euler rotations A_j whose design coordinate stays in the strict nonaxis right wedge and whose |α_j|² tends to one. Applying the already established fixed-A bound to each j and then taking that separate numerical limit gives W(p)≥vN(p). The upper inequality W(p)≤V(p)=vN(p) gives equality. Applying it to p=1 fixes v=1.

### Converse and the sixth local test

The positive-null constant κ≥0 was deduced before the supremum construction. Together with the nonnull result and W(0)=0 it gives the stated full classification. Conversely, each W_κ=N+κδ satisfies the five word schemas. Its prepared formula is

W_κ(B(n,m)p)=((n²+m²)/2)N(p)+κδ(p) indicator(n+m>0).

The nonnegative count factors are coordinatewise nondecreasing. c preserves N and δ. On every word raw grid the exceptional term vanishes and the response is 4^(−k)(n²+m²)/2, whose mixed defect is zero. Thus the classification includes the converse.

W(T)=0 selects κ=0. Before that sixth schema, the classification already gives global exact c transparency, and h^k=c^k u^k then gives scalar/word response equality and scalar-grid mixed zero. Since aT=bT=cT and the null-sector response equality was deduced directly, the T-origin defect is −W(T). The sixth schema therefore also has the single local-test presentation.

The word-only question is analytically settled under these exact hypotheses. The earlier six-schema omission certificates concern their stated exact-transparency families and retain that scope. The new theorem's formalization obligations include the uncalibrated orbit bound, exact supremum transfer, finite word rectangles, uniform raw convergence, variable-ratio program estimates, actual changing-source identities and the final normalization. They are recorded in the Lean research ledger with empty checked evidence. Real-valued output, the exact carrier prerequisite and universal availability of the stated mathematical preparation contexts remain explicit assumptions. Physical origins, detector and probability interpretation retain their separate obligations. [Authoritative analytic tasks](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean) · [Physical scope boundary](150-physical-scope-boundary.md)
