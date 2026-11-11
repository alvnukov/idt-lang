# Scaled-count readout reconstruction

This analytic conditional reconstruction awaits Lean formalization. Its checked-evidence list remains empty. It uses the exact initial normal form and six supplied response schemas. [Analytic task](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean) · [Checked initial normal form](../Proofs/QMClosure/TransparentFourthInitialNormalForm.lean)

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
