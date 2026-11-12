# Initial echo context and independence boundaries

## Exact arithmetic interface

The existing initial semiring P4 has `a+b=1`, `a^4=b^4`, canonical generator
swap `J` and algebraic echo `echo(p)=p*J(p)`.
`InitialEchoContextObstruction.Expr` is finite syntax containing exactly an
input, arbitrary fixed carrier constants, addition and multiplication.
Any finite number of syntactic input occurrences is allowed. Target agreement
means exact equality in the full carrier.

Every expression preserves fibres of every semiring homomorphism. The map
`chi:P4 -> ZMod 5` with `chi(a)=2`, `chi(b)=4` identifies the distinct inputs
`a` and `2`, whose target images are

| Input | `chi(input)` | `chi(J(input))` | `chi(echo(input))` |
| --- | --- | --- | --- |
| `a` | 2 | 4 | 3 |
| `2` | 2 | 2 | 4 |

Every expression therefore fails simultaneous exact agreement with either
target on these two inputs. Global implementations are excluded within this
language. A fixed constant expression matches every prescribed singleton
test, establishing minimal test-set size for this obstruction.

The core declarations in `Proofs/QMClosure/InitialEchoContextObstruction.lean`
are `Expr.eval_preserves_fibres`, `no_two_point_J`, `no_two_point_echo`,
`no_global_J_expression`, `no_global_echo_expression`, `two_ne_a`,
`one_point_J` and `one_point_echo`.

This modestly extends `FiniteScalarReversalBoundary` to all parameterized
expressions in the declared arithmetic language. The existing
`TransparentFourthReflectionEcho` supplies the mathematical generator swap.
The homomorphism is an algebraic proof witness. Physical distinguishability,
repeated-input resources, syntax-to-DAG compilation and known-recipe access
require separate contracts. Measurement, adaptive branching, division,
inversion and environmental operations require a richer language.

For `N(p)=Complex.normSq(E(p))`, squaring satisfies `N(p*p)=N(echo(p))`
for every input. Adding the fixed reference one at `a` gives `5/4` for
`N(1+a*a)` and `9/4` for `N(1+echo(a))`.
`square_matches_echo_normSq` and `fixed_reference_separates_square_echo`
record these comparisons. `normSq_two` gives `N(2)=4`, so physical success
probabilities require a specified bounded domain and normalization contract.

## Independent-trial countercontrol

The following second result is accepted analytically and awaits Lean
formalization. For `x>0`, write `x=2^k*u` with integer `k` and `1<=u<2`.
Define `f(0)=0`, `f(x)=2^k*F(u)` and

| Range | `F(u)` |
| --- | --- |
| `1<=u<=3/2` | `(u+1)/2` |
| `3/2<=u<2` | `(3*u-2)/2` |

The function is continuous and strictly increasing, with `f(1)=1`,
`f(2*x)=2*f(x)` and `0<=f(x)<=x`. The response `W(p)=f(N(p))` satisfies
all four non-echo laws of `InitialColumnOrderEchoSelection.Contract`

- Unit normalization holds.
- Both column responses are `W(p)/2`, giving column conservation.
- Since `N(c)=1`, multiplication by `c=2*a*b` preserves the response.
- The prepared-count identity
  `N(B(n,m)*p)=((n*n+m*m)/2)*N(p)` and monotonicity give prepared order.

For the actual preparation `p=(a+2*b)*a*h`, where `h=a*b` and `q` is the
existing shadow, the exact values are

| Preparation | `E` | `q` | `N` | `W` |
| --- | --- | --- | --- | --- |
| `p` | `(2+i)/4` | `3/16` | `5/16` | `9/32` |
| `echo(p)` | `5/16` | `9/256` | `25/256` | `43/512` |

Both preparations satisfy `N<=1` and `q<=1`. One fixed classical
rational-register detector computes the dyadic value `f(N)` and samples
Bernoulli success with finitely many fresh fair bits on the bounded dyadic
domain. Its unit success is one. Independent repeats have joint success
`(9/32)^2=81/1024`, while the compiled echo has success `86/1024`.
The exact defect is `5/1024`.

For `M,d ∈ ℕ` with `x=M/2^d` and `0<=x<=1`, `M>0`, let `L` be the
largest power of two at most `M`. Then `f(x)` has numerator `M+L` if
`2*M<=3*L`, else `3*M-2*L`,
over `2^(d+1)`, using at most `d+1` fair bits under the supplied encoding.
`M=0` outputs zero deterministically.

This supplied classical detector is an analytic countermodel. Its physical
realization within IDT and its shared computation of `N` remain supplied
origin obligations. The finite fair-bit
construction applies to the concrete dyadic control. For any nonnegative
real raw response, a separately idealized finite-support kernel
`C_p=floor(W(p))+Bernoulli(frac(W(p)))` has mean `W(p)`.
Independent such counts give a product mean while leaving the compiled
echo response unrestricted. Global raw responses can exceed one.

With positive raw normalization scales `S_A>0`, `S_B>0` and `S_E>0`, equality
of normalized product and echo probabilities gives
`W(echo(p))=S_E/(S_A*S_B)*W(p)*W(J(p))`.
A common scale `S>0` leaves the factor `1/S`.

## Attenuation and the remaining origin question

The following attenuation argument also remains analytic. The four
non-echo laws give `W(h^k*p)=4^(-k)*W(p)` for natural `k`.
Since `J(h)=h`, `echo(h^k*p)=h^(2*k)*echo(p)`.
Echo equality at one point of every forward `h` orbit implies global echo
by cancellation of the common factor `4^(-2*k)`.

The domains `W<=1`, `q<=1`, `N<=1` and their intersection meet every such
orbit analytically. Restricting the law to these domains transfers the
physical obligation to universally calibrated attenuation and sufficient
available depth. A `q<=1` cutoff permits `N=4` at actual coordinates `(2,1)`.
Existence of an attenuated point with `W<=1` leaves calibrated depth
selection for an opaque source open.

Reset and independent trials yield a product mean. Identifying that reset
process with coherent algebraic echo requires an independent operational
relation and raw accounting. The next question concerns independently
motivated locality, resources or an actual native rewrite explaining this
relation. Each test must state its origin-obligation delta, action motivation,
falsifier or route-stop criterion and added premises. A new law simply
restating multiplicativity or self-echo stops that route.

The conditional selection theorem retains its existing contract. Physical
operation libraries, response-comparison contracts, primitive origins,
Born actualization, Hilbert reconstruction, full QM, GR and physical-scale
origins remain open.
