# Detector scale under literal process composition

## A continuous response countercontrol

On the literal initial carrier P4, let `E` be the existing complex coordinate
and `N(p)=Complex.normSq(E(p))`. Define

`D={0} union {2^k | k is an integer}`,
`f(x)=x+(1/2)*infDist(x,D)`, and `W(p)=f(N(p))`.

The profile is continuous and strictly increasing, has `f(0)=0`, `f(1)=1`,
and obeys exact dyadic scaling `f(2*x)=2*f(x)`. The response satisfies all
four fields of `InitialColumnOrderReadoutCore.BaseContract`

- `W(1)=1`.
- `W(a*p)+W(b*p)=W(p)` for every preparation.
- `W(c*p)>=W(p)` for `c=2*a*b` and every preparation.
- For `B(n,m)=n*a+m*b`, natural `n<=n'`, `m<=m'` and every `p` imply
  `W(B(n,m)*p)<=W(B(n',m')*p)`.

This specific detector also satisfies exact `W(c*p)=W(p)`.

It depends only on `E`, admits a continuous detector formula on the ambient
complex plane, preserves null insertion and assigns zero to every finite
sum of coordinate-null preparations.

Native branch gains also hold on every input. For natural `m,n`,

`W(a^m*b^n*p)=(1/2)^(m+n)*W(p)`.

## Exact algebraic action and detector mismatch

The literal action `M_p(s)=p*s` is injective in its coefficient `p`.
It has identity action, exact serial composition
`M_(p*q)(s)=M_p(M_q(s))`, coherent addition and input distributivity.
These action identities coexist with the following numerical response

| Quantity at the actual preparation `p=1+a` | Value |
| --- | --- |
| `N(p)` | `5/2` |
| `N(p^2)` | `25/4` |
| `W(p)` | `11/4` |
| `W(p^2)` | `57/8` |
| `W(p)^2` | `121/16` |

`InitialDyadicDetectorCountermodel.process_square_countercontrol` combines
exact repeated process composition with this numerical square mismatch.
The response differs from `N` and fails global numerical multiplicativity.
The profile and native word gains therefore leave a detector-gain bridge
for arbitrary coherent operations.

The mathematical countercontrol retains literal carrier elements and a
faithful coefficient action. A complete probabilistic operational model,
physical detector realization and copying require separate contracts.

## Analytic fixed-tripler selection route

A separately accepted analytic argument adds one stationary law to the
same four-field BaseContract

`W((3:P4)*p)=W(3)*W(p)` for every actual preparation `p`.

It gives `W=N` and forces `W(3)=9`. The argument calibrates the gain using
count sandwiches, then uses near-collisions of powers of two and three to
obtain exact count homogeneity. Dyadic comparisons give coordinate
extensionality. A rational-cone Lipschitz estimate and finite small-angle
comparisons then establish continuity and isotropy.

Continuity, radial factorization and gain nine emerge within this analytic
argument. Its Lean artifacts and kernel review remain pending. The three
planned modules concern tripler count calibration, count-homogeneous
selection and final stationary-tripler selection.

The dyadic detector response above satisfies BaseContract and fails this
extra tripler law. The algebraic shadow `q` supplies a separate analytic
control with tripler gain three and a failed `c` comparison. An angular
control retains column, `c` and tripler laws while failing full prepared
count order. These controls retain their analytic status in the new plan.

Under BaseContract, both square and tripler contracts select the same
numerical model. The tripler law concerns a single fixed coherent multiplier
on every input. A physical interpretation of that operation and its gain
requires an independent bridge. Independent trials and physical copying
have their own operational contracts.

Detector-gain origin and the scalar-process versus actual-preparation
interface remain open. Born actualization, Hilbert reconstruction, full QM,
GR and physical-scale origins remain open.
