## 35. Weak-Gravity Input Ledger

This section is an anti-fit control ledger for the weak-gravity closure route.

It lists every input that must be obtained before the theory may claim a prediction for \(G_I\).

Status:

`weak_gravity_input_ledger_initialized`

### 35.1. Closure expression

The current minimal symbolic output is:

$$
G_I
=
\frac{c_I^4D_S}
{4\pi\kappa_{\chi,I}n_Lx_0^2\ell_0^2}.
$$

This expression is useful only if the denominator is obtained without \(G_N\).

Status:

`minimal_G_expression_recorded`

### 35.2. Input table

| Input | Meaning | Allowed source | Forbidden source | Status |
|---|---|---|---|---|
| \(c_I\) | clock/causal speed scale | clock/causal readout | gravitational fit | partially reconstructed |
| \(D_S\) | spatial dimension | order/count scaling | assumed Euclidean background | target \(3\) |
| \(\ell_0\) | link readout length | order/count/clock reconstruction | Planck length built from \(G_N\) | open |
| \(n_L\) | link density | event-density calibration \(\lambda_I\), mean degree \(z_I\) | Newtonian source fit | reduced to order/count geometry |
| \(x_0\) | dimensionless kernel response | \(K_{\eta,EF}(s)\) / \(\Gamma_I\) response | chosen to match \(G_N\) | open |
| \(\kappa_{\chi,I}\) | physical clock-strain cost scale | update action / clock-vacuum response | \(c^4/(4\pi G_N)\) | routes localized |

Status:

`weak_gravity_inputs_classified`

### 35.3. Hidden-fit tests

For each proposed derivation of an input \(p\), run:

$$
\frac{\partial p}{\partial G_N}
=
0
$$

at the level of definitions.

If:

$$
p
=
p(G_N)
$$

directly or through Planck units, the route is not predictive.

Planck length is forbidden as primitive here because:

$$
\ell_P
=
\sqrt{\frac{\hbar G_N}{c^3}}
$$

already contains \(G_N\).

Status:

`hidden_G_input_test_defined`

### 35.4. First computable subproblem

The least contaminated next input is:

$$
x_0.
$$

Reason:

it is dimensionless and can in principle be computed from normalized kernel response:

$$
X_\eta
=
\left.
\partial_s
\left[
-
\log
\frac{\Omega_{\eta,EF}(s)}
{\Omega_{\eta,EF}(0)}
\right]
\right|_{s=0}.
$$

The second input is:

$$
D_S,\lambda_I,n_L,\ell_0
$$

from order/count geometry.

The hardest input is:

$$
\kappa_{\chi,I}
$$

because it carries the physical cost dimension.

Status:

`next_input_priority_defined`

### 35.5. Publication readiness effect

With this ledger, the weak-gravity route is more controlled but not yet Mode C.

Current status:

$$
\text{symbolic closure expression}
$$

not:

$$
\text{numerical prediction}.
$$

Mode C begins only after at least one open input is computed from primitives and then used in an independent gate without refit.

Status:

`mode_C_still_not_reached`

### 35.6. What is closed

This section closes a potential AI failure mode:

$$
\text{hiding }G_N\text{ in a new symbol}.
$$

Every weak-gravity closure input now has an allowed source and a forbidden source.

It does not yet derive:

1. why the physical kernel must choose the minimal \(x_0=1\) sector;
2. \(\kappa_{\chi,I}\);
3. \(z_I,q_{V,I},\ell_0\);
4. numerical \(G_I\).

Next target:

derive \(x_0\) from a normalized positive kernel model.

Normalized positive kernel model:

`sections/36-normalized-positive-kernel-model.md`

Order-count link density:

`sections/37-order-count-link-density.md`

Clock-strain cost scale:

`sections/38-clock-strain-cost-scale.md`

Status:

`weak_gravity_anti_fit_control_added`
