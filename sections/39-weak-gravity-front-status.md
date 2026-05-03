## 39. Weak-Gravity Front Status

This section summarizes the current weak-gravity closure state after the link-density and cost-scale reductions.

Geometry inputs after later reduction are tracked in:

`sections/42-geometry-input-front-status.md`

Status:

`weak_gravity_front_status_initialized`

### 39.1. Current symbolic result

In the minimal normalized positive-kernel sector:

$$
x_0=1.
$$

The order/count link-density reduction gives:

$$
n_L\ell_0^2
=
\frac{z_Iq_{V,I}}{2\ell_0}.
$$

Therefore:

$$
G_I
=
\frac{c_I^4D_S\ell_0}
{2\pi\kappa_{\chi,I}z_Iq_{V,I}}.
$$

This is the current strongest symbolic weak-gravity closure expression.

Status:

`current_symbolic_G_front`

### 39.2. Closed vs open inputs

| Input | Current status |
|---|---|
| \(x_0\) | closed only in minimal normalized two-mode sector |
| \(n_L\ell_0^2\) | reduced to \(z_I,q_{V,I},\ell_0\) |
| \(z_I\) | reduced to mean spatial adjacency degree |
| \(q_{V,I}\) | reduced to reconstructed cell-volume shape factor |
| \(\ell_0\) | reduced to clock-radar distance per order-distance unit |
| \(\kappa_{\chi,I}\) | open physical cost scale with two declared routes |
| \(D_S\) | target \(3\), not derived exactly |

Status:

`weak_gravity_inputs_status_table`

### 39.3. What would make this predictive

The route becomes Mode C only if:

$$
z_I,\quad q_{V,I},\quad \ell_0,\quad \kappa_{\chi,I}
$$

are fixed without gravitational data, and then:

$$
\left|
\frac{G_I-G_N}{G_N}
\right|
\le
\epsilon_G.
$$

If \(G_I\) fails the gate, the result is still useful if the sign/form of the residual was fixed before comparison.

Status:

`mode_C_condition_restated`

### 39.4. Anti-fit checks passed

Current front explicitly forbids:

1. Planck length as primitive \(\ell_0\);
2. \(c^4/(4\pi G_N)\) as primitive \(\kappa_{\chi,I}\);
3. choosing \(z_I,q_{V,I}\), or \(x_0\) from \(G_N\);
4. changing the link neighbourhood after WEP/lensing comparison;
5. calling the symbolic expression a numerical prediction.

Status:

`current_front_anti_fit_checks`

### 39.5. Next best route

The geometry route has been reduced to readout invariants:

$$
z_I,q_{V,I},\ell_0
\Leftarrow
\text{order/count/clock distance reconstruction}.
$$

The hardest route remains:

$$
\kappa_{\chi,I}
\Leftarrow
\text{update action or clock-vacuum response}.
$$

Recommended next step:

derive \(\kappa_{\chi,I}\) from update action or clock-vacuum response, while keeping the geometry residuals fixed before any \(G_N\) comparison.

Status:

`next_route_kappa_after_geometry`
