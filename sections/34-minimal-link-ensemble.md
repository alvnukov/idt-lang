## 34. Minimal Link Ensemble

This section gives the first computable symbolic link ensemble.

It does not compute \(G_N\).

It exposes the remaining dimensional scale needed before a numerical \(G_I\) can be predicted.

Status:

`minimal_link_ensemble_initialized`

### 34.1. Dimensionless response ensemble

Take the minimal reciprocal two-mode link:

$$
\mathcal U_{EF}
=
\{\eta_+,\eta_-\},
$$

with:

$$
\Omega_+=\Omega_-,
\qquad
X_+=x_0,
\qquad
X_-=-x_0,
\qquad
Y_\pm=0.
$$

Then:

$$
\langle X\rangle_{EF}=0,
$$

and:

$$
\bar a_{EF}
=
\operatorname{Var}_{EF}(X)
=
x_0^2.
$$

The bar marks dimensionless stiffness from the kernel cumulant.

Status:

`minimal_reciprocal_two_mode_link`

### 34.2. Physical stiffness scale

The physical clock-strain cost requires a scale:

$$
\kappa_{\chi,I}.
$$

Define:

$$
a_{EF}^{\mathrm{phys}}
=
\kappa_{\chi,I}\bar a_{EF}.
$$

Therefore:

$$
\alpha_I
=
\kappa_{\chi,I}\bar\alpha_I.
$$

The theory must not hide \(G_N\) inside \(\kappa_{\chi,I}\).

The scale \(\kappa_{\chi,I}\) must be derived from primitive update action, clock-network vacuum response, or declared as an irreducible bridge constant.

Status:

`physical_stiffness_scale_exposed`

### 34.3. Isotropic coarse-graining

For a locally isotropic spatial domain \(U\), define link density:

$$
n_L(U)
=
\frac{N_L(U)}
{\nu_{G,S}(U)}.
$$

Assume equal link length:

$$
|\ell_{EF}|=\ell_0.
$$

Then:

$$
\bar\alpha_I
=
\frac{1}{D_S}
n_L
x_0^2
\ell_0^2
$$

in the minimal isotropic sector.

Thus:

$$
\alpha_I
=
\kappa_{\chi,I}
\frac{n_Lx_0^2\ell_0^2}{D_S}.
$$

Status:

`symbolic_alpha_from_minimal_link_ensemble`

### 34.4. Symbolic G output

The weak-gravity output becomes:

$$
G_I
=
\frac{c_I^4}{4\pi\alpha_I}
=
\frac{c_I^4D_S}
{4\pi\kappa_{\chi,I}n_Lx_0^2\ell_0^2}.
$$

This is not yet a numerical prediction.

It is a non-refit symbolic closure expression.

It identifies exactly what must be computed without gravitational data:

$$
\kappa_{\chi,I},
\quad
n_L,
\quad
x_0,
\quad
\ell_0,
\quad
D_S.
$$

Status:

`symbolic_G_expression_obtained`

### 34.5. No-fitting constraints

The following are forbidden:

1. choosing \(x_0\) from measured \(G_N\);
2. choosing \(n_L\) from measured \(G_N\);
3. choosing \(\ell_0\) from Planck length if Planck length was itself built from \(G_N\);
4. choosing \(\kappa_{\chi,I}\) from Newtonian gravity;
5. adjusting any one of these after lensing or WEP comparison.

Allowed:

1. derive \(n_L,\ell_0,D_S\) from order/count geometry;
2. derive \(x_0\) from kernel response;
3. derive \(\kappa_{\chi,I}\) from update action or clock-vacuum response;
4. compare the resulting \(G_I\) to \(G_N\).

Status:

`minimal_link_no_fit_constraints`

### 34.6. What is closed

This section closes:

$$
\mathcal U_{EF},X_\eta
$$

as purely abstract symbols in the first test sector.

It provides the minimal reciprocal ensemble:

$$
X=\{\pm x_0\}
$$

and symbolic output:

$$
G_I
=
\frac{c_I^4D_S}
{4\pi\kappa_{\chi,I}n_Lx_0^2\ell_0^2}.
$$

It does not yet derive:

1. \(x_0\);
2. \(\kappa_{\chi,I}\);
3. \(n_L\);
4. \(\ell_0\);
5. numerical \(G_I\).

Next target:

derive or constrain \(\kappa_{\chi,I}\) from primitive update action and clock-vacuum response.

Weak-gravity input ledger:

`sections/35-weak-gravity-input-ledger.md`

Order-count link density:

`sections/37-order-count-link-density.md`

Clock-strain cost scale:

`sections/38-clock-strain-cost-scale.md`

Status:

`minimal_link_ensemble_gap_reduced`
