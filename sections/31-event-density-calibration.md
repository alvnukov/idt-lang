## 31. Event-Density Calibration

This section targets:

$$
\nu_{\mathrm{count}}(U)
\approx
\lambda_I\nu_G^{(d)}(U).
$$

It does not assume continuum volume as primitive.

It defines how \(\lambda_I\) can be calibrated or derived from order/count/clock readout.

Status:

`event_density_calibration_initialized`

### 31.1. The gap

Volume reconstruction separated:

$$
\nu_{\mathrm{count}}
\neq
\nu_G.
$$

But source density and stiffness still require a map:

$$
\nu_{\mathrm{count}}
\Rightarrow
\nu_{G,S},
\qquad
\nu_G^{(4)}.
$$

The missing coefficient is:

$$
\lambda_I^{(d)}.
$$

Status:

`lambda_gap_declared`

### 31.2. Counting law

For a reconstructed \(d\)-dimensional domain \(U\):

$$
N_I(U)
=
\nu_{\mathrm{count}}(U).
$$

The event-density calibration is:

$$
\lambda_I^{(d)}(U)
=
\frac{N_I(U)}{\nu_G^{(d)}(U)}.
$$

In a stable flat readout domain:

$$
\lambda_I^{(d)}(U)
\to
\lambda_{I,0}^{(d)}.
$$

Status:

`lambda_as_count_volume_ratio`

### 31.3. Dimension extraction

Before \(\lambda_I\) can be constant, dimension must be stable.

Define scale exponent:

$$
D_{\mathrm{eff}}(R)
=
\frac{d\log N_I(B_R)}{d\log R}.
$$

Spatial readiness requires:

$$
D_{\mathrm{eff}}(R)
\to
3
$$

on the weak-field spatial domain.

Causal diamond readiness requires:

$$
D_{\mathrm{eff}}(\tau)
\to
4
$$

on the spacetime readout domain.

Status:

`dimension_before_lambda_gate`

### 31.4. Lambda residual

Define:

$$
\mathcal R_\lambda^{(d)}(U)
=
\frac{\lambda_I^{(d)}(U)-\lambda_{I,0}^{(d)}}
{\lambda_{I,0}^{(d)}}.
$$

If:

$$
\mathcal R_\lambda^{(d)}\neq0,
$$

then source density, stiffness density, and geometric volume all inherit a volume residual.

This residual must not be hidden as dark matter, dark energy, or modified \(G\) unless its functional form is declared before data comparison.

Status:

`lambda_residual_declared`

### 31.5. Coupling to stiffness

The stiffness density is:

$$
A_I^{ij}(U)
=
\frac{1}{\nu_{G,S}(U)}
\sum_{\langle EF\rangle\subset U}
a_{EF}\ell_{EF}^i\ell_{EF}^j.
$$

Using:

$$
\nu_{G,S}(U)
=
\frac{N_I(U)}{\lambda_I^{(3)}(U)},
$$

we get:

$$
A_I^{ij}(U)
=
\frac{\lambda_I^{(3)}(U)}{N_I(U)}
\sum_{\langle EF\rangle\subset U}
a_{EF}\ell_{EF}^i\ell_{EF}^j.
$$

Thus \(\lambda_I\) affects \(\alpha_I\) and therefore \(G_I\).

It cannot be calibrated independently after \(G_I\) is tested.

Status:

`lambda_coupled_to_stiffness`

### 31.6. Coupling to source density

For source-weighted activity:

$$
M_I(U)
=
\sum_{\eta\in U}m_I(\eta),
$$

spatial density becomes:

$$
\rho_I^G(U)
=
\frac{M_I(U)}{\nu_{G,S}(U)}
=
\lambda_I^{(3)}(U)
\frac{M_I(U)}{N_I(U)}.
$$

Thus a variation in \(\lambda_I^{(3)}\) can mimic a source residual.

The theory must declare whether:

$$
\mathcal R_\lambda
$$

is zero, bounded noise, or a physical residual.

Status:

`lambda_coupled_to_source_density`

### 31.7. No-refit lambda gate

The same \(\lambda_I^{(d)}\) calibration must be used for:

1. volume reconstruction;
2. source density;
3. stiffness density;
4. clock-network coarse-graining;
5. lensing/dynamics residual analysis.

If a different \(\lambda_I\) is needed for different gates, the geometry reconstruction fails.

Status:

`lambda_no_refit_gate`

### 31.8. What is closed

This section closes:

$$
\lambda_I
\quad
\text{as an unexamined conversion factor.}
$$

It replaces it with:

$$
\lambda_I^{(d)}(U)
=
\frac{\nu_{\mathrm{count}}(U)}{\nu_G^{(d)}(U)}
$$

plus dimension, residual, stiffness, source, and no-refit gates.

It does not yet derive:

1. exact \(D_S=3\);
2. exact \(D_G=4\);
3. constant \(\lambda_I^{(d)}\);
4. Lorentzian signature;
5. continuum limit from primitive order alone.

Next target:

derive stable \(D_G=4\) and constant \(\lambda_I\) from inherited order/count dynamics.

Status:

`lambda_calibration_gap_reduced`
