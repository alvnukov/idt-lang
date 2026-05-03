## 20. Clock-Network Calculator

This section turns clock-rate variables into a compressed calculator.

It is designed for weak-field clock networks, redshift tests, free-fall inference, and residual detection.

Status:

`clock_network_calculator_initialized`

### 20.1. Minimal clock packet

For clock \(C\) at readout node \(E_i\), define:

$$
\mathcal K_i^C
=
\left(
r_C(E_i),
r_{C,\infty},
\sigma_C(E_i),
\delta_C(E_i)
\right).
$$

Here:

1. \(r_C(E_i)\) is measured clock rate;
2. \(r_{C,\infty}\) is flat/reference calibration;
3. \(\sigma_C\) is stochastic/statistical uncertainty;
4. \(\delta_C\) is declared non-universal residual.

The compressed universal clock factor is:

$$
\chi_i
=
\frac{r_C(E_i)}{r_{C,\infty}}
$$

only after clock universality gates are satisfied.

Status:

`clock_packet_defined`

### 20.2. Potential readout

Define:

$$
\Phi_I(E_i)
=
c_I^2\log\chi_i.
$$

For two nodes:

$$
\Delta\Phi_{ij}
=
c_I^2\log
\frac{\chi_i}{\chi_j}.
$$

The redshift prediction is:

$$
\frac{\nu_i-\nu_j}{\nu_j}
\approx
\frac{\Phi_I(E_i)-\Phi_I(E_j)}{c_I^2}
$$

in the weak-field domain.

This uses clocks as direct potential sensors.

Status:

`clock_rates_to_potential_readout`

### 20.3. Clock universality residual

For two clock species \(C,C'\), define:

$$
\mathcal U_{CC'}(i,j)
=
\log
\frac{
r_C(E_i)r_{C'}(E_j)
}{
r_C(E_j)r_{C'}(E_i)
}.
$$

Clock universality requires:

$$
\mathcal U_{CC'}(i,j)
\to
0.
$$

A nonzero value is not absorbed into \(\Phi_I\).

It is a physical residual:

$$
\mathcal R_{\mathrm{LPI}}
=
\mathcal U_{CC'}.
$$

Known gate:

local position invariance / clock comparison tests bound clock-species residuals.

Status:

`clock_universality_residual_calculator`

### 20.4. Acceleration inference

Given spatial readout coordinates \(x^i\), infer:

$$
a_I^i(x)
=
-
\partial_i\Phi_I(x).
$$

For discrete clock network nodes:

$$
a_I^i(E_k)
\approx
-
\nabla_i^{\mathrm{net}}\Phi_I(E_k).
$$

Known gate:

slow free-fall acceleration in weak fields is:

$$
\ddot x^i
=
-
\partial_i\Phi.
$$

The calculator predicts free-fall from clock data, not from a fitted metric.

Status:

`clock_potential_to_freefall_inference`

### 20.5. Source residual

Compute the source-law residual:

$$
\mathcal R_{\rho}
=
\Delta_S\Phi_I
-
4\pi G_I\rho_I^G.
$$

If:

$$
\mathcal R_{\rho}=0
$$

within uncertainty, the Newtonian source gate is passed.

If:

$$
\mathcal R_{\rho}\neq0,
$$

the residual must be assigned to one of:

1. missing baryonic/source model;
2. non-Newtonian weak-field residual;
3. dark-sector effective source;
4. clock-systematic residual;
5. invalid weak-field domain.

Status:

`clock_network_source_residual`

### 20.6. Light and spatial curvature gate

Clock rates determine \(g_{00}\)-like readout.

They do not by themselves fix spatial curvature.

Introduce PPN spatial factor:

$$
\gamma_I^{\mathrm{PPN}}.
$$

Light bending and Shapiro gates require:

$$
\gamma_I^{\mathrm{PPN}}
\to
1
$$

in the no-residual GR weak-field sector.

Clock-network calculator therefore outputs:

$$
\left(
\Phi_I,\mathcal R_{\mathrm{LPI}},\mathcal R_\rho,
\gamma_I^{\mathrm{PPN}}\text{ target}
\right),
$$

not a full metric unless the spatial-curvature gate is passed.

Status:

`clock_calculator_does_not_hide_spatial_curvature_gap`

### 20.7. Combined residual packet

The clock-network residual packet is:

$$
\mathcal R_{\mathrm{clock}}
=
\left(
\mathcal R_{\mathrm{LPI}},
\mathcal R_{\rho},
\mathcal R_{\mathrm{boost}},
\mathcal R_{\mathrm{loop}},
\mathcal R_{\gamma}
\right).
$$

Interpretation:

1. \(\mathcal R_{\mathrm{LPI}}\): clock species non-universality;
2. \(\mathcal R_{\rho}\): source-law mismatch;
3. \(\mathcal R_{\mathrm{boost}}\): kinematic time-dilation mismatch;
4. \(\mathcal R_{\mathrm{loop}}\): non-integrable clock-rate loop;
5. \(\mathcal R_{\gamma}\): spatial-curvature / null-propagation mismatch.

Status:

`clock_network_residual_packet`

### 20.8. Computational advantage criterion

The calculator is useful when:

$$
\mathrm{Cost}(\chi,\Phi_I,\mathcal R_{\mathrm{clock}})
<
\mathrm{Cost}(g_{\mu\nu}\text{ fit})
$$

for clock-network data, or when it exposes residuals hidden by a metric fit.

It must reproduce:

1. gravitational redshift;
2. kinematic time dilation;
3. Newtonian free fall;
4. Poisson source law in the validated domain;
5. clock universality bounds;
6. PPN \(\gamma\) targets for null propagation.

Status:

`clock_network_calculator_acceptance_rule`

### 20.9. What v5.21 closes

This section provides a compressed gravity/clock calculator:

$$
r_C(E_i)
\Rightarrow
\chi_i
\Rightarrow
\Phi_I(E_i)
\Rightarrow
\left(
\Delta\nu/\nu,
a_I,
\mathcal R_\rho,
\mathcal R_{\mathrm{LPI}}
\right).
$$

It remains conditional because:

1. clock universality must be checked;
2. spatial curvature / \(\gamma_I^{\mathrm{PPN}}\) is not derived from clocks alone;
3. source density \(\rho_I^G\) must be independently reconstructed;
4. strong-field domains are not covered.

Next target:

derive the spatial-curvature compressed variable that pairs with \(\Phi_I\) and closes light bending / Shapiro gates.

Status:

`clock_network_compressed_calculator_defined`

Spatial-curvature partner calculator:

`sections/21-spatial-curvature-calculator.md`
