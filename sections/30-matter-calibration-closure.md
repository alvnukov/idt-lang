## 30. Matter Calibration Closure

This section targets:

$$
\sigma_{\Phi,I}^G
\to
\rho_m c_I^2.
$$

It does not assume mass as primitive.

It defines the conditions under which inherited source response, passive clock coupling, and inertial response are the same packet property.

Status:

`matter_calibration_closure_initialized`

### 30.1. Three mass-like readouts

For a localized admissible matter packet \(P\), define:

1. kinetic coefficient:

$$
m_{\mathrm{kin},I}(P)
=
\left.
\frac{\partial^2 L_P}{\partial v^2}
\right|_{v=0};
$$

2. passive gravitational coefficient:

$$
m_{\mathrm{grav},I}(P)
=
\left.
\frac{\partial C_P}{\partial \Phi_I}
\right|_{\Phi=0};
$$

3. active source coefficient:

$$
m_{\mathrm{src},I}(P)
=
\frac{q_{\Phi,I}(P)}{\beta_I}.
$$

These are not assumed equal.

They are three readouts of the same inherited packet only if a closure gate is passed.

Status:

`three_mass_like_readouts_separated`

### 30.2. Packet generator closure

Let the packet have one effective update generator:

$$
\mathcal K_P(\chi,v,\varphi)
$$

with:

$$
\varphi=\log\chi.
$$

The closure condition is that kinetic, passive, and active responses are derivatives of the same generator:

$$
m_{\mathrm{kin},I}
\leftarrow
\partial_v^2\mathcal K_P,
\qquad
m_{\mathrm{grav},I}
\leftarrow
\partial_\varphi\mathcal K_P,
\qquad
q_{\Phi,I}
\leftarrow
\partial_\varphi\mathcal C_P.
$$

The matter bridge closes only if these derivatives are not independently adjustable.

Status:

`single_packet_generator_condition`

### 30.3. Calibration equation

Define inertial matter density on a spatial clock slice:

$$
\rho_{\mathrm{kin},I}(U)
=
\frac{1}{\nu_{G,S}(U)}
\sum_{P\subset U}
m_{\mathrm{kin},I}(P).
$$

Define source response density:

$$
\sigma_{\Phi,I}^G(U)
=
\frac{1}{\nu_{G,S}(U)}
\sum_{P\subset U}
q_{\Phi,I}(P).
$$

The target calibration is:

$$
\sigma_{\Phi,I}^G
\to
\rho_{\mathrm{kin},I}c_I^2.
$$

Equivalently, packet by packet:

$$
q_{\Phi,I}(P)
\to
m_{\mathrm{kin},I}(P)c_I^2.
$$

Status:

`matter_calibration_equation_defined`

### 30.4. Equivalence residual triad

Define:

$$
\epsilon_{\mathrm{passive},I}(P)
=
\frac{m_{\mathrm{grav},I}(P)}
{m_{\mathrm{kin},I}(P)}
-
1,
$$

and:

$$
\epsilon_{\mathrm{active},I}(P)
=
\frac{m_{\mathrm{src},I}(P)}
{m_{\mathrm{kin},I}(P)}
-
1.
$$

The total weak equivalence residual is:

$$
\epsilon_{\mathrm{EP},I}(P)
=
\max
\left(
|\epsilon_{\mathrm{passive},I}(P)|,
|\epsilon_{\mathrm{active},I}(P)|
\right).
$$

The first residual controls free fall.

The second residual controls whether the same packet sources the field it falls in.

Status:

`active_passive_inertial_residuals_defined`

### 30.5. No-refit matter gate

After one calibration of the packet generator, the same matter map must pass:

1. inertial response in flat motion;
2. gravitational redshift of clocks made from matter;
3. slow free fall;
4. source strength in Poisson/Gauss law;
5. lensing source strength after spatial curvature closure.

If any gate requires a different \(m_{\mathrm{kin}}\), \(m_{\mathrm{grav}}\), or \(m_{\mathrm{src}}\), the matter calibration fails.

Status:

`matter_no_refit_gate`

### 30.6. Source law after closure

If:

$$
\sigma_{\Phi,I}^G
=
\rho_{\mathrm{kin},I}c_I^2,
$$

then the conditional source law becomes:

$$
\Delta_S\Phi_I
=
\frac{c_I^4}{\alpha_I}
\rho_{\mathrm{kin},I}.
$$

With:

$$
G_I
=
\frac{c_I^4}{4\pi\alpha_I},
$$

this gives:

$$
\Delta_S\Phi_I
=
4\pi G_I\rho_{\mathrm{kin},I}.
$$

This is still conditional on \(\alpha_I\) from the link stiffness closure.

Status:

`poisson_form_after_matter_closure`

### 30.7. What is closed

This section closes:

$$
\sigma_{\Phi,I}^G\to\rho_m c_I^2
$$

as an unexamined calibration phrase.

It replaces it with:

$$
q_{\Phi,I}(P)
\to
m_{\mathrm{kin},I}(P)c_I^2
$$

plus active/passive/inertial residual gates.

It does not yet derive:

1. the packet generator \(\mathcal K_P\);
2. the particle mass spectrum;
3. exact vanishing of \(\epsilon_{\mathrm{EP},I}\);
4. coupling to internal stress and relativistic pressure;
5. quantum field particle sectors.

Next target:

derive \(\mathcal K_P\) from inherited update action and clock response.

Status:

`matter_calibration_gap_reduced`
