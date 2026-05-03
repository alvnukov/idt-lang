## 25. Source-Weight Bridge

This section reduces the arbitrariness of the source weight \(m_I(\eta)\).

The source weight is not introduced as primitive mass.

It is the calibrated linear response of an inherited update to clock-rate strain:

$$
\varphi(E)
=
\log\chi(E)
=
\frac{\Phi_I(E)}{c_I^2}.
$$

Status:

`source_weight_bridge_initialized`

### 25.1. The gap

The source-stress packet uses:

$$
\rho_I^G(U)
=
\frac{1}{\nu_{G,S}(U)}
\sum_{\eta\in U}m_I(\eta).
$$

If \(m_I(\eta)\) is arbitrary, the source law is only a renamed fit.

Acceptance requirement:

$$
m_I(\eta)
\quad
\text{must be obtained from the same inheritance structure that generates clock-rate strain.}
$$

Status:

`arbitrary_mass_label_forbidden`

### 25.2. Local clock-strain response

Let one inherited update \(\eta\) have support near \(E_\eta\).

Its local contribution to the weak clock-distortion functional has expansion:

$$
\mathcal C_\eta[\varphi]
=
\mathcal C_\eta[0]
+
q_{\Phi,I}(\eta)\varphi(E_\eta)
+
O(\varphi^2,\partial\varphi).
$$

Define the clock-source charge:

$$
q_{\Phi,I}(\eta)
=
\left.
\frac{\partial \mathcal C_\eta}{\partial\varphi(E_\eta)}
\right|_{\varphi=0}.
$$

This is the primitive source-response coefficient.

Positive \(q_{\Phi,I}\) sources an attractive potential because the validated boundary condition is:

$$
\Phi_I(\infty)=0,
\qquad
\Phi_I<0
\quad
\text{near a positive isolated source.}
$$

Status:

`source_charge_as_clock_strain_response`

### 25.3. Additivity gate

For independent inherited updates in a coarse region \(U\):

$$
Q_{\Phi,I}(U)
=
\sum_{\eta\in U}q_{\Phi,I}(\eta).
$$

The geometric source density entering the Poisson bridge is:

$$
\sigma_{\Phi,I}^G(U)
=
\frac{Q_{\Phi,I}(U)}{\nu_{G,S}(U)}.
$$

The section 6 notation:

$$
\beta_I\rho_I^G
$$

is therefore identified as:

$$
\beta_I\rho_I^G
=
\sigma_{\Phi,I}^G.
$$

Equivalently:

$$
q_{\Phi,I}(\eta)
=
\beta_I m_I(\eta).
$$

Thus \(m_I\) alone is partly conventional.

The invariant source object is the product:

$$
\beta_I\rho_I^G.
$$

Status:

`source_weight_reduced_to_response_charge`

### 25.4. Newtonian calibration

The weak source law from section 6 is:

$$
\Delta_S\Phi_I
=
\frac{c_I^2\beta_I}{\alpha_I}\rho_I^G.
$$

Using:

$$
\beta_I\rho_I^G
=
\sigma_{\Phi,I}^G,
$$

this becomes:

$$
\Delta_S\Phi_I
=
\frac{c_I^2}{\alpha_I}\sigma_{\Phi,I}^G.
$$

The validated Newtonian gate is:

$$
\Delta\Phi
=
4\pi G_N\rho_m.
$$

Therefore the calibrated matter-density readout must satisfy:

$$
4\pi G_N\rho_m
=
\frac{c_I^2}{\alpha_I}\sigma_{\Phi,I}^G.
$$

Equivalently:

$$
\rho_m
=
\frac{c_I^2}{4\pi G_N\alpha_I}\sigma_{\Phi,I}^G.
$$

This is a calibration equation, not a free fit:

the same \(\sigma_{\Phi,I}^G\) must also pass redshift, free-fall, lensing, and no-slip gates.

Status:

`newtonian_source_calibration_equation`

### 25.5. Active/passive source equality

Define active source weight:

$$
m_{\mathrm{src},I}(\eta)
=
\frac{q_{\Phi,I}(\eta)}{\beta_I}.
$$

For a slow localized packet in the weak clock field:

$$
d\tau_I
\approx
dt
\left[
1+\frac{\Phi_I}{c_I^2}
-\frac{v^2}{2c_I^2}
\right].
$$

Let the kinetic coefficient be \(m_{\mathrm{kin},I}\).

Let the clock-source/passive coupling be \(m_{\mathrm{grav},I}\).

The effective slow-motion Lagrangian is:

$$
L_{\mathrm{eff}}
=
\frac12m_{\mathrm{kin},I}v^2
-
m_{\mathrm{grav},I}\Phi_I.
$$

Then:

$$
\ddot x^i
=
-
\frac{m_{\mathrm{grav},I}}{m_{\mathrm{kin},I}}
\partial_i\Phi_I.
$$

Universal free fall requires:

$$
\frac{m_{\mathrm{grav},I}}{m_{\mathrm{kin},I}}
\to
1.
$$

Poisson universality requires the same packet weight to source the field:

$$
\frac{m_{\mathrm{src},I}}{m_{\mathrm{kin},I}}
\to
1.
$$

Define the equivalence residual:

$$
\epsilon_{\mathrm{EP},I}(\eta)
=
\max
\left(
\left|
\frac{m_{\mathrm{grav},I}(\eta)}
{m_{\mathrm{kin},I}(\eta)}
-
1
\right|,
\left|
\frac{m_{\mathrm{src},I}(\eta)}
{m_{\mathrm{kin},I}(\eta)}
-
1
\right|
\right).
$$

The previous one-ratio form:

$$
\frac{m_{\mathrm{grav},I}(\eta)}
{m_{\mathrm{kin},I}(\eta)}
-
1.
$$

is only the passive/free-fall part of this gate.

The theory passes the weak-field equivalence gate only if:

$$
|\epsilon_{\mathrm{EP},I}|
\le
\epsilon_{\mathrm{Eotvos}}
$$

for all admissible localized matter packets and clock species in the validated domain.

Status:

`active_passive_source_gate`

### 25.6. No-refit rule

Once \(q_{\Phi,I}(\eta)\), \(\alpha_I\), and the matter calibration are chosen in one Newtonian domain,
they cannot be reselected for another gate.

The same source response must feed:

1. gravitational redshift;
2. Newtonian free fall;
3. Poisson/Gauss source law;
4. spatial-curvature/no-slip closure;
5. light bending and Shapiro delay through the PPN gates.

Failure mode:

if different experiments require different \(q_{\Phi,I}\), \(\beta_I\), or source calibration for the same matter packet, the bridge fails.

Status:

`single_source_weight_no_refit_gate`

### 25.7. What is closed

This section closes:

$$
m_I(\eta)
\quad
\text{as arbitrary source label.}
$$

It replaces it with:

$$
q_{\Phi,I}(\eta)
=
\left.
\frac{\partial \mathcal C_\eta}{\partial\varphi(E_\eta)}
\right|_{\varphi=0},
\qquad
q_{\Phi,I}=\beta_I m_I.
$$

It does not yet derive:

1. the particle mass spectrum;
2. the numerical value of \(G_N\);
3. microscopic link stiffness \(a_{EF}\);
4. the matter calibration from vacuum response;
5. exact vanishing of \(\epsilon_{\mathrm{EP},I}\).

Next target:

derive \(a_{EF}\) and the matter calibration from the same vacuum/clock-network response, so \(G_N\) is no longer an external calibration constant.

Vacuum stiffness bridge:

`sections/26-vacuum-stiffness-bridge.md`

Matter calibration closure:

`sections/30-matter-calibration-closure.md`

Status:

`source_weight_gap_reduced`
