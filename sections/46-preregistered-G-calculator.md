## 46. Pre-Registered \(G_I\) Calculator

This section collects the current weak-gravity route into one pre-registered calculator.

It is not yet a numerical prediction.

It defines exactly what must be supplied before comparing with \(G_N\).

Status:

`preregistered_G_calculator_initialized`

### 46.1. General update-action calculator

Current route:

$$
\kappa_{\chi,I}^{(A)}
=
\frac{\hbar_I C_{\chi,I}}{\tau_{\chi,*}}.
$$

Substitute into:

$$
G_I
=
\frac{c_I^4D_S\ell_{0,*}}
{2\pi\kappa_{\chi,I}z_{I,*}q_{V,*}}.
$$

Then:

$$
G_I^{(A)}
=
\frac{c_I^4D_S\ell_{0,*}\tau_{\chi,*}}
{2\pi\hbar_I C_{\chi,I}z_{I,*}q_{V,*}}.
$$

Status:

`general_update_action_G_calculator`

### 46.2. Minimal radar-sampling calculator

If:

$$
C_{\chi,I}=1,
$$

and:

$$
\tau_{\chi,*}
=
\eta_\tau\frac{\ell_{0,*}}{c_I},
$$

then:

$$
G_I^{(\mathrm{min})}
=
\frac{\eta_\tau D_Sc_I^3\ell_{0,*}^2}
{2\pi\hbar_I z_{I,*}q_{V,*}}.
$$

This is the current sharpest conditional calculator.

Status:

`minimal_radar_sampling_G_calculator`

### 46.3. Input ledger

Before \(G_N\) comparison, the calculator requires:

| Input | Source | May use \(G_N\)? |
|---|---|---|
| \(c_I\) | clock/null readout | no |
| \(\hbar_I\) | phase/action gates | no |
| \(D_S\) | order/count spatial dimension | no |
| \(\ell_{0,*}\) | clock-order distance scale | no |
| \(z_{I,*}\) | spatial adjacency degree | no |
| \(q_{V,*}\) | cell-volume shape factor | no |
| \(C_{\chi,I}\) | kernel-action phase curvature | no |
| \(\tau_{\chi,*}\) or \(\eta_\tau\) | clock-radar sampling protocol | no |

Forbidden hidden inputs:

$$
G_N,\quad l_P,\quad c^4/G_N,\quad \sqrt{\hbar G_N/c^3}.
$$

Status:

`G_calculator_input_ledger`

### 46.4. Dimensionless gate

The general dimensionless gate is:

$$
\Pi_G
=
\frac{
2\pi\hbar_I C_{\chi,I}z_{I,*}q_{V,*}G_N
}{
c_I^4D_S\ell_{0,*}\tau_{\chi,*}
}.
$$

The prediction is:

$$
\Pi_G=1
\pm
\epsilon_G.
$$

For the minimal radar-sampling calculator:

$$
\Pi_G^{(\mathrm{min})}
=
\frac{
2\pi\hbar_I z_{I,*}q_{V,*}G_N
}{
\eta_\tau D_Sc_I^3\ell_{0,*}^2
}.
$$

Again:

$$
\Pi_G^{(\mathrm{min})}=1\pm\epsilon_G.
$$

This is the proper comparison object because it is dimensionless.

Status:

`dimensionless_G_gate_defined`

### 46.5. Planck crossover as output

Using:

$$
l_{P,\mathrm{obs}}^2
=
\frac{\hbar G_N}{c^3}
$$

inside the gate is allowed only after \(G_N\) is already the experimental comparison value.

In the minimal calculator, the gate can be rewritten:

$$
\frac{\ell_{0,*}^2}{l_{P,\mathrm{obs}}^2}
=
\frac{2\pi z_{I,*}q_{V,*}}
{\eta_\tau D_S}
\quad
\text{at successful closure}.
$$

This is not a definition of \(\ell_{0,*}\).

It is the form the independently derived \(\ell_{0,*}\) must satisfy if the minimal sector is correct.

Status:

`planck_crossover_gate_not_input`

### 46.6. Residual map

If:

$$
\Pi_G-1\neq0,
$$

the residual is:

$$
\mathcal R_G=\Pi_G-1.
$$

Pre-declared residual locations:

1. \(\mathcal R_C\): \(C_{\chi,I}\neq\bar a_I\);
2. \(\mathcal R_\tau\): sampling interval is not \(\eta_\tau\ell_0/c_I\);
3. \(\mathcal R_z,\mathcal R_q,\mathcal R_Q\): spatial adjacency/cell sector not regular;
4. \(\mathcal R_D\): \(D_S\neq3\) or scale-dependent;
5. \(\mathcal R_{\mathrm{source}}\): Newtonian source law is only an effective gate;
6. \(\mathcal R_{\mathrm{cosmo}}\): large-scale dark-sector readout modifies the weak-gravity closure.

The residual must not be erased by retuning calculator inputs.

Status:

`G_residual_map_predeclared`

### 46.7. Experimental gates after \(G_I\)

After the calculator produces \(G_I\), it must pass the weak-field chain:

$$
\nabla^2\Phi_I=4\pi G_I\rho_m,
$$

$$
\ddot x=-\nabla\Phi_I,
$$

$$
\frac{\Delta\nu}{\nu}
\simeq
\frac{\Delta\Phi_I}{c_I^2},
$$

and the PPN target:

$$
\gamma_I^{\mathrm{PPN}}\to1,
\qquad
\beta_I^{\mathrm{PPN}}\to1.
$$

These gates are experimental filters, not assumptions used to set the inputs.

Status:

`post_calculator_weak_field_gates`

### 46.8. What is closed

Closed:

1. one explicit general \(G_I\) calculator;
2. one sharper minimal radar-sampling calculator;
3. dimensionless gate \(\Pi_G\);
4. forbidden-input ledger;
5. residual map.

Open:

1. numerical \(\ell_{0,*}\);
2. exact \(z_{I,*},q_{V,*},D_S\);
3. proof of \(C_{\chi,I}=1\);
4. numerical \(\eta_\tau\);
5. actual \(G_N\) comparison.

Next target:

derive \(\eta_\tau\) from the clock-radar protocol and exact neighbour-link sampling convention.

Radar sampling invariant:

`sections/47-radar-sampling-invariant.md`

Status:

`G_calculator_preregistered_not_executed`
