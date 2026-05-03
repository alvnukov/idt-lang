## 11. Predictive Closure Protocol

The theory gains predictive value only when a bridge constant is not re-fitted across routes.

A numerical coincidence is not enough.

A prediction requires:

1. a declared primitive route;
2. a declared calibration set;
3. a declared independent gate;
4. no new fit between calibration and gate.

### 11.1. Calibration is not prediction

Let:

$$
\theta_I
=
(\hbar_I,c_I,G_I,e_I,k_{B,I},\ldots)
$$

be bridge constants, and let:

$$
\pi_I
=
(\mathfrak s_I,\mathfrak q_I,\rho_I^G,\ldots)
$$

be primitive inheritance data.

A calibration map:

$$
\mathcal K_C:
\pi_I
\mapsto
\theta_I^{(C)}
$$

sets a bridge scale from one route \(C\).

It becomes predictive only if the same \(\theta_I^{(C)}\) is then used in a distinct route \(R\):

$$
O_R^{\mathrm{proto}}(\pi_I,\theta_I^{(C)})
\to
O_R^{\mathrm{obs}}
$$

without re-fitting.

If each route gets its own:

$$
\theta_I^{(R)}
$$

then the construction is descriptive, not predictive.

Status:

`calibration_prediction_separation`

### 11.2. Prediction count

Define:

$$
N_{\mathrm{pred}}
=
N_{\mathrm{independent\ gates}}
-
N_{\mathrm{free\ bridge\ parameters}}
-
N_{\mathrm{unit\ conventions}}
$$

The theory has predictive content in a sector only if:

$$
N_{\mathrm{pred}}>0.
$$

Dimensionful constants mostly count as unit-setting bridge parameters.

Dimensionless constants count as physical gates.

Therefore the first serious constants target is not:

$$
\hbar=\text{number}
$$

but:

$$
\alpha_{\mathrm{em},I}
=
\alpha_{\mathrm{em}}^{\mathrm{obs}}
$$

from primitive charge-phase structure without route-by-route fitting.

### 11.3. Action-phase closure

The action bridge is:

$$
\Delta\phi_I
=
\frac{\Delta S_I}{\hbar_I}.
$$

The primitive action target is:

$$
\Delta S_I(h_a,h_b)
=
\sum_{\eta\in h_a}\mathfrak s_I(\eta)
-
\sum_{\eta\in h_b}\mathfrak s_I(\eta).
$$

Then:

$$
\Delta\phi_I(h_a,h_b)
=
\frac{1}{\hbar_I}
\left[
\sum_{\eta\in h_a}\mathfrak s_I(\eta)
-
\sum_{\eta\in h_b}\mathfrak s_I(\eta)
\right].
$$

Allowed one-route calibration:

$$
\hbar_I
\leftarrow
E=hf
$$

or:

$$
\hbar_I
\leftarrow
p=\hbar k.
$$

Forbidden move:

$$
\hbar_I^{\mathrm{spectroscopy}}
\neq
\hbar_I^{\mathrm{interference}}
\neq
\hbar_I^{\mathrm{phase}}
$$

with separate fits.

Predictive closure gate:

$$
\mathcal C_{\hbar}
=
\left\{
\frac{h_I^{\mathrm{spectroscopy}}}{h_I^{\mathrm{interference}}},
\frac{h_I^{\mathrm{spectroscopy}}}{h_I^{\mathrm{phase}}},
\frac{h_I^{\mathrm{interference}}}{h_I^{\mathrm{phase}}}
\right\}
\to
\{1,1,1\}
$$

within experimental uncertainty.

Status:

`action_phase_closure_gate`

### 11.4. Charge-phase closure

Electromagnetic readout must enter as phase connection, not as a separate force postulate.

For a charged history \(h\), define a connection contribution:

$$
\phi_{q,I}(h)
=
\frac{q_I}{\hbar_I}
\int_h A_{I,\mu}\,dx^\mu.
$$

For two paths:

$$
\Delta\phi_{q,I}
=
\frac{q_I}{\hbar_I}
\oint A_{I,\mu}\,dx^\mu.
$$

Known Aharonov-Bohm gate:

$$
\Delta\phi_{\mathrm{AB}}
=
\frac{q\Phi_B}{\hbar}.
$$

This gate is important because it tests phase connection directly, not just local force.

The fine-structure target is:

$$
\alpha_{\mathrm{em},I}
=
\frac{e_I^2}{4\pi\epsilon_{0,I}\hbar_I c_I}.
$$

In natural bridge units:

$$
\hbar_I=c_I=1,
$$

the target reduces to a dimensionless gauge coupling:

$$
\alpha_{\mathrm{em},I}
=
\frac{g_I^2}{4\pi}.
$$

Therefore the real primitive target is:

$$
\mathfrak q_I(\eta)
\Rightarrow
g_I
\Rightarrow
\alpha_{\mathrm{em},I}.
$$

If \(g_I\) is only fitted from one electromagnetic experiment, the theory still must predict the others.

Charge-phase closure gate:

$$
\mathcal C_{\alpha}
=
\left\{
\frac{\alpha_{\mathrm{em},I}^{\mathrm{spectroscopy}}}
{\alpha_{\mathrm{em},I}^{\mathrm{scattering}}},
\frac{\alpha_{\mathrm{em},I}^{\mathrm{spectroscopy}}}
{\alpha_{\mathrm{em},I}^{\mathrm{Josephson/Hall}}},
\frac{\alpha_{\mathrm{em},I}^{\mathrm{scattering}}}
{\alpha_{\mathrm{em},I}^{\mathrm{Josephson/Hall}}}
\right\}
\to
\{1,1,1\}.
$$

Status:

`charge_phase_closure_gate`

### 11.5. Joint clock-action closure

Clock readout and quantum phase must share the same update ordering without making \(\lambda\) observable.

Clock frequency:

$$
f_I
=
\frac{1}{2\pi}
\frac{d\phi_I}{d\tau_I}
$$

with:

$$
\phi_I
=
\frac{S_I}{\hbar_I}.
$$

Then the spectral gate:

$$
\Delta E
=
h f
$$

is not a primitive axiom.

It is the closure of:

1. action-phase conversion;
2. clock proper-time readout;
3. energy as phase rate.

Predictive gate:

$$
\Delta E_I
=
\hbar_I
\frac{d(\Delta\phi_I)}{d\tau_I}
$$

must match the same \(\hbar_I\) used in interference.

Status:

`clock_action_closure_gate`

### 11.6. Gravity-clock closure

The clock-rate route already gives:

$$
\frac{\nu_A-\nu_B}{\nu_B}
\approx
\frac{\Phi_I(A)-\Phi_I(B)}{c_I^2}
$$

and:

$$
\ddot x
=
-\nabla\Phi_I.
$$

The predictive closure is stronger:

calibrate \(\Phi_I\) from one clock-redshift route, then predict:

$$
\Delta_S\Phi_I
=
4\pi G_I\rho_I^G
$$

and PPN observables without changing \(G_I\), \(\gamma_I\), or clock residuals.

Weak-field closure gate:

$$
\mathcal C_G
=
\left\{
\text{redshift},
\text{free fall},
\text{Poisson source},
\text{light bending},
\text{Shapiro delay}
\right\}
$$

with one shared:

$$
c_I,\quad G_I,\quad \Phi_I,\quad \gamma_I^{\mathrm{PPN}}.
$$

If \(\gamma_I^{\mathrm{PPN}}\neq1\), the theory must declare a residual and compare it to lensing/Shapiro gates.

Status:

`gravity_clock_closure_gate`

### 11.7. Residuals as predictions

A residual is allowed only if it is declared before comparison with data.

Generic form:

$$
O_R^{\mathrm{obs}}
-
O_R^{\mathrm{proto}}
=
\mathcal R_R(\pi_I)
$$

The residual is predictive only if:

1. its sign or functional form is fixed before fitting;
2. it appears in at least two independent gates;
3. it cannot be absorbed into an existing bridge constant.

Otherwise it is just a hidden fit.

Examples of acceptable residual windows:

| Residual | Required independent gates |
|---|---|
| \(\delta\alpha_{\mathrm{em}}(E)\) | spectroscopy + scattering + clock/electrical route |
| \(\delta\hbar_I\) | interference + phase accumulation + spectroscopy |
| \(\delta\gamma_I^{\mathrm{PPN}}\) | light bending + Shapiro + lensing |
| \(\mathcal R_{\mathrm{dyn}}\) | rotation curves + velocity dispersion + lensing comparison |
| \(\mathcal R_H(a)\) | supernovae + BAO + CMB background + growth |

Status:

`declared_residual_prediction_rule`

### 11.8. First computable target

The next concrete computation should not start with the universe.

It should start with the smallest closure loop:

$$
\mathfrak s_I(\eta)
\Rightarrow
\Delta S_I
\Rightarrow
\Delta\phi_I
\Rightarrow
\text{two-path interference}
$$

plus:

$$
\mathfrak q_I(\eta)
\Rightarrow
\Delta\phi_{q,I}
\Rightarrow
\text{Aharonov-Bohm phase}
$$

and then:

$$
\mathfrak q_I(\eta)
\Rightarrow
g_I
\Rightarrow
\alpha_{\mathrm{em},I}.
$$

This gives the first realistic path to predictive value:

1. define \(\mathfrak s_I\) and \(\mathfrak q_I\);
2. allow one unit-setting calibration for \(\hbar_I\);
3. derive the phase response for neutral and charged two-path systems;
4. compare AB phase and interference phase with one shared \(\hbar_I\);
5. derive or constrain \(g_I\);
6. test \(\alpha_{\mathrm{em},I}\) across independent electromagnetic routes.

Status:

`first_predictive_loop_selected`

Formula-level implementation:

`sections/12-minimal-two-path-loop.md`

Primitive phase support conditions:

`sections/13-primitive-phase-bridges.md`
