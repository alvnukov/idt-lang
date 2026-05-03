## 44. Phase-Action Kappa Gate

This section connects the update-action response:

$$
A_{\chi,*}
$$

to the action-phase bridge:

$$
\hbar_I.
$$

It does not assume:

$$
A_{\chi,*}=\hbar_I.
$$

It derives the allowed form:

$$
A_{\chi,*}
=
\hbar_I C_{\chi,I}.
$$

Status:

`phase_action_kappa_gate_initialized`

### 44.1. Dimensionless phase response

For a strained clock link \(\langle EF\rangle\), write the phase readout:

$$
U_{\chi,EF}[s]
=
\exp\left[
i\Theta_{\chi,EF}[s]
\right].
$$

The inherited action readout satisfies:

$$
\Theta_{\chi,EF}[s]
=
\frac{\mathcal S_{\chi,EF}[s]}{\hbar_I}.
$$

Therefore:

$$
\mathcal S_{\chi,EF}[s]
=
\hbar_I\Theta_{\chi,EF}[s].
$$

Status:

`clock_strain_phase_response_defined`

### 44.2. Dimensionless curvature

Define:

$$
C_{\chi,EF}
=
\left.
\frac{\partial^2\Theta_{\chi,EF}}
{\partial s_{EF}^2}
\right|_{s_{EF}=0}.
$$

Since \(\Theta\) and \(s_{EF}\) are dimensionless:

$$
[C_{\chi,EF}]=1.
$$

Using:

$$
A_{\chi,EF}
=
\left.
\frac{\partial^2\mathcal S_{\chi,EF}}
{\partial s_{EF}^2}
\right|_{s_{EF}=0},
$$

gives:

$$
A_{\chi,EF}
=
\hbar_I C_{\chi,EF}.
$$

In a stable flat sector:

$$
A_{\chi,*}
=
\hbar_I C_{\chi,I}.
$$

Status:

`Achi_as_hbar_times_dimensionless_curvature`

### 44.3. Kappa after phase-action bridge

The update-action route becomes:

$$
\kappa_{\chi,I}^{(A)}
=
\frac{\hbar_I C_{\chi,I}}{\tau_{\chi,*}}.
$$

Then:

$$
G_I^{(A)}
=
\frac{c_I^4D_S\ell_{0,*}\tau_{\chi,*}}
{2\pi\hbar_I C_{\chi,I}z_{I,*}q_{V,*}}.
$$

This is not a fit of \(G_N\).

It is a formula whose remaining non-gravitational inputs are:

$$
C_{\chi,I},
\qquad
\tau_{\chi,*},
\qquad
\ell_{0,*},z_{I,*},q_{V,*},D_S.
$$

Status:

`G_formula_after_phase_action_bridge`

### 44.4. Radar sampling option

If the standard sampling interval is fixed by one neighbour light-time:

$$
\tau_{\chi,*}
=
\eta_\tau
\frac{\ell_{0,*}}{c_I},
$$

where \(\eta_\tau\) is a dimensionless protocol invariant, then:

$$
G_I^{(A)}
=
\frac{\eta_\tau D_S c_I^3\ell_{0,*}^2}
{2\pi\hbar_I C_{\chi,I}z_{I,*}q_{V,*}}.
$$

This exposes a Planck-crossover relation:

$$
l_{P,I}^2
\equiv
\frac{\hbar_I G_I}{c_I^3}
=
\frac{\eta_\tau D_S}
{2\pi C_{\chi,I}z_{I,*}q_{V,*}}
\ell_{0,*}^2.
$$

This relation must not be inverted to choose \(\ell_{0,*}\) from the observed Planck length.

Allowed use:

1. derive \(\ell_{0,*}\), \(C_{\chi,I}\), \(z_{I,*}\), \(q_{V,*}\), \(D_S\), and \(\eta_\tau\) independently;
2. compute \(G_I\);
3. compare with \(G_N\);
4. record the residual.

Status:

`planck_crossover_as_output_not_input`

### 44.5. No-fit gates

Forbidden:

1. set \(C_{\chi,I}\) by demanding \(G_I=G_N\);
2. set \(\eta_\tau\) by demanding \(G_I=G_N\);
3. set \(\ell_{0,*}=l_P\) unless \(\ell_{0,*}\) was already independently derived;
4. use \(G_N\) to choose the kernel class.

Allowed:

1. derive \(C_{\chi,I}\) from phase curvature of the update kernel;
2. derive \(\eta_\tau\) from clock-radar sampling convention;
3. derive \(\ell_{0,*}\) from clock-order distance;
4. use \(G_N\) only as an experimental gate.

Status:

`phase_action_kappa_no_fit_gate`

### 44.6. Experimental gates

The same \(\hbar_I\) must already pass independent non-gravitational gates:

$$
E=\hbar_I\omega,
\qquad
p=\hbar_Ik,
\qquad
\Delta\phi=\Delta S/\hbar_I.
$$

Only after these gates can \(\hbar_I\) enter:

$$
\kappa_{\chi,I}^{(A)}
=
\frac{\hbar_I C_{\chi,I}}{\tau_{\chi,*}}.
$$

The gravitational check is then:

$$
\left|
\frac{G_I^{(A)}-G_N}{G_N}
\right|
\le
\epsilon_G.
$$

Status:

`hbar_independent_before_gravity_gate`

Action-cost hbar route:

`sections/82-action-cost-hbar-route.md`

### 44.7. What is closed

This section closes:

$$
A_{\chi,*}
=
\hbar_I C_{\chi,I}
$$

as the only action-phase-compatible form.

It does not close:

1. numerical \(C_{\chi,I}\);
2. numerical \(\eta_\tau\);
3. exact \(\ell_{0,*}\);
4. numerical \(G_I\);
5. whether the vacuum-response route gives the same \(\kappa_{\chi,I}\).

Next target:

derive \(C_{\chi,I}\) from the phase curvature of the minimal positive kernel, or declare it a residual before comparison.

Kernel phase curvature gate:

`sections/45-kernel-phase-curvature-gate.md`

Status:

`Achi_hbar_bridge_form_closed`
