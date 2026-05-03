## 60. Minimal Clock-Vacuum Oscillator

This section builds the first toy spectral model for the clock-vacuum response.

It is a consistency test, not a claim that nature is exactly this oscillator.

Status:

`minimal_clock_vacuum_oscillator_initialized`

### 60.1. Oscillator coordinate

Let:

$$
q_\chi(t)
$$

be the flat-vacuum clock-strain mode coupled to link strain \(s_{EF}\).

Use the quadratic action:

$$
S_\chi[q]
=
\frac12
\int dt
\left[
M_{\chi,I}\dot q_\chi^2
-
M_{\chi,I}\omega_{\ell,I}^2q_\chi^2
\right].
$$

The first response pole is:

$$
\omega_{\ell,I}.
$$

Status:

`clock_vacuum_oscillator_coordinate`

### 60.2. Static stiffness

The static vacuum energy for displacement \(q_\chi\) is:

$$
E_{\mathrm{vac}}
=
\frac12
M_{\chi,I}\omega_{\ell,I}^2q_\chi^2.
$$

If the normalized strain coordinate is:

$$
\bar s=q_\chi,
$$

then:

$$
\kappa_{\chi,I}^{(V)}
=
M_{\chi,I}\omega_{\ell,I}^2.
$$

Status:

`oscillator_static_stiffness`

### 60.3. Consistency with kappa-omega gate

The kappa-omega gate requires:

$$
\kappa_{\chi,I}
=
\frac{\hbar_I\omega_{\ell,I}}
{\rho_{\chi,I}}.
$$

Therefore the oscillator model satisfies the gate only if:

$$
M_{\chi,I}\omega_{\ell,I}^2
=
\frac{\hbar_I\omega_{\ell,I}}
{\rho_{\chi,I}}.
$$

Thus:

$$
M_{\chi,I}
=
\frac{\hbar_I}
{\rho_{\chi,I}\omega_{\ell,I}}.
$$

The oscillator inertia is not free after \(\omega_{\ell,I}\) and \(\rho_{\chi,I}\) are fixed.

Status:

`oscillator_inertia_from_consistency_gate`

### 60.4. Dimensionless oscillator action

For one period:

$$
T_\ell
=
\frac{2\pi}{\omega_{\ell,I}}.
$$

The action scale of a unit-amplitude oscillator cycle is:

$$
S_{\mathrm{cyc}}
\sim
M_{\chi,I}\omega_{\ell,I}
=
\frac{\hbar_I}{\rho_{\chi,I}}.
$$

For the minimal matched sector:

$$
\rho_{\chi,I}=1,
$$

so:

$$
S_{\mathrm{cyc}}
\sim
\hbar_I.
$$

This is a non-gravitational consistency link between:

1. action-phase scale;
2. clock-vacuum pole;
3. stiffness.

Status:

`oscillator_cycle_action_scale`

### 60.5. Response function

The oscillator response has form:

$$
\mathcal R_\chi(\omega)
=
\frac{1}{M_{\chi,I}}
\frac{1}
{\omega_{\ell,I}^2-\omega^2-i0^+}.
$$

The first pole is:

$$
\omega=\omega_{\ell,I}.
$$

The low-frequency expansion is:

$$
\mathcal R_\chi(\omega)
=
\frac{1}
{M_{\chi,I}\omega_{\ell,I}^2}
\left[
1
+
\left(
\frac{\omega}{\omega_{\ell,I}}
\right)^2
+
O(\omega^4/\omega_{\ell,I}^4)
\right].
$$

Thus:

$$
r_2=1.
$$

Status:

`oscillator_response_function`

### 60.6. What the oscillator does not solve

The model does not derive:

$$
\omega_{\ell,I}.
$$

It only says that if a clock-vacuum mode has first pole \(\omega_{\ell,I}\), consistency with phase-action stiffness fixes:

$$
M_{\chi,I}
=
\frac{\hbar_I}
{\rho_{\chi,I}\omega_{\ell,I}}.
$$

Therefore the remaining hard problem is still the pole itself.

Status:

`oscillator_does_not_compute_pole`

### 60.7. No-fit rule

Forbidden:

1. choose \(M_{\chi,I}\) from \(G_N\);
2. choose \(\omega_{\ell,I}\) from \(G_N\);
3. call the oscillator a derivation of \(\omega_{\ell,I}\);
4. hide a failed \(\mathcal R_{\kappa\omega}\) by rescaling \(q_\chi\).

Allowed:

1. use the oscillator to test route consistency;
2. derive \(M_{\chi,I}\) after \(\omega_{\ell,I}\) is known;
3. compare \(r_2=1\) with dispersion residual coefficients after geometry projection.

Status:

`oscillator_no_fit_rule`

### 60.8. What is closed

Closed in the toy oscillator sector:

$$
\mathcal R_\chi(\omega)
=
\frac{1}{M_{\chi,I}}
\frac{1}
{\omega_{\ell,I}^2-\omega^2-i0^+}.
$$

Closed:

$$
M_{\chi,I}
=
\frac{\hbar_I}
{\rho_{\chi,I}\omega_{\ell,I}}.
$$

Open:

1. primitive derivation of \(\omega_{\ell,I}\);
2. whether the response is single-pole or multi-pole;
3. whether \(r_2=1\) survives the full inherited kernel;
4. exact projection from \(r_2\) to propagation coefficients.

Next target:

define the primitive update spectrum whose lowest stable excitation gives \(\omega_{\ell,I}\).

Primitive update spectrum:

`sections/61-primitive-update-spectrum.md`

Status:

`minimal_oscillator_consistency_closed`
