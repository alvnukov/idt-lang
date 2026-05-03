## 62. Minimal Two-State Update Spectrum

This section tests the smallest finite-state update spectrum.

It is useful mainly because it exposes what is still not derived.

Status:

`minimal_two_state_update_spectrum_initialized`

### 62.1. Two reciprocal update modes

Use two reciprocal local update modes:

$$
|+\rangle,\qquad|-\rangle.
$$

They are exchanged by link reversal:

$$
E\leftrightarrow F.
$$

The most general unitary reciprocal transfer in this two-state sector, up to an irrelevant global phase, can be written:

$$
\mathsf T_{2}
=
\exp(-i\theta\sigma_x).
$$

Equivalently:

$$
\mathsf T_2
=
\cos\theta\;I
-
i\sin\theta\;\sigma_x.
$$

Status:

`two_reciprocal_update_modes_defined`

### 62.2. Spectrum

The eigenvalues are:

$$
\lambda_\pm
=
e^{\mp i\theta}.
$$

For transfer step duration:

$$
\Delta\tau_{\mathrm{step}},
$$

the mode frequency is:

$$
\omega_\theta
=
\frac{|\theta|}
{\Delta\tau_{\mathrm{step}}}.
$$

If this is the first stable strain-coupled mode:

$$
\omega_{\ell,I}
=
\omega_\theta.
$$

Status:

`two_state_spectrum_computed`

### 62.3. What remains free

The two-state model does not determine:

$$
\theta.
$$

It also does not determine:

$$
\Delta\tau_{\mathrm{step}}.
$$

Therefore:

$$
\omega_{\ell,I}
=
\frac{|\theta|}{\Delta\tau_{\mathrm{step}}}
$$

is only a parametrization unless an additional principle fixes \(\theta\) and the step clock time.

Status:

`two_state_model_exposes_free_phase`

### 62.4. Minimal phase-lock candidate

A possible non-fit phase-lock condition is:

$$
\mathsf T_2^N=I
$$

for a primitive closed update cycle of length \(N\).

Then:

$$
\theta
=
\frac{2\pi m}{N},
\qquad
m\in\mathbb Z.
$$

The first nonzero mode gives:

$$
\theta_{\min}
=
\frac{2\pi}{N}.
$$

Thus:

$$
\omega_{\ell,I}
=
\frac{2\pi}
{N\Delta\tau_{\mathrm{step}}}.
$$

This becomes predictive only if:

$$
N,\quad
\Delta\tau_{\mathrm{step}}
$$

are derived from the primitive update grammar.

Status:

`primitive_cycle_phase_lock_candidate`

### 62.5. Comparison with clock-radar step

If one transfer step is identified with the half-radar link time:

$$
\Delta\tau_{\mathrm{step}}
=
\frac{\ell_{0,*}}{c_I}
=
\frac{1}{\omega_{\ell,I}},
$$

then:

$$
\omega_{\ell,I}
=
\frac{\theta}{\Delta\tau_{\mathrm{step}}}
=
\theta\omega_{\ell,I}.
$$

Consistency requires:

$$
\theta=1.
$$

This is not generally compatible with:

$$
\theta=\frac{2\pi}{N}
$$

unless:

$$
N=2\pi,
$$

which is not an integer.

Therefore a transfer step is not automatically the half-radar link time.

This prevents a hidden circular definition.

Status:

`step_time_not_automatically_half_radar`

### 62.6. Required new invariant

Define:

$$
\zeta_{\mathrm{step}}
=
\Delta\tau_{\mathrm{step}}\omega_{\ell,I}.
$$

Then:

$$
\theta
=
\zeta_{\mathrm{step}}
$$

for the first mode.

The primitive update spectrum route requires:

$$
\zeta_{\mathrm{step}}
$$

from update grammar, not gravity.

Status:

`step_phase_invariant_defined`

### 62.7. No-fit rule

Forbidden:

1. choose \(\theta\) from \(G_N\);
2. choose \(N\) from \(G_N\);
3. identify step time with radar half-time without checking consistency;
4. call the two-state model a numerical derivation.

Allowed:

1. use it as the minimal spectrum scaffold;
2. derive \(\theta\) from primitive cycle closure;
3. derive \(\Delta\tau_{\mathrm{step}}\) from clock readout;
4. reject the model if it leaves both free.

Status:

`two_state_spectrum_no_fit_rule`

### 62.8. What is closed

Closed:

$$
\lambda_\pm=e^{\mp i\theta},
\qquad
\omega_{\ell,I}=|\theta|/\Delta\tau_{\mathrm{step}}.
$$

Closed:

The two-state model alone is not enough to derive \(\omega_{\ell,I}\).

Open:

1. primitive cycle length \(N\);
2. step clock time \(\Delta\tau_{\mathrm{step}}\);
3. step phase invariant \(\zeta_{\mathrm{step}}\);
4. whether a richer finite-state model fixes these.

Next target:

state the exact closure criterion for any finite-state update spectrum to count as a real derivation rather than a parametrization.

Update spectrum closure criteria:

`sections/63-update-spectrum-closure-criteria.md`

Primitive cycle grammar:

`sections/64-primitive-cycle-grammar.md`

Status:

`two_state_model_parametric_not_predictive`
