## 154. Spectral Primitive Reduction Test

Status:

`spectral_primitive_reduction_test_initialized`

This section defines the only honest way to add a primitive that could unblock
the calibrated \(G\) route without fitting \(G_N\).

The primitive must not be a value of:

\[
\omega_{\ell,I}.
\]

It must be a local spectral law whose pole is computed before gravity is
consulted.

### 154.1. Rejected direct primitive

A direct assignment:

\[
\omega_{\ell,I}:=\Omega_*
\]

is not a derivation of \(G\).

If \(\Omega_*\) is fixed from \(G_N\), the status is:

`gravity_backsolved_link_frequency`.

If \(\Omega_*\) is fixed from a non-gravity measurement, the status is:

`second_calibration_anchor`.

Then the programme has two dimensional anchors:

1. `calibrated_hbar_I`;
2. `omega_ell_anchor_I`.

The result may be useful phenomenology, but it is not a one-anchor calculation
of \(G\).

Status:

`direct_omega_primitive_rejected_as_derivation`

### 154.2. Acceptable primitive form

The admissible new primitive is a rule, not a number:

\[
\mathcal S_{\chi,I}
:
(\mathcal I,\Gamma_I,K_\eta,\mathcal E)
\longrightarrow
\mathcal R_{\chi}(\omega)
\]

or equivalently a rule producing a derived oriented transfer family:

\[
\mathcal S_{\chi,I}
\longrightarrow
\Xi_\eta,\Pi_\eta,\mathcal T_{ji}^{(\eta)}.
\]

It is acceptable only if it fixes, before gravitational comparison:

1. the response function or transfer family;
2. the first stable pole or spectral edge;
3. the relevant phase holonomies;
4. the step-clock invariant, if the update-spectrum route is used;
5. the clock-species universality class.

The extracted pole is then:

\[
\omega_{\ell,I}
=
\min_{\omega>0}
\{\omega:\mathcal R_\chi(\omega)\text{ has a stable pole or edge}\}
\]

or:

\[
\omega_{\ell,I}
=
\min_{n:g_n\ne0}
\frac{|\arg\lambda_n|}
{\Delta\tau_{\mathrm{step}}}.
\]

Status:

`spectral_law_primitive_candidate_defined`

### 154.3. Free-parameter test

The primitive fails as a derivation if its output contains an adjustable scale:

\[
\mathcal R_\chi(\omega;\Omega_*),
\qquad
\lambda_n=e^{i\theta_n},
\qquad
\Delta\tau_{\mathrm{step}},
\]

with \(\Omega_*,\theta_n\), or \(\Delta\tau_{\mathrm{step}}\) not fixed by the
primitive law.

In that case the status is:

`spectral_law_parametric_not_predictive`.

The primitive remains admissible only as a calibration bridge if the free scale
is measured without using \(G_N\).

Status:

`spectral_free_parameter_test_defined`

### 154.4. Reduction criterion

The new primitive can later be removed only if the theory proves:

\[
\mathcal I,\Gamma_I,K_\eta,\mathcal E
\Rightarrow
\mathcal S_{\chi,I}
\]

with the same frozen outputs:

1. same pole \(\omega_{\ell,I}\);
2. same low-frequency response coefficients;
3. same phase holonomies;
4. same step-clock invariant;
5. same clock-species universality.

If this reduction fails, the primitive remains:

`bridge_assumption`.

It must not be silently reclassified as derived.

Status:

`spectral_primitive_reduction_criterion_defined`

### 154.5. Blind validation package

After \(\mathcal S_{\chi,I}\) is fixed, the validation package is:

1. compute \(\omega_{\ell,I}\);
2. compute \(\rho_{\chi,I}\), or declare it separately frozen;
3. compute \(calibrated\_G_I\);
4. compare to \(G_N\);
5. compare the same response coefficients against non-gravity dispersion and
   matter-wave residual gates;
6. reject the primitive if any post-comparison retuning is needed.

The critical point:

\[
G_N
\]

is never used inside \(\mathcal S_{\chi,I}\).

Status:

`spectral_law_blind_validation_package_defined`

### 154.6. Current decision

The current primitive set does not yet contain:

1. explicit \(\mathcal S_{\chi,I}\);
2. explicit \(\mathcal R_\chi(\omega)\);
3. explicit cross-update transfer family \(\Xi_\eta\);
4. explicit event transport \(\Pi_\eta\);
5. explicit derived \(\Delta\tau_{\mathrm{step}}\).

Therefore the calibrated \(G\) route is not unlocked yet.

The least bad extension is:

`clock_vacuum_spectral_law_I = bridge_candidate`.

It is acceptable only as a declared bridge candidate until it is reduced to the
older primitives.

Status:

`clock_vacuum_spectral_law_bridge_candidate_selected`
