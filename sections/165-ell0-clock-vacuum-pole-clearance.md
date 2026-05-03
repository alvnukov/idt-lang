## 165. ell0 Clock-Vacuum Pole Clearance

Status:

`ell0_clock_vacuum_pole_clearance_initialized`

This section opens the admissible route from the clock-vacuum pole to a
physical length candidate:

$$
\mathcal R_{\chi}(\omega)
\Rightarrow
\omega_{\ell,I}
\Rightarrow
\ell_0=\frac{c_I}{\omega_{\ell,I}}.
$$

It does not compute the numerical value of \(\ell_0\).

### 165.1. Why this clearance is needed

The current non-gravity dispersion route gives only:

$$
\omega_{\ell,I}\ge \omega_{\min},
\qquad
\ell_0\le \frac{c_I}{\omega_{\min}}.
$$

That is a bound, not a physical length value.

Promoting it to exact \(\ell_0\) would hide the scale needed by the
first-principles \(G_I\) candidate.

Status:

`ell0_bound_not_physical_value`

### 165.2. Pole closure target

The new target is:

`clock_vacuum_pole_closure_I`.

It can close only after:

1. `clock_vacuum_spectral_law_I` is derived;
2. `omega_ell_I` is derived from the first stable clock-vacuum pole or edge;
3. the pole is species-stable;
4. no gravity, Planck, observed \(\hbar\), or calibrated anchor enters the
   construction;
5. the local \(G_N\) comparison remains a holdout.

Status:

`clock_vacuum_pole_closure_target_registered`

### 165.3. Length clearance target

The new clearance target is:

`ell0_emergence_clearance_I`.

It accepts:

$$
\ell_0=\frac{c_I}{\omega_{\ell,I}}
$$

only after `clock_vacuum_pole_closure_I` closes.

The derived physical candidate is represented separately as:

`ell0_physical_candidate_I`.

This separation prevents a bound-only result or a toy radar consistency check
from being relabeled as a physical length derivation.

Status:

`ell0_clearance_targets_registered`

### 165.4. No-fit rule

Forbidden construction inputs:

1. \(G_N\);
2. Planck units or Planck length;
3. observed \(\hbar\);
4. `calibrated_hbar_I`;
5. `calibrated_G_anchor_I`;
6. `local_G_anchor_I`;
7. any backsolved weak-gravity residual.

Allowed after freeze:

1. compare the resulting \(\ell_0\) with any gravity-inferred scale;
2. record a residual;
3. reject the candidate if the residual fails the preregistered holdout.

Status:

`ell0_no_gravity_or_planck_shortcut`

### 165.5. Machine guard

The verifier now rejects:

1. `clock_vacuum_pole_closure_I=derived` before pole inputs and finite pole
   gates close;
2. `ell0_emergence_clearance_I=derived` before the pole closure and length
   provenance gates close;
3. `ell0_physical_candidate_I=derived` before `ell0_emergence_clearance_I`;
4. `ell0=derived` or `ell0=derived_conditional` before both clearance targets
   are derived;
5. exact \(\ell_0\) claims made from bound-only evidence.

Status:

`ell0_machine_clearance_guard_registered`

### 165.6. Research verdict

The route is not a dead end.

But the live problem is now precise:

derive the first clock-vacuum pole from `clock_vacuum_spectral_law_I` without
using \(G_N\), Planck units, or calibrated anchors.

Until that happens, \(\ell_0\) remains open and \(G_I\) remains a target.

Status:

`ell0_clearance_research_complete_for_current_front`
