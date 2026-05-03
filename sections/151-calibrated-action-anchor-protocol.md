## 151. Calibrated Action Anchor Protocol

Status:

`calibrated_action_anchor_protocol_initialized`

This section defines the calibrated action branch after the physical scope
boundary.

The strong claim:

`hbar_I = derived_from_current_primitives`

remains out of scope until an independent action-scale anchor is supplied.

The new, weaker claim is:

`calibrated_action_reconstruction_I = target`.

### 151.1. New branch object

Introduce a separate calibrated action anchor:

`calibrated_action_anchor_I`.

Manifest status:

`bridge_assumption`.

Dimension:

\[
[calibrated\_action\_anchor_I]=ML^2T^{-1}.
\]

For the operational quantum branch, the corresponding phase-action conversion
is:

`calibrated_hbar_I`.

Manifest status:

`bridge_assumption`.

This is not the same claim as:

`hbar_I = derived`.

The original derived route remains:

`hbar_I = blocked`.

### 151.2. Source discipline

The calibrated branch may use one and only one unit-setting source for the
action scale.

Allowed source:

`hbar_obs`

or one declared equivalent action-scale calibration route.

Forbidden after calibration:

1. refit `calibrated_hbar_I` per experiment;
2. use one value for spectroscopy and another for matter waves;
3. tune the anchor after phase-cost or weak-gravity residuals;
4. relabel the calibrated anchor as derived.

The calibrated branch therefore uses:

\[
h_{\mathrm{cal}}
\quad\text{once},
\]

then treats all mismatches as residuals.

### 151.3. Validation gates

Existing gates become validation gates for the calibrated branch:

1. `phase_action_scale_universality_demo`;
2. `hbar_known_gate_holdout_demo`;
3. future spectroscopy / matter-wave / AB / phase-accumulation fixtures with
   predeclared tolerances.

The required check is:

\[
h_{\mathrm{spectroscopy}}
=
h_{\mathrm{matter-wave}}
=
h_{\mathrm{AB}}
=
h_{\mathrm{phase}}
\]

within declared experimental tolerances, without changing the anchor.

If the same anchor fails across routes, the calibrated branch is rejected.

### 151.4. What this unlocks

The calibrated branch can legitimately compute:

1. finite and continuum QM readouts that require an action scale;
2. Hamiltonian and momentum units from already derived generators:

\[
H_I^{\mathrm{cal}}=calibrated\_hbar_I\,\Omega_I,
\qquad
p_I^{\mathrm{cal}}=calibrated\_hbar_I\,k_I;
\]

3. phase accumulation and de Broglie gates as holdout checks;
4. dimensionless residual predictions after one action calibration.

This does not unlock a derived \(G_I\) unless the remaining length/tick and
work/mass anchors are also fixed or calibrated under their own protocols.

### 151.5. Discharge protocol

The calibrated anchor may later be discharged only in one of two ways.

First, the theory derives an independent action standard:

\[
A_{0,I}
\Leftarrow
\text{non-circular primitive work/tick route}.
\]

Then the calibrated branch can be compared against the derived branch.

Second, the anchor cancels from a prediction. Then the prediction must be
recorded as dimensionless and anchor-independent.

If neither happens, all results depending on `calibrated_hbar_I` remain:

`calibrated_not_derived`.

### 151.6. Claim boundary

Allowed claim:

> The protolanguage gives a calibrated reconstruction of quantum readouts using
> one universal action anchor, with no per-experiment refit.

Forbidden claim:

> The protolanguage derives Planck's constant from inherited distinguishability.

Forbidden claim:

> The calibrated action anchor proves the weak-gravity constant.

Current accepted statuses:

`calibrated_action_anchor_I = bridge_assumption`.

`calibrated_hbar_I = bridge_assumption`.

`calibrated_action_reconstruction_I = target`.

`hbar_I = blocked`.
