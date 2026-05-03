## 156. Our-Universe Selection Gate

Status:

`our_universe_selection_gate_initialized`

This section corrects the target of the calibrated branch.

The mistake was to treat the numerical values of \(\hbar\) and \(G\) as things
that must be derived from the current primitive language.

Without an additional universe-selection principle, that target is too strong.

### 156.1. What went wrong

The current primitives can describe structural relations across possible
readout worlds.

They do not yet select:

1. the absolute action scale;
2. the absolute gravitational coupling scale;
3. the clock-vacuum pole scale;
4. the realized vacuum sector of our universe.

Therefore a claimed derivation of \(\hbar\) or \(G\) from the current primitives
would either:

1. smuggle in an unmarked scale anchor;
2. describe a class of possible universes;
3. confuse a calibration of our universe with a derivation of all universes.

Status:

`dimensionful_constant_derivation_target_rejected`

### 156.2. New target

The target is no longer:

`derive_hbar_and_G`.

The target is:

`select_our_universe_sector`.

Operationally, this means:

1. calibrate `calibrated_hbar_I` once;
2. calibrate `calibrated_G_anchor_I` once;
3. freeze any geometry/readout sector choices used by those anchors;
4. test all remaining structures as holdouts;
5. do not retune anchors per phenomenon.

Status:

`our_universe_sector_target_declared`

### 156.3. What remains nontrivial

After \(\hbar\) and \(G\) are anchors, the theory can still fail.

Nontrivial tests remain:

1. the same `calibrated_hbar_I` must work for spectroscopy, matter waves,
   phase holonomy, AB-type phases, and generator units;
2. the same `calibrated_G_anchor_I` must work for clock redshift, weak-field
   acceleration, PPN no-slip, and held-out gravitational domains;
3. the \(G\)-calibrated \(\Omega_{Gcal,I}\) must not violate non-gravity
   link-frequency bounds;
4. any future clock-vacuum spectral law must reproduce the frozen target
   without being tuned to it;
5. dimensionless residual coefficients must remain consistent across sectors.

These are not automatic consequences of calibration.

Status:

`calibrated_branch_has_holdout_content`

### 156.4. Allowed future discharge

The calibration anchors can be discharged only if the theory adds or derives a
genuine selection principle:

\[
\mathcal U_{\mathrm{sel}}
\Rightarrow
(\hbar_{\mathrm{obs}},G_N,\Omega_{Gcal,I},\text{sector data})
\]

Examples of admissible selection content:

1. a vacuum-state selection rule;
2. a boundary-condition or cosmological sector selector;
3. a primitive measure over admissible sectors;
4. a stability principle with a unique selected dimensional scale after units
   and readout standards are fixed.

Until such a selector exists, the anchors remain:

`bridge_assumption`.

Status:

`selection_principle_required_to_discharge_anchors`

### 156.5. Claim boundary

Allowed claim:

> Given the calibrated \(\hbar\) and \(G\) anchors for our universe, the
> protolanguage reconstructs and tests cross-sector structure without
> per-domain refit.

Forbidden claim:

> The current primitive language derives the numerical constants \(\hbar\) and
> \(G\).

Forbidden claim:

> Matching \(\hbar\) and \(G\) proves the theory.

Correct status:

`our_universe_calibrated_reconstruction_I = target`.

Status:

`our_universe_selection_claim_boundary_defined`
