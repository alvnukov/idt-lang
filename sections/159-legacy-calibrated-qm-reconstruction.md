## 159. Legacy Calibrated QM Reconstruction

Status:

`legacy_calibrated_qm_reconstruction_initialized`

This section closes the QM tail that can honestly be closed after the legacy constant-anchor correction.

The theory no longer tries to derive the numerical value of \(\hbar\) inside
the QM route.

It uses:

`calibrated_hbar_I`

as the our-universe action-phase anchor, then checks that the same anchor
supports the whole finite and continuum QM reconstruction without per-domain
refit.

### 159.1. Split of claims

The old target:

`full_QM_I = derived`

remains not accepted.

Reason:

`hbar_I = blocked`

as a first-principles dimensional derivation.

The legacy calibrated target is:

`calibrated_QM_reconstruction_I`.

It means:

given the single action anchor `calibrated_hbar_I`, reconstruct the operational
QM spine:

1. amplitude packets;
2. Born/context readout;
3. reversible unitary evolution;
4. continuum frequency generator;
5. Hamiltonian and momentum scales;
6. de Broglie and canonical sectors;
7. measurement contexts;
8. apparatus/facticity gates.

Status:

`full_QM_split_from_calibrated_QM`

### 159.2. Calibrated dynamics

The generator route remains anchor-free:

\[
i\partial_t\psi=\Omega_I\psi.
\]

The calibrated energy operator is:

\[
H_I^{cal}
=
calibrated\_hbar_I\,\Omega_I.
\]

Manifest symbol:

`calibrated_hamiltonian_energy_operator_I`.

This is not a derivation of \(\hbar_I\).

It is the calibrated energy readout for the selected universe sector.

Status:

`calibrated_H_from_frequency_generator`

### 159.3. Calibrated translation and momentum

The spatial generator route remains:

\[
T(a)=e^{-iak_I}.
\]

The calibrated momentum operator is:

\[
p_I^{cal}
=
calibrated\_hbar_I\,k_I.
\]

Manifest symbol:

`calibrated_momentum_operator_I`.

The de Broglie relation becomes a calibrated readout identity:

\[
\lambda
=
\frac{2\pi}{|k_I|}
=
\frac{h_I^{cal}}{|p_I^{cal}|}.
\]

Manifest symbol:

`calibrated_de_broglie_relation_I`.

Status:

`calibrated_translation_momentum_closure`

### 159.4. Calibrated canonical sector

The finite gate remains the Weyl relation:

\[
ZX=e^{2\pi i/N}XZ.
\]

The continuum tangent sector becomes:

\[
[x,k_I]=i,
\qquad
[x,p_I^{cal}]=i\,calibrated\_hbar_I.
\]

Manifest symbol:

`calibrated_canonical_commutator_I`.

This closes the canonical readout for the calibrated branch, while preserving
the earlier warning that exact finite-dimensional canonical commutators are
impossible.

Status:

`calibrated_canonical_sector_closed_conditionally`

### 159.5. Apparatus and facticity tail

The remaining measurement tail is now handled as a finite operational closure:

1. pointer sectors pass the stability gate;
2. premeasurement preserves Born weights while suppressing off-diagonal
   apparatus coherence;
3. recoverability loss separates reversible erasure from stable facticity.

These are already represented by:

1. `pointer_sector_stability_demo`;
2. `premeasurement_decoherence_demo`;
3. `recoverability_loss_demo`.

The status is not:

`collapse_postulate_derived`.

The status is:

`apparatus_facticity_math_closed_conditional`.

Status:

`apparatus_facticity_tail_closed_for_calibrated_QM`

### 159.6. Legacy machine guard

The manifest now registers:

`calibrated_QM_reconstruction_I = derived_conditional`.

The verifier requires an explicit derivation containing:

1. finite amplitude/Born/unitary spine;
2. continuum generator closure;
3. `calibrated_hbar_I`;
4. calibrated Hamiltonian and momentum operators;
5. calibrated de Broglie and canonical sectors;
6. observable context;
7. apparatus context dynamics;
8. measurement facticity.

It rejects:

1. missing calibrated-QM derivation;
2. premature `derived` status while required nodes remain open or target;
3. silently replacing `calibrated_hbar_I` with `hbar_I`.

Status:

`calibrated_QM_machine_guard_registered`

### 159.7. Final legacy QM status

Closed for the legacy calibrated branch:

`calibrated_QM_reconstruction_I = derived_conditional`

with explicit route and machine guard.

The calibrated closure is decomposed into:

1. `calibrated_qm_continuum_closure_I = derived_conditional`;
2. `calibrated_qm_generator_translation_closure_I = derived_conditional`;
3. `calibrated_qm_apparatus_facticity_closure_I = derived_conditional`;
4. `calibrated_qm_dynamics_action_facticity_closure_I = derived_conditional`.

Still not accepted:

`full_QM_I = derived`.

Still open outside the calibrated QM route:

1. first-principles numerical \(\hbar_I\);
2. primitive proof that all admissible update networks have the required
   continuum limit;
3. primitive derivation of macroscopic apparatus sectors;
4. beyond-standard-QM residual prediction.

Therefore the QM tail is closed in the only honest legacy calibrated sense:

calibrated operational reconstruction, not first-principles derivation of all
dimensional constants.

Status:

`legacy_QM_tail_closed_as_calibrated_reconstruction`
