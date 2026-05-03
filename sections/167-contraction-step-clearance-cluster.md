## 167. Contraction-Step Clearance Cluster

Status:

`contraction_step_clearance_cluster_initialized`

This section audits the two nearest blockers of the clock-vacuum pole route:

1. `cross_update_contraction_selection_I`;
2. `fixed_point_step_invariant_I`.

It does not compute \(\omega_{\ell,I}\).

It determines which shortcuts are invalid and which subproblem remains live.

### 167.1. Cross-update contraction result

Block positivity gives:

$$
X_\eta
=
G_1^{1/2}C_\eta G_0^{1/2},
\qquad
\|C_\eta\|\le1.
$$

Maximal recoverability can force \(C_\eta^\dagger C_\eta=I\) on the active
support.

But every active-support isometry has the same recoverability score.

Therefore:

$$
\text{recoverability}
\nRightarrow
\text{phase selection}.
$$

Status:

`recoverability_does_not_select_contraction_phase`

### 167.2. Support matching result

If the update support relation selects a unique matching, it may select the
transport permutation or partial isometry.

It still leaves a diagonal phase freedom:

$$
C_\eta=P_\eta D_\eta.
$$

If \(D_\eta\) is exact endpoint gauge, every closed cycle has:

$$
U_\gamma=1.
$$

So support matching alone cannot supply the non-exact holonomy needed by the
fixed-point route.

Status:

`support_matching_does_not_select_nonexact_holonomy`

### 167.3. Machine target for contraction selection

The target:

`cross_update_contraction_selection_I`

now requires:

1. `cross_update_support_relation_I`;
2. `cross_update_block_kernel_I`;
3. `support_respecting_isometry_I`;
4. `contraction_phase_selection_rule_I`;
5. `non_exact_holonomy_source_I`.

The verifier rejects a derived claim if the route only has recoverability or
support matching but no phase-selection rule.

Status:

`contraction_selection_target_guarded`

### 167.4. Step invariant obstruction

The finite-cycle route demands:

$$
\Theta_*=\frac{2\pi m_*}{N_{\mathrm{cyc}}},
\qquad
\zeta_{\mathrm{step}}=\frac1{N_{1/2}}.
$$

Exact compatibility would imply:

$$
2\pi
=
\frac{N_{\mathrm{cyc}}}{m_*N_{1/2}},
$$

which cannot hold for finite integers.

Therefore exact finite root-of-unity closure plus exact integer half-radar step
count is not an admissible derivation of the step invariant.

Status:

`finite_cycle_integer_step_route_rejected`

### 167.5. Machine target for fixed-point step

The target:

`fixed_point_step_invariant_I`

now requires:

1. `fixed_point_rotation_map_I`;
2. `cycle_rotation_number_I`;
3. `step_clock_readout_rule_I`;
4. `radar_response_pole_relation_I`.

The admissible route must either derive an irrational/coarse-grained step
invariant, or declare the fixed-point pole route underdetermined.

Status:

`fixed_point_step_target_guarded`

### 167.6. No-fit rule

Forbidden:

1. choose the contraction phase that makes \(G_I\) work;
2. treat maximal recoverability as a phase derivation;
3. treat support matching as non-exact holonomy;
4. round \(2\pi\) into an integer cycle identity;
5. choose the step invariant after seeing \(G_N\).

Allowed:

1. derive a non-exact phase from topology, curvature, or action-cost
   obstruction;
2. derive a fixed irrational rotation number from primitive grammar;
3. derive a coarse-grained step rate independent of gravity;
4. pause the clock-vacuum pole route if these objects remain free.

Status:

`contraction_step_no_fit_rule_registered`

### 167.7. Research verdict

This cluster narrows the route again.

The easy path fails:

$$
\text{positivity}
+\text{recoverability}
+\text{support}
\nRightarrow
\omega_{\ell,I}.
$$

The live path is now:

$$
\text{non-exact holonomy source}
\quad\text{or}\quad
\text{irrational/coarse-grained step invariant}.
$$

If neither can be derived from primitive inheritance, the spectral route must
be classified as underdetermined rather than merely incomplete.

Status:

`contraction_step_clearance_cluster_complete`
