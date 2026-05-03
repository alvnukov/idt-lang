## 168. Holonomy Source Clearance Cluster

Status:

`holonomy_source_clearance_cluster_initialized`

This section audits the nearest live branch left by Section 167:

`non_exact_holonomy_source_I`.

It does not derive \(G_I\), \(\omega_{\ell,I}\), or a physical value of the
cycle phase.

It separates three statements that were previously too close:

1. a finite transfer readout can compute a unit phase;
2. a cycle composition can compute a holonomy;
3. a non-exact physical source for that holonomy has been derived.

Only the first two are machine-checkable in the current primitive set.

### 168.1. Primitive transition phase readout

For a finite transfer element \(T_\eta\), the verifier can read:

$$
u_\eta=\frac{T_\eta}{|T_\eta|}.
$$

For a finite cycle \(\gamma=(a_0,\ldots,a_n)\), it can then compute:

$$
U_\gamma=\prod_i u_{a_i a_{i+1}}.
$$

This is a valid transition-phase readout.

It is not a physical source by itself.

Status:

`transition_phase_readout_machine_guarded`

### 168.2. Branch and winding boundary

The lifted phase \(\Theta_\gamma\) is only meaningful after a branch rule is
fixed before comparison.

The verifier therefore accepts only additive lifted branches:

$$
\Theta_{\gamma_1\gamma_2}
=
\Theta_{\gamma_1}
+
\Theta_{\gamma_2}.
$$

But the winding rule must come from primitive topology, graph grammar, or an
equivalent predeclared structure.

Choosing the branch after seeing \(G_N\), \(\hbar_{\mathrm{obs}}\), or a target
frequency is a post-fit move.

Status:

`phase_branch_postfit_route_rejected`

### 168.3. Cost independence boundary

A phase-cost relation is admissible only if the cost is defined independently
of the phase being tested.

Invalid:

$$
C_\gamma := f(\Theta_\gamma)
\quad\Rightarrow\quad
\Theta_\gamma \sim C_\gamma.
$$

That is circular.

The live cost candidates are kernel strain, spectral kernel strain, or another
primitive ledger computed before phase comparison.

Status:

`phase_defined_cost_rejected_as_source`

### 168.4. Non-exact source classes

The current admissible source classes are:

1. discrete curvature;
2. topological winding;
3. action-cost obstruction;
4. source-coupled phase response.

If the cocycle is exact, or if the class is `none`, the route cannot claim a
non-exact source.

If the source class is only `target`, it may remain a research target but not a
derived physical input.

Status:

`non_exact_source_classification_guarded`

### 168.5. Machine targets

The target:

`primitive_transition_phase_readout_I`

now requires:

1. `cross_update_block_kernel_I`;
2. `transfer_phase_normalization_I`;
3. `cycle_holonomy_composition_I`;
4. `phase_branch_reconstruction_I`.

The target:

`non_exact_holonomy_source_I`

now requires:

1. `primitive_transition_phase_readout_I`;
2. `phase_branch_reconstruction_I`;
3. `holonomy_source_classification_I`;
4. `phase_cost_independence_I`.

Both targets forbid calibrated quantum/gravity anchors as derivation sources.

Status:

`holonomy_source_targets_guarded`

### 168.6. Research verdict

The route is not dead, but it is still not unlocked.

The finite machinery can compute:

$$
T_\eta
\Rightarrow
u_\eta
\Rightarrow
U_\gamma
\Rightarrow
\Theta_\gamma.
$$

It still cannot infer:

$$
U_\gamma\ne 1
\quad\text{as a physical non-exact source}.
$$

The next live path is therefore narrower:

derive graph curvature, primitive winding, or an independent action-cost
obstruction before using the holonomy in the clock-vacuum pole route.

Until that happens, `non_exact_holonomy_source_I` remains `target`, not
`derived`.

Status:

`holonomy_source_clearance_cluster_complete`
