## 89. Normalized Kernel-Strain Cost

This section defines the primary candidate for:

$$
\bar c_K(\eta).
$$

It is a candidate dimensionless update cost, not a derivation of \(\hbar_I\).

Status:

`normalized_kernel_strain_cost_initialized`

### 89.1. Before/after kernel states

In a finite active readout sector, let:

$$
G_0\succeq0,
\qquad
G_1\succeq0
$$

be the before/after Gram kernels.

Normalize them as trace-one kernel states:

$$
\rho_0
=
\frac{G_0}{\operatorname{Tr}G_0},
\qquad
\rho_1
=
\frac{G_1}{\operatorname{Tr}G_1}.
$$

This removes overall scale and keeps the distinguishability shape.

Status:

`normalized_kernel_states_defined`

### 89.2. Support alignment

The update support relation:

$$
R_\eta
$$

must provide an alignment map:

$$
\mathsf P_\eta.
$$

The transported before-state is:

$$
\rho_{0\to1}^{(\eta)}
=
\frac{
\mathsf P_\eta\rho_0\mathsf P_\eta^\dagger
}{
\operatorname{Tr}
\left(
\mathsf P_\eta\rho_0\mathsf P_\eta^\dagger
\right)
}.
$$

If no \(\mathsf P_\eta\) is derived, the cost is not derived.

Status:

`support_aligned_before_state_required`

### 89.3. Bures-angle strain cost

Define fidelity:

$$
F(\rho,\sigma)
=
\operatorname{Tr}
\sqrt{
\sqrt{\rho}\sigma\sqrt{\rho}
}.
$$

Define Bures angle:

$$
d_B(\rho,\sigma)
=
\arccos F(\rho,\sigma).
$$

The normalized kernel-strain cost is:

$$
\bar c_K(\eta)
=
d_B^2
\left(
\rho_{0\to1}^{(\eta)},
\rho_1
\right).
$$

Properties:

1. dimensionless;
2. nonnegative;
3. zero if the aligned kernel state is unchanged;
4. invariant under unitary/relabeling transformations of the active basis;
5. independent of \(\hbar_I\), \(G_N\), and Planck units.

Status:

`bures_angle_kernel_strain_cost_defined`

### 89.4. Cycle cost

For a closed update cycle:

$$
\gamma
=
\eta_1\eta_2\cdots\eta_N,
$$

define:

$$
\bar C_{\gamma}^{K}
=
\sum_{r=1}^{N}
\bar c_K(\eta_r).
$$

This gives an additive dimensionless cycle cost.

Status:

`kernel_strain_cycle_cost_defined`

### 89.5. Loss component remains separate

The loss cost:

$$
\bar c_{\mathrm{loss}}(\eta)
=
-\frac12
\log
\det_+
\left(
\mathsf C_\eta^\dagger\mathsf C_\eta
\right)
$$

is not merged into:

$$
\bar c_K
$$

by a free coefficient.

Reason:

a coefficient would become a hidden fitting parameter unless derived independently.

Therefore the theory tracks a two-component candidate:

$$
\left(
\bar C_\gamma^K,
\bar C_\gamma^{\mathrm{loss}}
\right)
$$

until a scalar projection is derived.

Status:

`loss_component_kept_separate_to_avoid_hidden_fit`

### 89.6. Phase-only failure condition

If:

$$
\bar C_\gamma^K=0,
\qquad
\bar C_\gamma^{\mathrm{loss}}=0,
\qquad
\theta_\gamma\ne0,
$$

then the kernel-strain/loss cost route fails for that cycle.

The phase must then come from:

1. topology;
2. connection curvature;
3. independent action-cost obstruction;
4. another non-kernel-strain primitive.

This failure condition is required.

Otherwise the theory would hide phase inside cost after the fact.

Status:

`phase_only_cycles_reject_kernel_strain_cost_route`

### 89.7. Relative gate

For cycles with nonzero:

$$
\theta_\gamma,
\qquad
\bar C_\gamma^K,
$$

define:

$$
\mathcal R_{\theta K}(\gamma,\gamma')
=
\left|
\frac{
\bar C_\gamma^K/\theta_\gamma
}{
\bar C_{\gamma'}^K/\theta_{\gamma'}
}
-1
\right|.
$$

If this residual is small across independently generated cycles, the kernel-strain cost supports a universal relative phase-cost ratio.

If it is not small, the cost route fails or requires a declared residual.

Status:

`kernel_strain_relative_phase_cost_gate_defined`

### 89.8. Known gates

Known phase gates remain:

$$
\Delta\phi=\Delta S/\hbar,
\qquad
\Delta\phi_{AB}
=
\frac{q}{\hbar}
\oint A_\mu dx^\mu,
\qquad
\Delta\phi_{\mathrm{grav}}
\approx
\frac{m g A}{\hbar v}.
$$

The kernel-strain route may be tested against these only after:

1. \(\bar C_\gamma^K\) is derived;
2. \(\theta_\gamma\) is derived;
3. \(A_{0,I}\) is derived if an absolute \(\hbar_I\) is claimed.

Status:

`known_phase_gates_remain_post_derivation_tests`

### 89.9. What is closed

Closed:

1. normalized kernel-state construction;
2. support-aligned Bures-angle strain cost;
3. additive kernel-strain cycle cost;
4. phase-only failure condition;
5. no-fit separation of loss cost.

Open:

1. primitive derivation of \(\mathsf P_\eta\);
2. finite verifier gate for \(\bar c_K\);
3. scalar projection if loss and strain both matter;
4. relation to non-exact holonomy;
5. independent action standard \(A_{0,I}\).

Next target:

create a finite verifier gate for:

$$
(G_0,G_1,\mathsf P_\eta)
\Rightarrow
\bar c_K(\eta).
$$

Relative phase-cost closure gate:

`sections/90-relative-phase-cost-closure-gate.md`

Status:

`normalized_kernel_strain_cost_closed`
