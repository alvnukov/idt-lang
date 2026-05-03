## 91. Phase Branch Reconstruction Gate

This section defines when a modulo phase:

$$
U_\gamma\in U(1)
$$

can be lifted to an unwrapped phase:

$$
\Theta_\gamma\in\mathbb R.
$$

Status:

`phase_branch_reconstruction_gate_initialized`

### 91.1. Holonomy lift

The holonomy gives:

$$
U_\gamma
=
e^{i\theta_\gamma}.
$$

A branch reconstruction is a lift:

$$
\mathcal L:
U_\gamma
\mapsto
\Theta_\gamma
$$

such that:

$$
e^{i\Theta_\gamma}
=
U_\gamma.
$$

Therefore:

$$
\Theta_\gamma
=
\theta_\gamma+2\pi n_\gamma,
\qquad
n_\gamma\in\mathbb Z.
$$

Status:

`phase_lift_defined`

### 91.2. Additivity requirement

For composable cycles:

$$
\gamma\circ\gamma',
$$

the lift must satisfy:

$$
\Theta_{\gamma\circ\gamma'}
=
\Theta_\gamma+\Theta_{\gamma'}.
$$

For repeated cycles:

$$
\Theta_{\gamma^m}
=
m\Theta_\gamma.
$$

This prevents independent branch choices per cycle.

Status:

`branch_additivity_required`

### 91.3. Orientation requirement

For the reversed cycle:

$$
\gamma^{-1},
$$

the lift must satisfy:

$$
\Theta_{\gamma^{-1}}
=
-\Theta_\gamma.
$$

This matches:

$$
U_{\gamma^{-1}}
=
\overline{U_\gamma}.
$$

Status:

`branch_orientation_required`

### 91.4. Small-cycle principal branch

If a cycle belongs to a pre-declared small deformation family:

$$
\gamma(\epsilon),
\qquad
\gamma(0)=\mathrm{id},
$$

and:

$$
U_{\gamma(0)}=1,
$$

then the allowed lift is the continuous one with:

$$
\Theta_{\gamma(0)}=0.
$$

For sufficiently small \(\epsilon\):

$$
\Theta_{\gamma(\epsilon)}
=
\operatorname{Arg}U_{\gamma(\epsilon)}
$$

on the principal branch.

Status:

`small_cycle_continuity_branch_rule`

### 91.5. Global topology and winding

For non-contractible cycles, the lift may require winding data:

$$
w_\gamma\in\mathbb Z.
$$

Then:

$$
\Theta_\gamma
=
\operatorname{Arg}U_\gamma+2\pi w_\gamma.
$$

The winding:

$$
w_\gamma
$$

must be derived from primitive topology or grammar.

If it is not derived, the unwrapped phase is not derived.

Status:

`global_branch_requires_topological_winding`

### 91.6. Branch residual

For a proposed lift, define:

$$
\mathcal R_{\mathrm{branch}}
(\gamma,\gamma')
=
\left|
\Theta_{\gamma\circ\gamma'}
-\Theta_\gamma
-\Theta_{\gamma'}
\right|.
$$

Accepted branch rules require:

$$
\mathcal R_{\mathrm{branch}}=0
$$

up to the declared tolerance of the finite or continuum model.

Status:

`branch_additivity_residual_defined`

### 91.7. Known gates

Interference measurements observe phase modulo:

$$
2\pi.
$$

Action accumulation uses unwrapped phase through continuity:

$$
\Delta S/\hbar.
$$

Aharonov-Bohm phases are also periodic modulo \(2\pi\), while flux winding and charge sector determine global branch interpretation.

Therefore known experiments support the distinction:

$$
U_\gamma
\quad
\text{observable modulo phase},
$$

versus:

$$
\Theta_\gamma
\quad
\text{lifted action comparison variable}.
$$

Status:

`known_phase_gates_support_modulo_vs_lifted_distinction`

### 91.8. No-fit rule

Forbidden:

1. choose \(n_\gamma\) to minimize \(\mathcal R_{\theta C}^{K}\);
2. choose winding after comparing with observed \(\hbar\);
3. use global topology that is not present in the primitive grammar;
4. mix principal branches and lifted branches without declaring the cycle family.

Allowed:

1. principal branch for pre-declared small contractible cycles;
2. integer winding from primitive topology;
3. route failure if branch additivity cannot be satisfied;
4. separate modulo-phase gates from lifted-action gates.

Status:

`phase_branch_no_fit_rule`

### 91.9. What is closed

Closed:

1. lift definition;
2. additivity and orientation requirements;
3. small-cycle principal branch rule;
4. global winding requirement;
5. branch residual.

Open:

1. primitive topology / winding derivation;
2. finite verifier gate for branch additivity;
3. admissible cycle-family registry;
4. branch-safe \(\mathcal R_{\theta C}^{K}\) calculation.

Next target:

define admissible cycle families:

$$
\mathcal G_{\mathrm{cycle}}
\Rightarrow
\{\gamma_a\}
\Rightarrow
\Theta_{\gamma_a}.
$$

Admissible cycle family registry:

`sections/92-admissible-cycle-family-registry.md`

Status:

`phase_branch_reconstruction_gate_closed`
