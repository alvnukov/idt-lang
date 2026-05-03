## 88. Dimensionless Cycle Cost Front

This section starts the route:

$$
\gamma
\Rightarrow
\bar C_\gamma.
$$

It does not compute a numerical \(\hbar_I\).

It defines what a non-circular dimensionless cycle cost must satisfy.

Status:

`dimensionless_cycle_cost_front_initialized`

### 88.1. Required object

For a closed update cycle:

$$
\gamma
=
\eta_1\eta_2\cdots\eta_N,
$$

the target is:

$$
\bar C_\gamma
\in
\mathbb R_{\ge0}.
$$

It must be dimensionless and defined without:

1. \(\hbar_I\);
2. observed \(\hbar\);
3. \(G_N\);
4. Planck units;
5. fitted phase data.

Status:

`cycle_cost_target_defined`

### 88.2. Additivity requirement

The elementary cost must satisfy:

$$
\bar C_\gamma
=
\sum_{\eta\in\gamma}
\bar c_I(\eta)
$$

or, if the cost is not edge-local, an explicitly declared composition rule:

$$
\bar C_{\gamma\circ\gamma'}
=
\bar C_\gamma+\bar C_{\gamma'}.
$$

Without additive or composable structure, the ratio:

$$
\frac{\bar C_\gamma}{\theta_\gamma}
$$

cannot test a universal phase/action scale.

Status:

`cycle_cost_additivity_required`

### 88.3. Gauge and relabeling invariance

The cost cannot depend on endpoint phase labels:

$$
a_i\mapsto e^{i\alpha_i}a_i.
$$

Therefore:

$$
\bar C_\gamma
$$

must be a function of gauge-invariant update data:

1. kernel spectra;
2. support relations;
3. contraction singular values;
4. invariant distances between normalized kernel states;
5. topology or cycle structure.

Status:

`cycle_cost_gauge_invariance_required`

### 88.4. Loss-only cost is insufficient

A natural dimensionless candidate is recoverability loss:

$$
\bar c_{\mathrm{loss}}(\eta)
=
-\frac12
\log
\det_+
\left(
\mathsf C_\eta^\dagger\mathsf C_\eta
\right).
$$

This is dimensionless, nonnegative, and zero for lossless isometries.

But it cannot be the whole action-cost route.

Reason:

many known phase gates occur in nearly lossless sectors:

$$
\mathsf C_\eta^\dagger\mathsf C_\eta
\approx
I,
$$

while:

$$
\operatorname{Arg}U_\gamma
\ne
0.
$$

Therefore loss-only cost can quantify irreversibility, but cannot by itself source phase/action universality.

Status:

`loss_only_cost_rejected_as_complete_action_cost`

### 88.5. Pure phase cost is circular

Forbidden:

$$
\bar C_\gamma
=
|\operatorname{Arg}U_\gamma|.
$$

This would make:

$$
\bar C_\gamma/\theta_\gamma
=
1
$$

by definition.

That is not a derivation of phase/action scale.

Status:

`phase_defined_cost_rejected_as_circular`

### 88.6. Candidate cost classes

Allowed candidate classes:

1. kernel-strain distance between before/after normalized distinguishability states;
2. support-transport complexity derived from \(R_\eta\);
3. contraction-loss cost for irreversible sectors;
4. grammar surprisal from a pre-derived Perron-Frobenius update grammar;
5. topological obstruction count if topology is derived before phase comparison.

Only a candidate fixed before phase comparison can enter:

$$
\mathcal R_{\hbar}^{\mathrm{rel}}
$$

as a real test.

Status:

`cycle_cost_candidate_classes_registered`

### 88.7. Primary route selection

The primary route is kernel-strain cost:

$$
(G_0,G_1,\mathsf C_\eta,R_\eta)
\Rightarrow
\bar c_K(\eta).
$$

Reason:

1. it uses existing primitive verifier objects;
2. it is independent of observed \(\hbar\);
3. it can be checked on finite models;
4. it does not require gravitational data;
5. it can distinguish lossless-but-strained updates from no-op updates.

Status:

`kernel_strain_cost_route_selected`

### 88.8. Relative phase-cost gate

Once:

$$
\bar C_\gamma
$$

and:

$$
\theta_\gamma
=
\operatorname{Arg}U_\gamma
$$

are independently derived, the first non-dimensional test is:

$$
\mathcal R_{\hbar}^{\mathrm{rel}}(\gamma,\gamma')
=
\left|
\frac{
\bar C_\gamma/\theta_\gamma
}{
\bar C_{\gamma'}/\theta_{\gamma'}
}
-1
\right|.
$$

This tests universality of the phase/cost ratio.

It still does not yield a numerical dimensional \(\hbar_I\) without:

$$
A_{0,I}.
$$

Status:

`relative_phase_cost_gate_reaffirmed`

### 88.9. What is closed

Closed:

1. \(\bar C_\gamma\) requirements;
2. loss-only insufficiency;
3. pure phase-cost circularity;
4. primary route selection: kernel-strain cost.

Open:

1. exact definition of \(\bar c_K(\eta)\);
2. finite verifier gate for \(\bar c_K\);
3. relation between \(\bar C_\gamma\) and \(\theta_\gamma\);
4. independent dimensional action standard \(A_{0,I}\).

Next target:

define normalized kernel-strain cycle cost:

$$
(G_0,G_1,R_\eta,\mathsf C_\eta)
\Rightarrow
\bar c_K(\eta)
\Rightarrow
\bar C_\gamma.
$$

Normalized kernel-strain cost:

`sections/89-normalized-kernel-strain-cost.md`

Status:

`dimensionless_cycle_cost_front_closed`
