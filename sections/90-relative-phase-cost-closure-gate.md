## 90. Relative Phase-Cost Closure Gate

This section defines the first closure test between:

$$
\bar C_\gamma
$$

and:

$$
U_\gamma.
$$

It is dimensionless.

It does not compute numerical \(\hbar_I\).

Status:

`relative_phase_cost_closure_gate_initialized`

### 90.1. Branch-safe phase

Cycle holonomy gives:

$$
\theta_\gamma
=
\operatorname{Arg}U_\gamma
\in
(-\pi,\pi].
$$

Action comparison needs an unwrapped phase:

$$
\Theta_\gamma
=
\theta_\gamma+2\pi n_\gamma,
\qquad
n_\gamma\in\mathbb Z.
$$

The branch integer:

$$
n_\gamma
$$

cannot be chosen after comparing with experiments.

It must be fixed by:

1. continuity under refinement;
2. primitive cycle grammar;
3. declared winding/topology;
4. a pre-registered small-cycle branch convention.

Status:

`phase_branch_gate_defined`

### 90.2. Dimensionless slope

For admissible cycles with:

$$
\bar C_\gamma^K>0,
\qquad
\Theta_\gamma\ne0,
$$

define:

$$
\lambda_{\theta C}^{(\gamma)}
=
\frac{\Theta_\gamma}{\bar C_\gamma^K}.
$$

This is dimensionless.

If the kernel-strain route is correct for phase/action comparison, then:

$$
\lambda_{\theta C}^{(\gamma)}
\approx
\lambda_{\theta C,I}
$$

for independent admissible cycles.

Status:

`dimensionless_phase_cost_slope_defined`

### 90.3. Relative closure residual

For two cycles:

$$
\gamma,\gamma',
$$

define:

$$
\mathcal R_{\theta C}^{K}(\gamma,\gamma')
=
\left|
\frac{
\lambda_{\theta C}^{(\gamma)}
}{
\lambda_{\theta C}^{(\gamma')}
}
-1
\right|.
$$

The closure condition is:

$$
\mathcal R_{\theta C}^{K}
\le
\epsilon_{\theta C}
$$

across a pre-declared cycle set.

Failure is not repaired by:

1. changing branches;
2. adding loss cost with a fitted coefficient;
3. changing cycle selection after the result.

Status:

`relative_phase_cost_residual_defined`

### 90.4. Relation to \(\hbar_I\)

If a non-circular action standard exists:

$$
C_\gamma
=
A_{0,I}\bar C_\gamma^K,
$$

and:

$$
\Theta_\gamma
=
\frac{C_\gamma}{\hbar_I},
$$

then:

$$
\lambda_{\theta C,I}
=
\frac{A_{0,I}}{\hbar_I}.
$$

Therefore:

$$
\hbar_I
=
\frac{A_{0,I}}{\lambda_{\theta C,I}}.
$$

This shows exactly what remains missing:

$$
A_{0,I}.
$$

Status:

`hbar_from_action_standard_and_dimensionless_slope`

### 90.5. Zero-cost and zero-phase cases

If:

$$
\bar C_\gamma^K=0,
\qquad
\Theta_\gamma=0,
$$

the cycle is neutral for this test.

If:

$$
\bar C_\gamma^K>0,
\qquad
\Theta_\gamma=0,
$$

the cycle contributes strain without phase.

If:

$$
\bar C_\gamma^K=0,
\qquad
\Theta_\gamma\ne0,
$$

the kernel-strain phase/action route fails for that cycle.

Status:

`zero_case_classification_defined`

### 90.6. Known gates

The closure gate must be compatible with known phase universality:

$$
\Delta\phi
=
\Delta S/\hbar,
\qquad
p=\hbar k,
\qquad
E=\hbar\omega.
$$

But these are not used to set:

$$
\lambda_{\theta C,I}.
$$

They become tests only after:

1. \(\bar C_\gamma^K\) is fixed;
2. branch rules are fixed;
3. \(A_{0,I}\) is fixed.

Status:

`known_phase_universality_gates_after_closure`

### 90.7. No-fit rule

Forbidden:

1. choose \(n_\gamma\) to reduce \(\mathcal R_{\theta C}^{K}\);
2. drop cycles whose slope differs;
3. mix \(\bar C^K\) and \(\bar C^{\mathrm{loss}}\) using a fitted coefficient;
4. use observed \(\hbar\) to select \(\lambda_{\theta C,I}\).

Allowed:

1. pre-register admissible cycle sets;
2. classify route failure by residual;
3. introduce a declared residual sector if cycles split into stable families;
4. keep \(\hbar_I\) blocked until \(A_{0,I}\) is derived.

Status:

`relative_phase_cost_no_fit_rule`

### 90.8. What is closed

Closed:

1. branch-safe phase-cost slope;
2. relative closure residual;
3. exact relation \(\lambda_{\theta C,I}=A_{0,I}/\hbar_I\);
4. zero-case classification;
5. no-fit branch rule.

Open:

1. primitive branch rule;
2. pre-registered cycle set;
3. finite verifier gate for \(\mathcal R_{\theta C}^{K}\);
4. independent action standard \(A_{0,I}\).

Next target:

derive or reject the branch rule:

$$
U_\gamma
\Rightarrow
\Theta_\gamma.
$$

Phase branch reconstruction gate:

`sections/91-phase-branch-reconstruction-gate.md`

Status:

`relative_phase_cost_closure_gate_closed`
