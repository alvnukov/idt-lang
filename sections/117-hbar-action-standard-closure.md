## 117. Hbar Action Standard Closure

Status: `guarded_route`, not numerical derivation.

Target:

`hbar_action_standard_closure_I`

The goal is to make the \(\hbar_I\) route predictive without smuggling in the
observed Planck constant or formulas that already contain it.

### 117.1. What must be derived

The proto-language already has a dimensionless phase-cost route:

$$
\gamma
\Rightarrow
\bar C_\gamma,
\qquad
\gamma
\Rightarrow
\theta_\gamma .
$$

This can test a universal dimensionless ratio, but it cannot produce a
dimensional action constant. A numerical \(\hbar_I\) requires an independent
action unit:

$$
A_{0,I}.
$$

Only then may the theory define

$$
\hbar_I
=
\frac{A_{0,I}\bar C_\gamma}{\theta_\gamma}
$$

on a fixed phase branch.

### 117.2. No-fit protocol

An admissible \(\hbar_I\) derivation must have three disjoint roles:

1. action-standard source:

$$
A_{0,I}
\nLeftarrow
\hbar_{\mathrm{obs}},G_N,\text{Planck units},E=\hbar\omega,p=\hbar k;
$$

2. calibration cycles:

$$
\hbar_I^{(\gamma)}
=
\frac{A_{0,I}\bar C_\gamma}{\theta_\gamma};
$$

3. holdout tests:

$$
E=\hbar_I\omega,
\qquad
p=\hbar_Ik,
\qquad
\Delta\phi=\frac{S}{\hbar_I}.
$$

The known formulas are validation gates. They are not allowed as calibration
inputs for \(A_{0,I}\) or \(\hbar_I\).

### 117.3. Universal action-scale residual

For admissible nonzero fixed-branch cycles define:

$$
\widehat\hbar_\gamma
=
\frac{A_{0,I}\bar C_\gamma}{\theta_\gamma}.
$$

Calibration gives:

$$
\widehat\hbar_{\mathrm{cal}}
=
\left\langle
\widehat\hbar_\gamma
\right\rangle_{\gamma\in\Gamma_{\mathrm{cal}}}.
$$

Validation requires:

$$
\mathcal R_{\hbar}^{\mathrm{val}}(\gamma)
=
\left|
\frac{\widehat\hbar_\gamma}{\widehat\hbar_{\mathrm{cal}}}
-1
\right|
\le
\epsilon_\hbar .
$$

Failure is informative: it means either the phase-cost route is not universal,
the action standard is not independent, or the chosen cycle class is not
admissible.

### 117.4. Machine gates

The manifest now requires:

1. `phase_action_scale_universality_demo`;
2. `action_standard_independence_demo`;
3. `hbar_known_gate_holdout_demo`.

The verifier now registers:

`hbar_action_standard_closure_I`

with dependencies:

1. `A0_I`;
2. `bar_C_gamma`;
3. `theta_gamma`;
4. `hbar_I`.

It rejects:

1. missing route symbols;
2. missing explicit derivation;
3. missing finite gates;
4. premature `derived` status while \(A_{0,I}\), \(\bar C_\gamma\),
   \(\theta_\gamma\), or \(\hbar_I\) remains unclosed;
5. action standards sourced from `hbar_obs`, `G_N`, `planck_units`, or explicit
   \(\hbar\)-formulas;
6. validation cycles whose phase/action estimate does not match the calibrated
   scale.

The next guard strengthens this further: `hbar_I=derived_conditional` is also
rejected when it rests on an open or normalization-only \(A_{0,I}\).

### 117.5. Current status

Closed by this pass:

1. the no-fit structure of the \(\hbar_I\) route;
2. the separation between calibration cycles and holdout formulas;
3. machine guards against hidden \(\hbar_{\mathrm{obs}}\) input;
4. finite validation of \(E=\hbar\omega\), \(p=\hbar k\), and
   \(\Delta\phi=S/\hbar\) as outputs.

Still open:

1. primitive derivation of \(A_{0,I}\);
2. physical cycle class giving real \(\bar C_\gamma,\theta_\gamma\);
3. numerical \(\hbar_I\);
4. first beyond-standard-QM residual.

Current accepted status:

`hbar_I = blocked`

`hbar_action_standard_closure_I = target`

Not accepted:

`numeric_hbar_derived`
