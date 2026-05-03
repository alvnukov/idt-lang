## 66. Fixed-Point Rotation Grammar

This section replaces exact finite-cycle phase-lock with a possible fixed-point rotation rule.

It is a route around the finite integer obstruction.

It is not yet a numerical derivation.

Status:

`fixed_point_rotation_grammar_initialized`

### 66.1. Rotation number

Let the primitive update grammar induce a rotation number:

$$
\Theta_*
\in
\mathbb R/2\pi\mathbb Z
$$

for the first strain-coupled transfer mode.

Then:

$$
\lambda_*
=
e^{-i\Theta_*}.
$$

The link frequency is:

$$
\omega_{\ell,I}
=
\frac{|\Theta_*|}
{\Delta\tau_{\mathrm{step}}}.
$$

Status:

`primitive_rotation_number_defined`

### 66.2. Fixed-point condition

Instead of:

$$
\mathsf T^N=I,
$$

use a grammar renormalization map:

$$
\mathcal R_G:
\Theta\mapsto F_G(\Theta).
$$

A stable primitive rotation is a fixed point:

$$
\Theta_*
=
F_G(\Theta_*).
$$

with:

$$
|F_G'(\Theta_*)|<1.
$$

This can generate an irrational rotation without finite root-of-unity closure.

Status:

`grammar_rotation_fixed_point`

### 66.3. Clock-step compatibility

The step clock rule gives:

$$
\zeta_{\mathrm{step}}
=
\Delta\tau_{\mathrm{step}}\omega_{\ell,I}.
$$

Therefore:

$$
\Theta_*=\zeta_{\mathrm{step}}.
$$

The fixed-point route closes only if the same grammar/readout dynamics gives both:

$$
\Theta_*
\quad\text{and}\quad
\zeta_{\mathrm{step}}
$$

with:

$$
\Theta_*-\zeta_{\mathrm{step}}
=
0
\pm
\epsilon_{\Theta}.
$$

Status:

`fixed_point_step_compatibility`

### 66.4. Candidate fixed-point sources

Allowed sources for \(F_G\):

1. coarse-graining of update words;
2. stationary distribution of update transitions;
3. positivity-preserving kernel normalization;
4. reciprocity plus clock universality;
5. stability of the first clock-vacuum pole.

Forbidden sources:

1. \(G_N\);
2. Planck frequency;
3. post-hoc matching to \(\omega_{\ell,G}\);
4. experimental residuals used before the grammar is fixed.

Status:

`fixed_point_sources_declared`

### 66.5. Closure condition

The fixed-point rotation route is closed only if:

$$
\mathcal I,\Gamma_I,K_\eta
\Rightarrow
F_G
\Rightarrow
\Theta_*
$$

and:

$$
\mathcal I,\Gamma_I,K_\eta,\text{clock readout}
\Rightarrow
\zeta_{\mathrm{step}}.
$$

Then:

$$
\Theta_*=\zeta_{\mathrm{step}}
$$

must hold without tuning.

If either \(F_G\) or \(\zeta_{\mathrm{step}}\) remains free, status is:

`parametric_not_predictive`.

Status:

`fixed_point_closure_condition`

### 66.6. No-fit rule

Forbidden:

1. choose \(F_G\) to reproduce \(G_N\);
2. choose \(\Theta_*\) from \(\omega_{\ell,G}\);
3. call irrationality itself a derivation;
4. move \(\epsilon_\Theta\) after seeing gravity comparison.

Allowed:

1. use fixed-point grammar to avoid exact finite-cycle obstruction;
2. reject the route if \(F_G\) is not derived;
3. carry \(\Theta_*-\zeta_{\mathrm{step}}\) as a residual.

Status:

`fixed_point_rotation_no_fit_rule`

### 66.7. What is closed

Closed:

finite root-of-unity closure is not the only grammar option.

Closed:

fixed-point rotation grammar has a precise closure test:

$$
\Theta_*
=
\zeta_{\mathrm{step}}.
$$

Open:

1. explicit \(F_G\);
2. explicit \(\Theta_*\);
3. explicit \(\zeta_{\mathrm{step}}\);
4. numerical \(\omega_{\ell,I}\).

Next target:

derive or propose the simplest non-arbitrary \(F_G\) from positivity-preserving kernel normalization.

Update spectrum front status:

`sections/67-update-spectrum-front-status.md`

Kernel normalization map:

`sections/68-kernel-normalization-map.md`

Status:

`fixed_point_route_defined_not_solved`
