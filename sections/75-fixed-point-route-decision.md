## 75. Fixed-Point Route Decision

This section applies the stop condition for the fixed-point route.

Status:

`fixed_point_route_decision_initialized`

### 75.1. Current state

The fixed-point map form is:

$$
F_G(\Theta)
=
\arg
\left[
\sum_w
p(w)e^{-\Lambda_w}
e^{i(b_w\Theta+S_I(w)/\hbar_I)}
\right].
$$

The route has non-fit forms for:

1. \(p(w)\): Perron-Frobenius grammar measure;
2. \(S_I(w)\): action cocycle;
3. \(e^{-\Lambda_w}\): recoverable coherence magnitude.

Status:

`fixed_point_form_available`

### 75.2. Blocking missing input

The blocking missing input is:

$$
\mathfrak s_{ij}
$$

or equivalently:

$$
U_I(\eta_j\leftarrow\eta_i).
$$

Without this primitive phase readout:

$$
S_I(w)
$$

is not computable.

Therefore:

$$
\Theta_*
$$

is not computable.

Status:

`primitive_phase_readout_missing`

### 75.3. Route classification

Current route status:

`structured_but_underived`

More specifically:

`action_constrained_not_derived`

because:

1. positivity does not fix transition phases;
2. reciprocity only constrains signs;
3. additivity only constrains composition;
4. no primitive transition phase readout has been specified.

Status:

`fixed_point_route_classified`

### 75.4. Pause condition

The fixed-point route is paused for numerical prediction until at least one of these is derived:

1. primitive transition phase readout \(U_I(\eta_j\leftarrow\eta_i)\);
2. primitive transition action \(\mathfrak s_{ij}\);
3. non-exact cycle action \(S_I(\gamma)\);
4. a different non-action mechanism fixing \(\Theta_*\) and passing gauge invariance.

Until then, no numerical \(\omega_{\ell,I}\) may be claimed from this route.

Status:

`fixed_point_route_paused_for_prediction`

### 75.5. What remains useful

The route remains useful as a structural scaffold:

$$
\mathcal I,\Gamma_I,K_\eta
\Rightarrow
F_G
\Rightarrow
\Theta_*
\Rightarrow
\omega_{\ell,I}.
$$

It also provides no-fit tests for any future proposed primitive phase rule.

But it is not yet a predictive closure.

Status:

`fixed_point_route_structural_scaffold`

### 75.6. Next viable direction

The next viable direction is not more \(F_G\) algebra.

It is:

$$
\text{primitive phase readout}
\Rightarrow
\mathfrak s_{ij}.
$$

This also attacks the older open problem:

$$
\hbar_I
\Leftarrow
\text{primitive update action}.
$$

Therefore the theory should move from:

$$
\omega_{\ell,I}
$$

back to:

$$
\hbar_I,\quad
\mathfrak s_I,\quad
U_I.
$$

Primitive transition phase readout:

`sections/76-primitive-transition-phase-readout.md`

Status:

`next_direction_primitive_phase_readout`

### 75.7. What is closed

Closed:

1. \(F_G\) form;
2. route classification;
3. pause condition;
4. next viable direction.

Open:

1. primitive phase readout;
2. transition actions;
3. numerical \(\omega_{\ell,I}\);
4. numerical \(G_I\).

Status:

`fixed_point_route_decision_closed`
