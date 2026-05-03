## 149. Deadlock Exit Route

Status:

`deadlock_exit_route_registered`

This section records the result of the direct attempt to move past the current
anchor deadlock.

The deadlock is not a missing algebraic manipulation. It is a scale-lock
problem:

\[
A_{0,I}=W_{0,I}\tau_{0,I}
\Rightarrow
\hbar_I
\]

requires an independently locked tick scale and an independently locked
work/mass scale.

### 149.1. Direct L2+W1 attempt

The strongest previously selected move was:

\[
\text{L2: primitive update spectrum}
\quad+\quad
\text{W1: inertial response}.
\]

This attempt does not close the action scale.

L2 can improve the dimensionless phase-step route:

\[
\mathsf T_{EF}
\Rightarrow
\Theta_*,
\qquad
\Theta_*=\zeta_{\mathrm{step}}
\]

but it does not by itself lock the physical tick:

\[
\tau_{0,I}.
\]

W1 gives an inertial ratio:

\[
m_I=\frac{J_I}{\Delta v},
\]

but without an independently locked impulse scale \(J_I\), this is still not a
work/mass lock.

Therefore the current result is:

`L2_W1_improves_structure_not_anchor`.

Not accepted:

`tick_scale_locked`.

Not accepted:

`work_scale_locked`.

Not accepted:

`hbar_I = derived_conditional`.

### 149.2. No recycle rule

The theory must not define the missing impulse or work scale from the same
action object it is trying to derive.

Forbidden recycle:

\[
\Theta_\gamma,\bar C_\gamma
\Rightarrow
A_{0,I}
\Rightarrow
J_I,W_{0,I}
\Rightarrow
A_{0,I}.
\]

Equally forbidden:

\[
p=\hbar k,
\qquad
E=\hbar\omega,
\qquad
G_N,
\qquad
\text{Planck units},
\qquad
\text{spectroscopy}.
\]

If a proposed work/mass lock uses any of these as source data, it is not a
deadlock exit. It is an import.

Status:

`action_anchor_recycle_forbidden`.

### 149.3. Actual exit: dimensionless Mode C route

The nearest non-stalled route is not an immediate numerical \(\hbar_I\).

The nearest route is a dimensionless no-refit prediction:

\[
\mathcal K_\eta
\Rightarrow
C_\eta=G_1^{-1/2}X_\eta G_0^{-1/2}
\Rightarrow
\left(
T_\eta=\frac{\det C_\eta}{|\det C_\eta|},
\bar c_K(\eta)
\right)
\]

and for pre-registered cycles:

\[
U_\gamma=\prod_{\eta\in\gamma}T_\eta,
\qquad
\Theta_\gamma=\arg U_\gamma+2\pi n_\gamma,
\qquad
\bar C_\gamma^K=\sum_{\eta\in\gamma}\bar c_K(\eta).
\]

The test object is the dimensionless relative slope:

\[
\lambda_{\theta C}^{(\gamma)}
=
\frac{\Theta_\gamma}{\bar C_\gamma^K}.
\]

This does not derive \(A_{0,I}\). It can still create Mode C value if the same
\(\lambda_{\theta C}\) survives a pre-registered validation family without
refitting.

Accepted target:

`dimensionless_phase_cost_prediction_route`.

Not accepted:

`A0_I = derived_conditional`.

Not accepted:

`hbar_I = derived_conditional`.

### 149.4. Acceptance rule

The dimensionless route can be upgraded only if all of the following are fixed
before validation:

1. the source of finite or continuum spectral block kernels \(\mathcal K_\eta\);
2. the active cycle family;
3. branch and winding policy \(n_\gamma\);
4. calibration cycles;
5. validation cycles;
6. residual tolerance for \(\lambda_{\theta C}\);
7. no \(\hbar\), \(G_N\), Planck-unit, spectroscopy, or postfit residual input.

The phase and the cost must come from the same spectral block family. A copied
phase ledger or separate fitted cost ledger does not count.

If validation passes, the status may become:

`route_improved_not_hbar`.

If validation fails, the status must become:

`dimensionless_phase_cost_route_rejected`.

### 149.5. Stop condition

Stop this route if the next work only creates another toy spectral block.

The next accepted work must do at least one of:

1. derive a non-toy \(\mathcal K_\eta\) family from primitive inheritance;
2. extract \(\mathcal K_\eta\) from a declared experimental fixture without
   using the validation residual;
3. pre-register a calibration/validation cycle split and run it unchanged;
4. reject the dimensionless phase-cost route.

Until then, the theory is out of the false `derive_hbar_now` loop, but not yet
out of the physical-anchor problem.
