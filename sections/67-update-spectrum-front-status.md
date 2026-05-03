## 67. Update Spectrum Front Status

This section summarizes the update-spectrum route after the cycle grammar and step-clock checks.

Status:

`update_spectrum_front_status_initialized`

### 67.1. What is now formalized

The route now has formal objects:

$$
\mathsf T_{EF},
\qquad
\lambda_n,
\qquad
g_n,
\qquad
\Delta\tau_{\mathrm{step}},
\qquad
\omega_{\ell,I}.
$$

and:

$$
\omega_{\ell,I}
=
\min_{n:g_n\neq0}
\frac{|\arg\lambda_n|}
{\Delta\tau_{\mathrm{step}}}.
$$

Status:

`update_spectrum_objects_formalized`

### 67.2. Negative result

The minimal two-state model:

$$
\lambda_\pm=e^{\mp i\theta}
$$

does not derive:

$$
\theta,
\qquad
\Delta\tau_{\mathrm{step}}.
$$

Therefore it is:

`parametric_not_predictive`.

Status:

`two_state_negative_result_recorded`

### 67.3. Finite-cycle obstruction

Finite cycle closure gives:

$$
\theta_*=\frac{2\pi m_*}{N_{\mathrm{cyc}}}.
$$

Exact integer step counting in a half-radar interval gives:

$$
\theta_*=\frac1{N_{1/2}}.
$$

Together:

$$
2\pi
=
\frac{N_{\mathrm{cyc}}}
{m_*N_{1/2}},
$$

which cannot hold exactly for finite integers.

Thus exact finite-cycle closure plus exact integer radar-step counting is rejected.

Status:

`finite_cycle_obstruction_recorded`

### 67.4. Remaining viable route

The remaining viable update-spectrum route is:

$$
\text{fixed-point rotation grammar}
\Rightarrow
\Theta_*
$$

and:

$$
\text{clock-readout step rule}
\Rightarrow
\zeta_{\mathrm{step}}.
$$

Closure requires:

$$
\Theta_*=\zeta_{\mathrm{step}}
$$

without tuning.

Status:

`fixed_point_route_remaining`

### 67.5. Stop condition

The update-spectrum route should stop if:

1. no derived \(F_G\) is available;
2. \(\zeta_{\mathrm{step}}\) remains free;
3. \(\Theta_*\) is chosen only to hit \(\omega_{\ell,G}\);
4. fixed-point grammar adds arbitrary structure not grounded in \(\mathcal I,\Gamma_I,K_\eta\).

In that case the theory must report:

`update_spectrum_underived`

and move to another independent route.

Status:

`update_spectrum_stop_condition`

### 67.6. Next hard problem

The next hard problem is:

$$
\mathcal I,\Gamma_I,K_\eta
\Rightarrow
F_G.
$$

The most plausible candidate is:

$$
F_G
\Leftarrow
\text{positivity-preserving kernel normalization under coarse-graining}.
$$

This is not yet done.

Status:

`next_hard_problem_kernel_normalization_map`

### 67.7. What is closed

Closed:

1. update-spectrum formal route;
2. two-state negative result;
3. finite-cycle obstruction;
4. fixed-point closure criterion;
5. stop condition.

Open:

1. explicit \(F_G\);
2. explicit \(\zeta_{\mathrm{step}}\);
3. numerical \(\omega_{\ell,I}\);
4. final \(G_I\) prediction.

Next target:

derive the kernel-normalization coarse-graining map \(F_G\) or pause the update-spectrum route as underdetermined.

Kernel normalization map:

`sections/68-kernel-normalization-map.md`

Status:

`update_spectrum_front_reduced_to_FG`
