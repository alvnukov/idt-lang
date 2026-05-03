## 63. Update Spectrum Closure Criteria

This section defines when the update-spectrum route counts as a real derivation of:

$$
\omega_{\ell,I}.
$$

It prevents a free spectral parametrization from being mistaken for a prediction.

Status:

`update_spectrum_closure_criteria_initialized`

### 63.1. Required objects

A closed update-spectrum derivation must specify:

1. local update set:

$$
\mathcal U_{EF};
$$

2. transition weights:

$$
\mathcal T_{EF}(\eta'\leftarrow\eta);
$$

3. flat step clock time:

$$
\Delta\tau_{\mathrm{step}};
$$

4. strain coupling:

$$
g_n;
$$

5. stability widths:

$$
\gamma_n
\quad\text{or}\quad
\Gamma_n.
$$

All five must be fixed without \(G_N\).

Status:

`spectrum_required_objects`

### 63.2. Closure condition

The route is closed only if:

$$
\omega_{\ell,I}
=
\min_{n:g_n\neq0,\ \gamma_n\le\epsilon_\gamma}
\frac{|\arg\lambda_n|}
{\Delta\tau_{\mathrm{step}}}
$$

is determined by:

$$
\mathcal U_{EF},\quad
\mathcal T_{EF},\quad
\Delta\tau_{\mathrm{step}},\quad
g_n,
$$

with no free continuous spectral phase left.

If a continuous parameter remains:

$$
\theta,
\quad
\Delta\tau_{\mathrm{step}},
\quad
g_n,
$$

then the route is not closed.

Status:

`spectrum_closure_condition`

### 63.3. Predictive ladder

The acceptable ladder is:

$$
\mathcal I,\Gamma_I,K_\eta
\Rightarrow
\mathcal U_{EF}
\Rightarrow
\mathsf T_{EF}
\Rightarrow
\{\lambda_n,g_n,\gamma_n\}
\Rightarrow
\omega_{\ell,I}
\Rightarrow
\kappa_{\chi,I}
\Rightarrow
G_I.
$$

The forbidden ladder is:

$$
G_N
\Rightarrow
\omega_{\ell,G}
\Rightarrow
\theta
\text{ or }
\Delta\tau_{\mathrm{step}}
\Rightarrow
\mathsf T_{EF}.
$$

Status:

`predictive_ladder_declared`

### 63.4. Independent cross-checks

After \(\omega_{\ell,I}\) is derived, it must pass:

1. kappa-omega consistency:

$$
\mathcal R_{\kappa\omega}=0
\pm
\epsilon_{\kappa\omega};
$$

2. non-gravity bounds:

$$
\omega_{\ell,I}
\ge
\omega_{\ell,\min};
$$

3. gravity gate:

$$
\Xi_\ell
=
\frac{\omega_{\ell,I}^2}
{\omega_{\ell,G}^2}
=
1
\pm
\epsilon_G;
$$

4. dispersion residual gates using the derived coefficients.

Status:

`spectrum_cross_checks_declared`

### 63.5. Failure taxonomy

If the route fails, report one of:

1. `parametric_not_predictive`:
   free spectral phase or step time remains;
2. `wrong_pole_scale`:
   derived \(\omega_{\ell,I}\) misses \(\omega_{\ell,G}\);
3. `wrong_residual_coefficients`:
   dispersion/matter-wave coefficients fail;
4. `nonuniversal_clock_pole`:
   pole depends on clock species;
5. `vacuum_response_mismatch`:
   \(\mathcal R_{\kappa\omega}\neq0\).

No failure may be repaired by retuning after comparison.

Status:

`spectrum_failure_taxonomy`

### 63.6. Current status of the two-state model

The minimal two-state model has:

$$
\lambda_\pm=e^{\mp i\theta}.
$$

But it leaves:

$$
\theta,
\qquad
\Delta\tau_{\mathrm{step}}
$$

free unless a primitive cycle grammar fixes them.

Therefore its current status is:

`parametric_not_predictive`

It remains useful as a test scaffold only.

Status:

`two_state_status_classified`

### 63.7. What is closed

Closed:

1. formal criteria for update-spectrum closure;
2. forbidden ladder;
3. cross-checks;
4. failure taxonomy;
5. classification of the two-state model as not predictive yet.

Open:

1. primitive cycle grammar;
2. transition weights;
3. step time;
4. strain coupling;
5. numerical \(\omega_{\ell,I}\).

Next target:

derive a primitive cycle grammar or stop the update-spectrum route as underdetermined and move to a different route.

Primitive cycle grammar:

`sections/64-primitive-cycle-grammar.md`

Status:

`update_spectrum_closure_criteria_defined`
