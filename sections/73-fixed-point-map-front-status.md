## 73. Fixed-Point Map Front Status

This section summarizes the current status of:

$$
F_G.
$$

Status:

`fixed_point_map_front_status_initialized`

### 73.1. Current full map form

The current fixed-point map has the form:

$$
F_G(\Theta)
=
\arg
\left[
\sum_w
p(w)
e^{-\Lambda_w}
\exp
\left(
i[b_w\Theta+S_I(w)/\hbar_I]
\right)
\right].
$$

where:

1. \(p(w)\) comes from the Perron-Frobenius grammar measure;
2. \(e^{-\Lambda_w}\) is recoverable coherence magnitude;
3. \(b_w\) is the integer phase-count coefficient of the word;
4. \(S_I(w)/\hbar_I\) is the gauge-invariant action cocycle phase.

Status:

`full_FG_form_assembled`

### 73.2. Fixed-point closure

The rotation route requires:

$$
\Theta_*
=
F_G(\Theta_*),
$$

with:

$$
|F_G'(\Theta_*)|<1.
$$

Step compatibility requires:

$$
\Theta_*=\zeta_{\mathrm{step}}
\pm
\epsilon_\Theta.
$$

Then:

$$
\omega_{\ell,I}
=
\frac{|\Theta_*|}
{\Delta\tau_{\mathrm{step}}}.
$$

Status:

`FG_fixed_point_closure_restated`

### 73.3. What is actually closed

Closed:

1. allowed kernel-normalization map class;
2. non-fit route for word weights \(p(w)\);
3. phase cocycle form;
4. action cocycle bridge;
5. coherence magnitude bridge;
6. fixed-point and step-compatibility tests.

Status:

`FG_structure_closed`

### 73.4. What is not closed

Still open:

1. actual primitive grammar graph \(A\);
2. primitive transition actions \(\mathfrak s_{ij}\);
3. recoverable coherence losses \(\Lambda_w\);
4. step readout invariant \(\zeta_{\mathrm{step}}\);
5. stable fixed point \(\Theta_*\);
6. numerical \(\omega_{\ell,I}\);
7. final \(G_I\).

Therefore the route is not yet predictive.

Current status:

`form_closed_values_underived`

Status:

`FG_values_not_closed`

### 73.5. No-fit summary

Forbidden:

1. choose grammar graph \(A\) from \(G_N\);
2. choose action cocycle \(S_I(w)\) from \(\omega_{\ell,G}\);
3. choose coherence losses \(\Lambda_w\) from gravity comparison;
4. choose \(\zeta_{\mathrm{step}}\) to match \(\Theta_*\);
5. call the form of \(F_G\) a numerical derivation.

Allowed:

1. compute \(F_G\) after all components are fixed from primitives;
2. reject the route if components remain free;
3. compare derived \(\omega_{\ell,I}\) with non-gravity and gravity gates.

Status:

`FG_no_fit_summary`

### 73.6. Decision gate

The update-spectrum route may continue only if the next work derives at least one of:

$$
A,
\qquad
\mathfrak s_{ij},
\qquad
\Lambda_w,
\qquad
\zeta_{\mathrm{step}}
$$

from primitive inheritance.

If the next work only introduces another free parameter, the route must be marked:

`update_spectrum_underived`

and paused.

Status:

`FG_route_decision_gate`

### 73.7. What is closed

Closed:

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

Open:

the primitive data needed to evaluate it.

Next target:

derive one primitive component of this map, preferably transition actions \(\mathfrak s_{ij}\), because they also connect to the existing \(\hbar_I\) problem.

Transition action gate:

`sections/74-transition-action-gate.md`

Fixed-point route decision:

`sections/75-fixed-point-route-decision.md`

Status:

`FG_front_reduced_to_primitive_components`
