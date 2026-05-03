## 15. Coupling Selection Front

This section states the coupling problem sharply.

Gauge covariance and Maxwell field-cost determine the form of the electromagnetic sector.

They do not determine the numerical value of the dimensionless coupling.

Status:

`coupling_selection_front_initialized`

### 15.1. The remaining electromagnetic constant

After v5.15, the weak electromagnetic sector has:

$$
\mathcal F_A[A]
=
\frac{1}{4g_I^2}
\int F_{I,\mu\nu}F_I^{\mu\nu}\,d\nu
+
\int j_I^\mu A_{I,\mu}\,d\nu.
$$

The physical dimensionless target is:

$$
\alpha_{\mathrm{em},I}
=
\frac{g_I^2}{4\pi}
$$

in canonical natural bridge units.

Thus the remaining problem is:

$$
\text{why this }g_I?
$$

not:

$$
\text{why this }e,\hbar,c
$$

separately.

Status:

`alpha_reduced_to_dimensionless_coupling_selection`

### 15.2. No-go from symmetry alone

Claim:

local \(U(1)\) covariance, locality, quadratic weak-field response, and long-range masslessness do not fix \(g_I\).

Reason:

For every positive:

$$
g_I>0
$$

the functional:

$$
\mathcal F_A^{(g)}[A]
=
\frac{1}{4g_I^2}
\int F_I^2\,d\nu
+
\int j_I\cdot A_I\,d\nu
$$

has the same:

1. gauge covariance;
2. field equation form;
3. AB holonomy structure;
4. long-range massless propagation;
5. charge conservation condition.

Changing \(g_I\) changes strengths, not the symmetry class.

Therefore:

$$
\text{symmetry + locality}
\nRightarrow
\alpha_{\mathrm{em}}.
$$

Any numerical derivation of \(\alpha_{\mathrm{em}}\) must use an additional primitive condition.

Status:

`no_alpha_from_gauge_symmetry_alone`

### 15.3. Allowed coupling-selection routes

Only three routes are currently admissible.

Route A: primitive fixed point.

$$
\beta_I(g_\star)=0
\quad\Rightarrow\quad
\alpha_{\mathrm{em},I}
=
\frac{g_\star^2}{4\pi}.
$$

Route B: inherited vacuum response.

$$
\rho_{\mathrm{vac},I},
\chi_{\mathrm{vac},I}
\Rightarrow
\epsilon_{0,I},\mu_{0,I}
\Rightarrow
\alpha_{\mathrm{em},I}.
$$

Route C: embedding / topology.

$$
\mathcal G_I
\Rightarrow
U(1)
\Rightarrow
g_I
$$

where \(\mathcal G_I\) is a larger primitive connection structure.

Topology may quantize charge ratios:

$$
q_I=n e_I,
$$

but topology alone does not normally fix the coupling magnitude.

Status:

`admissible_coupling_selection_routes`

### 15.4. Running coupling gate

If \(g_I\) changes with scale, the theory must not hide that as a new fit.

Define:

$$
\mu\frac{dg_I}{d\mu}
=
\beta_I(g_I,\mathcal M_I),
$$

where \(\mathcal M_I\) is the active matter/readout content.

Equivalently:

$$
\mu\frac{d\alpha_{\mathrm{em},I}}{d\mu}
=
B_I(\alpha_{\mathrm{em},I},\mathcal M_I).
$$

Known QED perturbative gate in a domain with active charged fermions:

$$
\mu\frac{d\alpha}{d\mu}
=
\frac{2}{3\pi}
\left(\sum_f Q_f^2\right)
\alpha^2
+
O(\alpha^3).
$$

The protolanguage may reproduce this as a coarse-graining flow.

It must not replace it with an arbitrary scale-by-scale \(\alpha(E)\).

Status:

`running_alpha_as_coarse_graining_gate`

### 15.5. Predictive test after one coupling calibration

Allowed calibration:

$$
\alpha_{\mathrm{em},I}(E_0)
\leftarrow
\text{one precision route}.
$$

Then predict:

$$
\alpha_{\mathrm{em},I}(E)
$$

through:

$$
B_I(\alpha,\mathcal M_I).
$$

No-refit gate:

$$
\alpha_{\mathrm{em},I}^{\mathrm{spectroscopy}}(E_1)
\to
\alpha_{\mathrm{em},I}^{\mathrm{scattering}}(E_2)
\to
\alpha_{\mathrm{em},I}^{\mathrm{electrical}}(E_3)
$$

with one initial calibration and one derived flow.

If the flow is not derived, then the result is only a consistency test, not a prediction.

Status:

`single_calibration_running_alpha_gate`

### 15.6. Coupling fixed point as a hard target

To predict \(\alpha_{\mathrm{em}}\), the theory needs:

$$
\mathcal B_I[g]
=
0
$$

with an isolated stable solution:

$$
g_I=g_\star.
$$

Then:

$$
\alpha_{\mathrm{em},I}
=
\frac{g_\star^2}{4\pi}
$$

would be a genuine non-fitted prediction.

Acceptance conditions:

1. \(g_\star\) must be dimensionless;
2. \(g_\star\) must not be chosen after looking at \(\alpha_{\mathrm{obs}}\);
3. the same \(g_\star\) must pass at least two independent electromagnetic gates;
4. running from \(g_\star\) to low-energy readout must be derived or explicitly bounded.

Status:

`coupling_fixed_point_hard_target`

### 15.7. Vacuum-response route

Another admissible path is to derive the field-cost coefficient from inherited vacuum response.

Let:

$$
\mathcal P_I
$$

be primitive polarizability of the inherited vacuum readout.

Then:

$$
\mathcal P_I
\Rightarrow
\epsilon_{0,I}
$$

and:

$$
c_I^2
=
\frac{1}{\epsilon_{0,I}\mu_{0,I}}.
$$

If \(c_I\) is already fixed by clock/causal readout, then:

$$
\epsilon_{0,I}
\quad\text{and}\quad
\mu_{0,I}
$$

cannot be fitted independently.

The fine-structure gate becomes:

$$
\alpha_{\mathrm{em},I}
=
\frac{e_I^2}{4\pi\epsilon_{0,I}\hbar_I c_I}.
$$

This route is promising only if \(\mathcal P_I\) is derived from primitive inheritance, not inserted as measured permittivity.

Status:

`vacuum_response_route_to_alpha`

### 15.8. What v5.16 closes

This section closes a methodological loophole:

$$
\text{Maxwell form}
\neq
\text{numerical }\alpha_{\mathrm{em}}.
$$

It proves only the no-go:

$$
U(1)
+
\text{locality}
+
\text{quadratic field cost}
\nRightarrow
g_I.
$$

It selects the next admissible hard targets:

$$
\beta_I(g_\star)=0
$$

or:

$$
\mathcal P_I
\Rightarrow
\epsilon_{0,I}
\Rightarrow
\alpha_{\mathrm{em},I}.
$$

Status:

`alpha_prediction_requires_new_primitive_condition`

Selected vacuum-response route:

`sections/16-vacuum-impedance-bridge.md`
