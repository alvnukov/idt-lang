## 16. Vacuum Impedance Bridge

This section chooses the next coupling-selection route:

$$
\mathcal P_I
\Rightarrow
\epsilon_{0,I},\mu_{0,I}
\Rightarrow
Z_{0,I}
\Rightarrow
\alpha_{\mathrm{em},I}.
$$

It does not yet derive the numerical vacuum response.

It turns the target into a sharper dimensionless impedance gate.

Status:

`vacuum_impedance_bridge_initialized`

### 16.1. Vacuum response coefficients

In a weak flat readout domain, decompose:

$$
F_I
\Rightarrow
(\mathbf E_I,\mathbf B_I).
$$

Let inherited vacuum response define:

$$
\epsilon_{0,I},
\qquad
\mu_{0,I}.
$$

The field energy readout is:

$$
u_{A,I}
=
\frac12
\left(
\epsilon_{0,I}|\mathbf E_I|^2
+
\frac{1}{\mu_{0,I}}|\mathbf B_I|^2
\right).
$$

These are not allowed to be independent fitted constants once \(c_I\) and \(\alpha_{\mathrm{em},I}\) are targeted.

Status:

`vacuum_response_coefficients_defined`

### 16.2. Speed and impedance

The electromagnetic propagation speed from field response is:

$$
c_{\mathrm{em},I}
=
\frac{1}{\sqrt{\epsilon_{0,I}\mu_{0,I}}}.
$$

Clock/causal readout already has:

$$
c_I.
$$

Known gate:

$$
c_{\mathrm{em},I}
\to
c_I.
$$

This fixes only the product:

$$
\epsilon_{0,I}\mu_{0,I}
=
\frac{1}{c_I^2}.
$$

It does not fix the impedance:

$$
Z_{0,I}
=
\sqrt{\frac{\mu_{0,I}}{\epsilon_{0,I}}}
=
\frac{1}{\epsilon_{0,I}c_I}.
$$

Therefore:

$$
c_I
\nRightarrow
\alpha_{\mathrm{em},I}.
$$

The missing electromagnetic scale is the vacuum impedance \(Z_{0,I}\).

Status:

`c_fixes_product_not_impedance`

### 16.3. Fine-structure constant as impedance ratio

The fine-structure constant is:

$$
\alpha_{\mathrm{em},I}
=
\frac{e_I^2}{4\pi\epsilon_{0,I}\hbar_I c_I}.
$$

Using:

$$
h_I=2\pi\hbar_I
$$

and:

$$
R_{K,I}
=
\frac{h_I}{e_I^2},
$$

we get:

$$
\alpha_{\mathrm{em},I}
=
\frac{Z_{0,I}}{2R_{K,I}}.
$$

This is a strong bridge relation:

$$
\text{vacuum impedance}
+
\text{quantum Hall resistance}
\Rightarrow
\alpha_{\mathrm{em}}.
$$

It is dimensionless and experimentally checkable.

Status:

`alpha_as_vacuum_impedance_over_quantum_hall_resistance`

### 16.4. Why this is not yet a prediction

The relation:

$$
\alpha_{\mathrm{em},I}
=
\frac{Z_{0,I}}{2R_{K,I}}
$$

is exact as a bridge identity once the sectors are defined.

But it is predictive only if:

1. \(R_{K,I}\) is fixed by the action/charge phase bridge;
2. \(Z_{0,I}\) is derived from inherited vacuum response;
3. no separate \(\alpha_{\mathrm{em}}\) fit is used.

If \(Z_{0,I}\) is inserted from measured electromagnetism, this is only a consistency relation.

Status:

`impedance_relation_not_yet_numeric_prediction`

### 16.5. Primitive vacuum response target

Let:

$$
\mathcal P_{E,I}
$$

be inherited electric polarizability response, and:

$$
\mathcal P_{B,I}
$$

be inherited magnetic stiffness response.

Target:

$$
\mathcal P_{E,I}
\Rightarrow
\epsilon_{0,I},
$$

and:

$$
\mathcal P_{B,I}
\Rightarrow
\mu_{0,I}^{-1}.
$$

Then:

$$
Z_{0,I}
=
\sqrt{\frac{\mu_{0,I}}{\epsilon_{0,I}}}.
$$

The hard primitive problem becomes:

$$
\frac{\mathcal P_{B,I}}{\mathcal P_{E,I}}
\Rightarrow
Z_{0,I}
\Rightarrow
\alpha_{\mathrm{em},I}.
$$

Status:

`primitive_vacuum_response_target`

### 16.6. Closure gates

A valid vacuum-response route must pass all of:

| Gate | Required |
|---|---|
| light speed | \(c_{\mathrm{em},I}=1/\sqrt{\epsilon_{0,I}\mu_{0,I}}\to c_I\) |
| impedance | \(Z_{0,I}=\sqrt{\mu_{0,I}/\epsilon_{0,I}}\) is one value |
| quantum Hall | \(R_{K,I}=h_I/e_I^2\) |
| fine structure | \(\alpha_{\mathrm{em},I}=Z_{0,I}/(2R_{K,I})\) |
| AB / flux | \(\Phi_{0,I}=h_I/|q_I|\) |
| scattering | Coulomb / Mott routes use same \(\alpha_{\mathrm{em},I}\) |
| spectroscopy | atomic spectra use same \(\alpha_{\mathrm{em},I}\) after running corrections |

No route may reset \(e_I\), \(\hbar_I\), \(Z_{0,I}\), or \(g_I\) independently.

Status:

`vacuum_impedance_no_refit_closure`

### 16.7. Allowed residuals

Vacuum-response residuals:

$$
Z_{0,I}(E)
=
Z_{0,I}(E_0)
+
\mathcal R_Z(E,E_0).
$$

Anisotropic response:

$$
\epsilon_{0,I}^{ij}
\neq
\epsilon_{0,I}\delta^{ij}.
$$

Magnetoelectric residual:

$$
\mathcal R_{EB}
\sim
\mathbf E_I\cdot\mathbf B_I.
$$

Each must be tied to gates:

1. precision optics;
2. polarization / birefringence;
3. scattering;
4. spectroscopy;
5. quantum electrical standards.

Status:

`vacuum_response_residuals_declared`

### 16.8. What v5.17 closes

This section turns the fine-structure target into a sharper bridge:

$$
\alpha_{\mathrm{em},I}
=
\frac{Z_{0,I}}{2R_{K,I}}.
$$

It shows that:

$$
c_I
\text{ fixes }
\epsilon_{0,I}\mu_{0,I},
$$

but not:

$$
Z_{0,I}.
$$

Therefore the next hard target is:

$$
\mathcal P_{E,I},\mathcal P_{B,I}
\Rightarrow
Z_{0,I}
\Rightarrow
\alpha_{\mathrm{em},I}.
$$

It does not yet derive the numerical value.

Status:

`fine_structure_reduced_to_vacuum_impedance_derivation`

Computational compression front:

`sections/17-computational-compression-front.md`
