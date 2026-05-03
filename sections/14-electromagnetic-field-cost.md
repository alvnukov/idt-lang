## 14. Electromagnetic Field-Cost Bridge

The Aharonov-Bohm phase fixes connection holonomy.

It does not by itself fix the normalization of the electromagnetic field.

That normalization is required before \(\alpha_{\mathrm{em}}\) can become predictive.

Status:

`electromagnetic_field_cost_bridge_initialized`

### 14.1. The AB scale degeneracy

The charged phase uses:

$$
\Delta\phi_{q,I}
=
\frac{q_I}{\hbar_I}
\oint A_{I,\mu}dx^\mu.
$$

This is invariant under the readout rescaling:

$$
A_I\mapsto \lambda A_I,
\qquad
q_I\mapsto q_I/\lambda.
$$

Therefore AB phase alone fixes:

$$
q_I A_I
$$

or operationally:

$$
\frac{q_I\Phi_{B,I}}{\hbar_I},
$$

but not the separate field normalization.

This is why:

$$
\text{AB phase}
\nRightarrow
\alpha_{\mathrm{em}}
$$

without a field-cost bridge.

Status:

`ab_phase_has_field_scale_degeneracy`

### 14.2. Source current from charged histories

Let charged inherited activity define a conserved current:

$$
j_I^\mu.
$$

The minimal source coupling is:

$$
S_{\mathrm{int},I}
=
\int j_I^\mu A_{I,\mu}\,d\nu.
$$

Under:

$$
A_{I,\mu}
\mapsto
A_{I,\mu}-\partial_\mu\Lambda,
$$

the source term changes by:

$$
\delta S_{\mathrm{int},I}
=
-
\int j_I^\mu\partial_\mu\Lambda\,d\nu.
$$

After integration by parts:

$$
\delta S_{\mathrm{int},I}
=
\int \Lambda\,\partial_\mu j_I^\mu\,d\nu
\quad+
\text{boundary}.
$$

Gauge covariance for arbitrary local \(\Lambda\) requires:

$$
\partial_\mu j_I^\mu=0.
$$

Thus charge conservation is not an extra empirical patch.

It follows as the compatibility condition of local phase relabeling.

Known gate:

electric charge is conserved in all confirmed electromagnetic processes.

Status:

`charge_conservation_from_gauge_covariance`

### 14.3. Field-cost support conditions

The weak-field electromagnetic cost must satisfy:

1. locality;
2. gauge invariance;
3. quadratic leading response;
4. isotropy in the reconstructed flat readout domain;
5. no photon mass term at leading long range;
6. bounded positive field energy;
7. source additivity;
8. no leading parity-odd term unless a residual is declared.

The field strength is:

$$
F_{I,\mu\nu}
=
\partial_\mu A_{I,\nu}
-
\partial_\nu A_{I,\mu}.
$$

Gauge invariance excludes a leading local term:

$$
A_{I,\mu}A_I^\mu.
$$

The lowest-derivative even scalar is:

$$
F_{I,\mu\nu}F_I^{\mu\nu}.
$$

Therefore the leading weak-field cost is:

$$
\mathcal F_A[A]
=
\frac{1}{4g_I^2}
\int F_{I,\mu\nu}F_I^{\mu\nu}\,d\nu
+
\int j_I^\mu A_{I,\mu}\,d\nu
$$

up to boundary terms, topological terms, and higher-order residuals.

Status:

`maxwell_cost_from_gauge_locality_quadratic_response`

### 14.4. Maxwell readout equation

Varying \(A_{I,\mu}\) gives:

$$
\partial_\mu
\left(
\frac{1}{g_I^2}
F_I^{\mu\nu}
\right)
=
j_I^\nu.
$$

If \(g_I\) is constant in the tested domain:

$$
\partial_\mu F_I^{\mu\nu}
=
g_I^2 j_I^\nu.
$$

This is the Maxwell source equation in bridge normalization.

The homogeneous equation:

$$
\partial_{[\lambda}F_{I,\mu\nu]}=0
$$

follows from:

$$
F_I=dA_I.
$$

Known gates:

1. electromagnetic waves have two transverse long-range modes;
2. no observed photon mass in the tested domain;
3. source conservation is required.

Status:

`maxwell_equations_as_field_cost_readout`

### 14.5. Coulomb / scattering gate

In the static flat readout domain:

$$
A_{I,0}=V_I,
\qquad
A_{I,i}=0.
$$

The field equation reduces to:

$$
\nabla^2 V_I
=
-
g_I^2\rho_I.
$$

For a point source:

$$
V_I(r)
=
\frac{g_I^2 q_I}{4\pi r}.
$$

For two elementary charges in natural bridge units:

$$
U_I(r)
=
\frac{g_I^2}{4\pi r}.
$$

Therefore:

$$
\alpha_{\mathrm{em},I}
=
\frac{g_I^2}{4\pi}
$$

in the canonical weak-field normalization:

$$
\hbar_I=c_I=1.
$$

Known gates:

1. Coulomb law;
2. Rutherford / Mott scattering in the appropriate limit;
3. atomic spectral dependence on \(\alpha_{\mathrm{em}}\).

Status:

`alpha_as_canonical_field_coupling`

### 14.6. No-refit electromagnetic closure

One route may calibrate \(g_I\).

After that, the same \(g_I\) must pass independent gates.

Closure set:

$$
\mathcal C_{\mathrm{em}}
=
\left\{
\alpha_{\mathrm{em},I}^{\mathrm{Coulomb}},
\alpha_{\mathrm{em},I}^{\mathrm{scattering}},
\alpha_{\mathrm{em},I}^{\mathrm{spectroscopy}},
\alpha_{\mathrm{em},I}^{\mathrm{Josephson/Hall}}
\right\}.
$$

Predictive closure requires:

$$
\frac{
\alpha_{\mathrm{em},I}^{(r)}
}{
\alpha_{\mathrm{em},I}^{(s)}
}
\to
1
$$

for all independent routes \(r,s\), within domain uncertainty.

Forbidden move:

change \(g_I\), \(e_I\), or \(\hbar_I\) separately for each route.

Status:

`electromagnetic_no_refit_closure_gate`

### 14.7. Relation to Josephson and Hall gates

The AB / phase sector gives:

$$
\Phi_0
=
\frac{h}{|q|}.
$$

For Cooper-pair charge \(2e\):

$$
\Phi_0^{(2e)}
=
\frac{h}{2e}.
$$

Quantum electrical standards give:

$$
K_J
=
\frac{2e}{h},
$$

and:

$$
R_K
=
\frac{h}{e^2}.
$$

These test the same \(e/h\) and \(h/e^2\) bridge ratios that appear in AB and charge transport.

They do not alone derive \(\alpha_{\mathrm{em}}\), because \(\alpha_{\mathrm{em}}\) also uses the field propagation normalization through \(c\) and vacuum response.

But they strongly constrain any mismatch between phase-charge and transport-charge readouts.

Status:

`quantum_electrical_closure_linked_to_phase_charge_bridge`

### 14.8. Allowed electromagnetic residuals

Residuals must be declared before comparison with data.

Photon-mass residual:

$$
\mathcal R_m
=
\frac{m_{A,I}^2}{2}
A_{I,\mu}A_I^\mu.
$$

Higher-field residual:

$$
\mathcal R_{F^4}
=
\frac{1}{\Lambda_{F,I}^4}
\left(F_{I,\mu\nu}F_I^{\mu\nu}\right)^2.
$$

Parity-odd residual:

$$
\mathcal R_\theta
=
\theta_I
F_I\wedge F_I.
$$

Running-coupling residual:

$$
\alpha_{\mathrm{em},I}(E)
=
\alpha_{\mathrm{em},I}(E_0)
+
\mathcal R_{\mathrm{run}}(E,E_0).
$$

Each residual requires independent gates:

| Residual | Required gates |
|---|---|
| \(m_{A,I}\) | long-range Coulomb, magnetic fields, photon propagation |
| \(F^4\) | high-intensity optics, scattering, vacuum birefringence |
| \(\theta_I\) | parity / CP-sensitive electromagnetic channels |
| \(\mathcal R_{\mathrm{run}}\) | spectroscopy at different scales, scattering, precision QED |

Status:

`electromagnetic_residual_channels_declared`

### 14.9. What v5.15 closes

This section closes the next logical bridge:

$$
A_I
\Rightarrow
F_I=dA_I
\Rightarrow
\mathcal F_A[A]
\Rightarrow
\text{Maxwell weak-field readout}.
$$

It also explains why:

$$
\text{AB phase}
\neq
\text{full derivation of }\alpha_{\mathrm{em}}.
$$

It reduces the \(\alpha_{\mathrm{em}}\) problem to:

$$
g_I
\Rightarrow
\alpha_{\mathrm{em},I}
=
\frac{g_I^2}{4\pi}
$$

in canonical natural bridge units.

It does not yet derive:

1. numerical \(g_I\);
2. numerical \(\alpha_{\mathrm{em}}\);
3. charge topology;
4. QED loop running;
5. electroweak embedding.

Next target:

$$
\text{primitive fixed point / stability condition}
\Rightarrow
g_I
\Rightarrow
\alpha_{\mathrm{em},I}
$$

or, if that fails, a declared residual:

$$
\delta\alpha_{\mathrm{em},I}.
$$

Status:

`electromagnetic_field_cost_gap_reduced`

Coupling-selection no-go and routes:

`sections/15-coupling-selection-front.md`
