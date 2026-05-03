## 26. Vacuum Stiffness Bridge

This section localizes where the Newtonian constant enters the clock-rate route.

After section 25, the remaining gravitational calibration is the vacuum resistance to clock-rate strain:

$$
\alpha_I.
$$

Status:

`vacuum_stiffness_bridge_initialized`

### 26.1. The gap

The weak source equation currently reads:

$$
\Delta_S\Phi_I
=
\frac{c_I^2}{\alpha_I}\sigma_{\Phi,I}^G.
$$

The validated Newtonian gate is:

$$
\Delta\Phi
=
4\pi G_N\rho_m.
$$

Therefore \(G_N\) is not hidden in \(m_I\) after section 25.

It sits in the ratio between:

1. source response density \(\sigma_{\Phi,I}^G\);
2. vacuum stiffness \(\alpha_I\).

Status:

`G_localized_in_vacuum_stiffness_ratio`

### 26.2. Edge stiffness from primitive clock links

For neighbouring readout cells \(E,F\), define:

$$
s_{EF}
=
\varphi(F)-\varphi(E).
$$

The local vacuum cost has expansion:

$$
C_{EF}(s_{EF})
=
C_{EF}(0)
+
\frac12a_{EF}s_{EF}^2
+
O(s_{EF}^4),
$$

with:

$$
a_{EF}
=
\left.
\frac{\partial^2 C_{EF}}{\partial s_{EF}^2}
\right|_{s=0}
>
0.
$$

Thus \(a_{EF}\) is a primitive clock-link stiffness.

It is not fitted to planetary motion.

Status:

`edge_stiffness_defined`

### 26.3. Coarse-grained stiffness tensor

Let \(\ell_{EF}^i\) be the reconstructed spatial displacement of the neighbour link.

For a coarse region \(U\), define:

$$
A_I^{ij}(U)
=
\frac{1}{\nu_{G,S}(U)}
\sum_{\langle EF\rangle\subset U}
a_{EF}\ell_{EF}^i\ell_{EF}^j.
$$

The continuum clock-strain cost is:

$$
\frac12
\int_U
A_I^{ij}\partial_i\varphi\partial_j\varphi
d\nu_{G,S}.
$$

The isotropic weak-field fixed point is:

$$
A_I^{ij}
\to
\alpha_I h^{ij}.
$$

Equivalently:

$$
\alpha_I
=
\frac{1}{D_S}
h_{ij}A_I^{ij}
$$

in the isotropic domain.

Status:

`alpha_as_coarse_grained_clock_stiffness`

### 26.4. Newtonian stiffness target

If the source calibration reaches:

$$
\sigma_{\Phi,I}^G
\to
\rho_m c_I^2,
$$

then the source equation becomes:

$$
\Delta_S\Phi_I
=
\frac{c_I^4}{\alpha_I}\rho_m.
$$

Matching the validated Newtonian gate:

$$
\Delta\Phi
=
4\pi G_N\rho_m
$$

requires:

$$
\alpha_I
\to
\frac{c_I^4}{4\pi G_N}.
$$

This is the stiffness target.

It does not derive \(G_N\) yet.

It states exactly what the primitive clock network must compute.

Status:

`newtonian_stiffness_target`

### 26.5. Predictive computation route

The theory becomes predictive for \(G_N\) only if the following chain closes:

$$
(\bar E,\le_I,\Gamma_I,\tau_I)
\Rightarrow
a_{EF}
\Rightarrow
A_I^{ij}
\Rightarrow
\alpha_I
\Rightarrow
G_I
=
\frac{c_I^4}{4\pi\alpha_I}.
$$

No \(G_N\) input is allowed in this chain.

The output must then be compared with:

$$
G_I
\stackrel{gate}{\longrightarrow}
G_N.
$$

Status:

`G_prediction_chain_defined`

### 26.6. Residuals

Anisotropic stiffness residual:

$$
\mathcal R_A^{ij}
=
A_I^{ij}
-
\alpha_I h^{ij}.
$$

Scale-dependent stiffness residual:

$$
\mathcal R_{\alpha}(L)
=
\frac{\alpha_I(L)-\alpha_I(L_0)}{\alpha_I(L_0)}.
$$

If nonzero, it creates an effective gravitational residual:

$$
\frac{\Delta G_I(L)}{G_I}
\approx
-
\mathcal R_{\alpha}(L)
$$

when \(c_I\) and source calibration are fixed.

Such residuals may be relevant to dark-sector phenomenology only if they survive solar-system,
laboratory, lensing, and cosmological gates without refitting.

Status:

`stiffness_residuals_explicit`

### 26.7. No-refit experimental gates

The same \(\alpha_I\) must pass:

1. laboratory inverse-square/Newtonian source tests;
2. free-fall and Eotvos tests through the same \(\Phi_I\);
3. orbital dynamics in the weak-field domain;
4. light bending and Shapiro gates after \(\gamma_I^{\mathrm{PPN}}\to1\);
5. cosmological residual gates only after local tests remain satisfied.

If local and astronomical gates require different \(\alpha_I\) without an explicit residual equation,
the bridge fails.

Status:

`single_alpha_no_refit_gate`

### 26.8. What is closed

This section closes:

$$
\alpha_I
\quad
\text{as an unnamed free coefficient.}
$$

It replaces it with:

$$
\alpha_I
=
\frac{1}{D_S}
h_{ij}
\left[
\frac{1}{\nu_{G,S}(U)}
\sum_{\langle EF\rangle\subset U}
a_{EF}\ell_{EF}^i\ell_{EF}^j
\right].
$$

It does not yet derive:

1. the microscopic law for \(a_{EF}\);
2. the event-density calibration \(\lambda_I\);
3. the matter calibration \(\sigma_{\Phi,I}^G\to\rho_m c_I^2\);
4. the numerical value of \(G_N\);
5. dark-sector residual equations.

Next target:

derive \(a_{EF}\) from stability of distinguishability inheritance and clock-network update rules.

Link stiffness closure:

`sections/29-link-stiffness-closure.md`

Status:

`vacuum_stiffness_gap_reduced`
