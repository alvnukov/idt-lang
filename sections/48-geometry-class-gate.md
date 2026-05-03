## 48. Geometry Class Gate

This section constrains:

$$
D_S,\qquad z_{I,*},\qquad q_{V,*}.
$$

It does not choose them from \(G_N\).

It defines the geometric gates that must be passed before the weak-gravity calculator is executed.

Status:

`geometry_class_gate_initialized`

### 48.1. Three independent dimension readouts

The spatial dimension must be checked through independent readouts.

Volume growth:

$$
N_E(B_R)
\propto
R^{D_{\mathrm{vol}}}.
$$

Diffusion/spectral return:

$$
P(\sigma)
\propto
\sigma^{-D_{\mathrm{spec}}/2}.
$$

Radar-coordinate rank:

$$
D_{\mathrm{rad}}
=
\operatorname{rank}
\left[
\partial_a d_{\mathrm{rad}}(E,F)
\right].
$$

The dimension gate is:

$$
D_{\mathrm{vol}}
=
D_{\mathrm{spec}}
=
D_{\mathrm{rad}}
=
D_S
\pm
\epsilon_D.
$$

The observed weak-field target is:

$$
D_S=3.
$$

Status:

`spatial_dimension_cross_readout_gate`

### 48.2. Radar-orthogonal neighbour sector

Define a radar-orthogonal neighbour sector by \(D_S\) independent local axes:

$$
\pm e_1,\ldots,\pm e_{D_S}.
$$

Each coarse event has:

$$
z_{I,*}=2D_S.
$$

For:

$$
D_S=3,
$$

this gives:

$$
z_{I,*}=6.
$$

This value is fixed by neighbour structure, not by gravity.

Status:

`radar_orthogonal_degree_gate`

### 48.3. Cell-volume sector

If the reconstructed radar cell is an orthogonal cell with side:

$$
\ell_{0,*},
$$

then:

$$
\langle V\rangle
=
\ell_{0,*}^{D_S}.
$$

For \(D_S=3\):

$$
\langle V\rangle
=
\ell_{0,*}^3.
$$

Therefore:

$$
q_{V,*}
=
\frac{\ell_{0,*}^3}{\langle V\rangle}
=
1.
$$

If the reconstructed cell is not radar-orthogonal, then:

$$
q_{V,*}\neq1
$$

is a geometric residual, not a gravitational tuning knob.

Status:

`radar_orthogonal_cell_shape_gate`

### 48.4. Isotropy checks

Second-moment isotropy requires:

$$
Q_I^{ij}
=
\frac{1}{D_S}h^{ij}.
$$

For equal weights on \(\pm e_a\), this holds.

But second-moment isotropy is not enough for all propagation tests.

Define a fourth-moment residual:

$$
\mathcal R_4^{ijkl}
=
Q_I^{ijkl}
-
Q_{\mathrm{iso}}^{ijkl},
$$

where:

$$
Q_I^{ijkl}
=
\frac{1}{N_L}
\sum_{\langle EF\rangle}
\hat\ell_{EF}^i\hat\ell_{EF}^j
\hat\ell_{EF}^k\hat\ell_{EF}^l.
$$

The weak-field geometry gate requires:

$$
\|\mathcal R_Q\|,
\|\mathcal R_4\|
\le
\epsilon_{\mathrm{iso}}.
$$

If \(\mathcal R_4\) survives coarse-graining, it becomes a pre-declared anisotropic propagation residual.

Status:

`second_and_fourth_isotropy_gates`

### 48.5. Minimal radar-orthogonal sector

The minimal radar-orthogonal sector is:

$$
D_S=3,
\qquad
z_{I,*}=6,
\qquad
q_{V,*}=1.
$$

Together with the sampling invariant:

$$
\rho_{\chi,I}=1,
$$

the \(G_I\) calculator becomes:

$$
G_I^{(\mathrm{orth,min})}
=
\frac{c_I^3\ell_{0,*}^2}
{4\pi\hbar_I}.
$$

More generally, keeping \(\rho_{\chi,I}\):

$$
G_I^{(\mathrm{orth})}
=
\frac{\rho_{\chi,I}c_I^3\ell_{0,*}^2}
{4\pi\hbar_I}.
$$

Status:

`orthogonal_minimal_G_formula`

### 48.6. Dimensionless gate

For the radar-orthogonal sector:

$$
\Pi_G^{(\mathrm{orth})}
=
\frac{4\pi\hbar_I G_N}
{\rho_{\chi,I}c_I^3\ell_{0,*}^2}.
$$

Successful closure requires:

$$
\Pi_G^{(\mathrm{orth})}
=
1\pm\epsilon_G.
$$

Equivalently, if the gate succeeds:

$$
\ell_{0,*}^2
=
\frac{4\pi}{\rho_{\chi,I}}
\frac{\hbar_I G_N}{c_I^3}.
$$

This last equation must not be used to define \(\ell_{0,*}\).

It is only the experimental success condition after \(\ell_{0,*}\) has been independently derived.

Status:

`orthogonal_dimensionless_G_gate`

### 48.7. Experimental meaning

If the sector fails \(G_N\), possible pre-declared failures are:

1. the physical geometry is not radar-orthogonal;
2. \(D_S\neq3\) at the relevant scale;
3. \(q_{V,*}\neq1\);
4. \(\rho_{\chi,I}\neq1\);
5. \(\ell_{0,*}\) is not the fundamental clock-order link scale;
6. the Newtonian source law is an effective large-scale limit only.

No failure is repaired by changing:

$$
D_S,z_{I,*},q_{V,*},\rho_{\chi,I},\ell_{0,*}
$$

after comparison with \(G_N\).

Status:

`geometry_failure_modes_predeclared`

### 48.8. What is closed

Closed conditionally:

$$
D_S=3,\quad z_{I,*}=6,\quad q_{V,*}=1
$$

for the radar-orthogonal sector.

Closed as a calculator:

$$
G_I^{(\mathrm{orth})}
=
\frac{\rho_{\chi,I}c_I^3\ell_{0,*}^2}
{4\pi\hbar_I}.
$$

Open:

1. proof that inherited geometry selects the radar-orthogonal sector;
2. proof that \(\mathcal R_4\to0\) under coarse-graining;
3. independent numerical \(\ell_{0,*}\);
4. experimental \(G_N\) comparison;
5. PPN spatial-curvature gates after the Newtonian gate.

Next target:

derive \(\ell_{0,*}\) or a dimensionless relation fixing it without \(G_N\).

Link scale closure gate:

`sections/49-link-scale-closure-gate.md`

Status:

`geometry_class_conditionally_reduced`
