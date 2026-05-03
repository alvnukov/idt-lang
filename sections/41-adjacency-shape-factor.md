## 41. Adjacency Shape Factor

This section targets:

$$
z_I,\qquad q_{V,I}.
$$

These are order/count spatial adjacency invariants.

They must not be chosen to fit \(G_N\).

Status:

`adjacency_shape_factor_initialized`

### 41.1. Neighbour relation

On a spatial slice \(S\), define admissible neighbour links:

$$
E\sim_S F
$$

if:

1. \(E,F\in S\);
2. no intermediate coarse event lies between them in the spatial adjacency graph;
3. the clock-radar distance satisfies:

$$
d_{\mathrm{radar}}(E,F)
=
\ell_0 w_S(E,F)
[1+O(\epsilon_\ell)].
$$

The neighbour relation must be fixed before any gravitational comparison.

Status:

`spatial_neighbour_relation_defined`

### 41.2. Mean degree

For a region \(U\subset S\):

$$
z_I(U)
=
\frac{2N_L(U)}{N_E(U)}.
$$

Flat-domain readiness requires:

$$
z_I(U)
\to
z_{I,0}
$$

under coarse-graining.

Degree residual:

$$
\mathcal R_z(U)
=
\frac{z_I(U)-z_{I,0}}{z_{I,0}}.
$$

Status:

`mean_degree_as_adjacency_invariant`

### 41.3. Cell volume and shape factor

Let each coarse cell \(E\) have reconstructed spatial Voronoi/readout volume:

$$
V_E.
$$

Define average cell volume:

$$
\langle V\rangle_U
=
\frac{1}{N_E(U)}
\sum_{E\in U}V_E.
$$

Since:

$$
\lambda_I^{(3)}(U)
=
\frac{N_E(U)}{\nu_{G,S}(U)}
=
\frac{1}{\langle V\rangle_U},
$$

the shape factor is:

$$
q_{V,I}(U)
=
\lambda_I^{(3)}(U)\ell_0^3
=
\frac{\ell_0^3}{\langle V\rangle_U}.
$$

Status:

`shape_factor_from_cell_volume`

### 41.4. Isotropic regular sector

For an isotropic regular spatial sector:

$$
z_I(U)\to z_{I,0},
\qquad
q_{V,I}(U)\to q_{V,0}.
$$

Then:

$$
n_L\ell_0^2
=
\frac{z_{I,0}q_{V,0}}{2\ell_0}.
$$

The pair:

$$
(z_{I,0},q_{V,0})
$$

is a geometry class invariant, not a gravitational fit.

Status:

`regular_sector_geometry_invariants`

### 41.5. Anisotropy residual

If neighbour directions are not isotropically distributed, define:

$$
Q_I^{ij}(U)
=
\frac{1}{N_L(U)}
\sum_{\langle EF\rangle\subset U}
\hat\ell_{EF}^i\hat\ell_{EF}^j.
$$

Isotropy target:

$$
Q_I^{ij}
\to
\frac{1}{D_S}h^{ij}.
$$

Residual:

$$
\mathcal R_Q^{ij}
=
Q_I^{ij}
-
\frac{1}{D_S}h^{ij}.
$$

This feeds the stiffness anisotropy:

$$
\mathcal R_A^{ij}.
$$

Status:

`adjacency_anisotropy_residual`

### 41.6. No-fit rule

Forbidden:

1. choosing \(z_{I,0}\) from \(G_N\);
2. choosing \(q_{V,0}\) from \(G_N\);
3. changing neighbour definition after lensing/free-fall comparison;
4. absorbing \(\mathcal R_Q^{ij}\) into \(\kappa_{\chi,I}\).

Allowed:

1. derive \(z_{I,0}\) from the adjacency graph;
2. derive \(q_{V,0}\) from reconstructed cell volumes;
3. declare anisotropy as a residual before experimental comparison.

Status:

`adjacency_shape_no_fit_rule`

### 41.7. What is closed

This section closes:

$$
z_I,\quad q_{V,I}
$$

as opaque geometry factors.

It replaces them with:

$$
z_I=\frac{2N_L}{N_E},
\qquad
q_{V,I}=\frac{\ell_0^3}{\langle V\rangle}.
$$

It does not yet derive:

1. exact regular geometry class;
2. exact isotropy;
3. exact \(D_S=3\);
4. numerical \(\ell_0\);
5. numerical \(G_I\).

Next target:

insert these geometry factors into the weak-gravity front status.

Geometry class gate:

`sections/48-geometry-class-gate.md`

Status:

`z_q_geometry_gap_reduced`
