## 37. Order-Count Link Density

This section reduces:

$$
n_L\ell_0^2
$$

to order/count geometry.

It does not use \(G_N\), Planck length, or Newtonian dynamics.

Status:

`order_count_link_density_initialized`

### 37.1. Link count

For a reconstructed spatial region \(U\), define:

$$
N_E(U)
=
\nu_{\mathrm{count}}(U)
$$

as the number of coarse spatial events/cells.

Let:

$$
N_L(U)
$$

be the number of admissible neighbour links \(\langle EF\rangle\subset U\).

Define mean spatial degree:

$$
z_I(U)
=
\frac{2N_L(U)}{N_E(U)}.
$$

Then:

$$
n_L(U)
=
\frac{N_L(U)}{\nu_{G,S}(U)}
=
\frac{z_I(U)}{2}
\lambda_I^{(3)}(U).
$$

Status:

`link_density_from_mean_degree`

### 37.2. Link-length moment

The stiffness factor actually needs:

$$
n_L\ell_0^2.
$$

For nonuniform links define:

$$
\langle \ell^2\rangle_L(U)
=
\frac{1}{N_L(U)}
\sum_{\langle EF\rangle\subset U}
h_{ij}\ell_{EF}^i\ell_{EF}^j.
$$

Then:

$$
n_L\ell_0^2
\quad
\text{is replaced by}
\quad
n_L\langle \ell^2\rangle_L.
$$

Using the degree/count relation:

$$
n_L\langle \ell^2\rangle_L
=
\frac{z_I}{2}
\lambda_I^{(3)}
\langle \ell^2\rangle_L.
$$

Status:

`link_length_moment_defined`

### 37.3. Cell shape factor

If the spatial readout has a stable cell scale \(\ell_0\), define the shape factor:

$$
q_{V,I}
=
\lambda_I^{(3)}
\ell_0^3.
$$

Equivalently:

$$
\lambda_I^{(3)}
=
\frac{q_{V,I}}{\ell_0^3}.
$$

Then the uniform-link factor becomes:

$$
n_L\ell_0^2
=
\frac{z_Iq_{V,I}}{2\ell_0}.
$$

The remaining length \(\ell_0\) is not fixed by this step.

It must come from order/count/clock reconstruction, not from \(G_N\).

Status:

`shape_factor_reduces_link_density`

### 37.4. Symbolic G update

With:

$$
x_0=1,
$$

the minimal weak-gravity expression becomes:

$$
G_I
=
\frac{c_I^4D_S}
{4\pi\kappa_{\chi,I}n_L\ell_0^2}.
$$

Using the shape-factor relation:

$$
G_I
=
\frac{c_I^4D_S\ell_0}
{2\pi\kappa_{\chi,I}z_Iq_{V,I}}.
$$

This is still not a numerical prediction.

It reduces the open geometry input to:

$$
D_S,\quad
z_I,\quad
q_{V,I},\quad
\ell_0.
$$

Status:

`G_symbolic_geometry_factor_reduced`

### 37.5. Geometry residuals

Degree residual:

$$
\mathcal R_z(U)
=
\frac{z_I(U)-z_{I,0}}{z_{I,0}}.
$$

Shape residual:

$$
\mathcal R_q(U)
=
\frac{q_{V,I}(U)-q_{V,0}}{q_{V,0}}.
$$

Link-length residual:

$$
\mathcal R_\ell(U)
=
\frac{\langle\ell^2\rangle_L-\ell_0^2}{\ell_0^2}.
$$

These residuals feed:

$$
\mathcal R_A^{ij},
\qquad
\mathcal R_G.
$$

Status:

`geometry_factor_residuals_defined`

### 37.6. No-fit constraints

Forbidden:

1. choosing \(z_I\) to match \(G_N\);
2. choosing \(q_{V,I}\) to match \(G_N\);
3. choosing \(\ell_0\) as Planck length;
4. changing link neighbourhood after gravitational comparison.

Allowed:

1. derive \(z_I\) from order adjacency;
2. derive \(q_{V,I}\) from count/volume reconstruction;
3. derive \(\ell_0\) from clock/order distance readout;
4. compare the resulting \(G_I\) without refit.

Status:

`link_geometry_no_fit_constraints`

### 37.7. What is closed

This section closes:

$$
n_L\ell_0^2
$$

as an opaque symbol.

It replaces it with:

$$
n_L\ell_0^2
=
\frac{z_Iq_{V,I}}{2\ell_0}
$$

in the uniform isotropic sector.

It does not yet derive:

1. exact regular geometry class;
2. exact isotropy;
3. global constancy of \(\ell_0,z_I,q_{V,I}\);
4. numerical \(G_I\).

Follow-up closure:

reduce \(\ell_0,z_I,q_{V,I}\) to clock/order/count readout invariants.

Clock-order distance scale:

`sections/40-clock-order-distance-scale.md`

Adjacency shape factor:

`sections/41-adjacency-shape-factor.md`

Status:

`link_density_gap_reduced`
