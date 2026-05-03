## 40. Clock-Order Distance Scale

This section targets:

$$
\ell_0.
$$

It is the spatial link distance scale used by order/count geometry.

It must not be chosen from \(G_N\), Planck length, or Newtonian gravity.

Status:

`clock_order_distance_scale_initialized`

### 40.1. The gap

Spatial distance was defined as:

$$
d_S(A,B)
=
\ell_0
\inf_{\pi:A\to B}
\sum_{(X,Y)\in\pi}w_S(X,Y).
$$

This leaves \(\ell_0\) as a scale factor.

To avoid hidden fitting, \(\ell_0\) must be fixed by a non-gravitational distance calibration.

Status:

`ell0_scale_gap_declared`

### 40.2. Clock radar route

For two nearby spatial events \(A,B\) on a slice \(S\), use a local clock-radar loop:

$$
A
\to
B
\to
A.
$$

Let the round-trip clock time be:

$$
\Delta\tau_{ABA}.
$$

In a flat calibration domain with causal speed \(c_I\), define:

$$
d_{\mathrm{radar}}(A,B)
=
\frac{c_I}{2}\Delta\tau_{ABA}.
$$

For one admissible neighbour link:

$$
\langle AB\rangle,
$$

define:

$$
\ell_0
=
\frac{d_{\mathrm{radar}}(A,B)}
{w_S(A,B)}
$$

in the stable local calibration domain.

Status:

`ell0_from_clock_radar_route`

### 40.3. Order-distance consistency

The same \(\ell_0\) must make path distance consistent:

$$
d_S(A,B)
=
\ell_0
\inf_{\pi:A\to B}
\sum_{(X,Y)\in\pi}w_S(X,Y)
$$

with local radar distance:

$$
d_{\mathrm{radar}}(A,B).
$$

Define:

$$
\mathcal R_{\ell,\mathrm{radar}}(A,B)
=
\frac{d_S(A,B)-d_{\mathrm{radar}}(A,B)}
{d_{\mathrm{radar}}(A,B)}.
$$

Acceptance requires:

$$
|\mathcal R_{\ell,\mathrm{radar}}|
\le
\epsilon_\ell
$$

on the flat local calibration domain.

Status:

`order_distance_radar_consistency_gate`

### 40.4. No-gravity-input rule

Allowed inputs:

1. clock tick counts;
2. causal round-trip order;
3. flat-domain causal speed \(c_I\);
4. adjacency weights \(w_S\).

Forbidden inputs:

1. \(G_N\);
2. \(\ell_P\);
3. Newtonian orbital dynamics;
4. gravitational lensing;
5. choosing \(\epsilon_\ell\) after weak-gravity comparison.

Status:

`ell0_no_gravity_input_rule`

### 40.5. Link-length residual

For a region \(U\), define:

$$
\ell_0(U)
=
\left\langle
\frac{d_{\mathrm{radar}}(E,F)}
{w_S(E,F)}
\right\rangle_{\langle EF\rangle\subset U}.
$$

Residual:

$$
\mathcal R_{\ell_0}(U)
=
\frac{\ell_0(U)-\ell_{0,\infty}}
{\ell_{0,\infty}}.
$$

If nonzero, it feeds:

$$
\mathcal R_A^{ij},
\qquad
\mathcal R_G.
$$

Status:

`ell0_residual_defined`

### 40.6. What is closed

This section closes:

$$
\ell_0
\quad
\text{as arbitrary spatial scale.}
$$

It replaces it with:

$$
\ell_0
=
\frac{c_I\Delta\tau_{ABA}}
{2w_S(A,B)}
$$

in the flat local clock-radar calibration domain.

It does not yet derive:

1. uniqueness of \(w_S\);
2. exact flat-domain \(c_I\);
3. global constancy of \(\ell_0\);
4. Lorentzian signature;
5. numerical \(G_I\).

Next target:

derive \(z_I\) and \(q_{V,I}\) from the same spatial adjacency/cell structure.

Adjacency shape factor:

`sections/41-adjacency-shape-factor.md`

Link scale closure gate:

`sections/49-link-scale-closure-gate.md`

Status:

`ell0_gap_reduced`
