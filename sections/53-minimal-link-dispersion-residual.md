## 53. Minimal Link Dispersion Residual

This section derives the first non-gravity residual coefficient for the link-frequency ledger.

It is conditional on the simple radar-orthogonal nearest-neighbour wave sector.

Status:

`minimal_link_dispersion_residual_initialized`

### 53.1. Nearest-neighbour wave operator

In a flat radar-orthogonal sector, take the minimal spatial wave operator:

$$
\Delta_{\ell}\psi(x)
=
\frac{1}{\ell_{0,*}^2}
\sum_{a=1}^{D_S}
\left[
\psi(x+\ell_{0,*}e_a)
+
\psi(x-\ell_{0,*}e_a)
-
2\psi(x)
\right].
$$

Use the flat wave equation:

$$
\partial_t^2\psi
=
c_I^2\Delta_{\ell}\psi.
$$

This is not yet claimed as the physical propagation law.

It is the minimal conditional sector for computing a source-free dispersion residual.

Status:

`minimal_nearest_neighbour_wave_operator`

### 53.2. Dispersion relation

For:

$$
\psi\sim e^{i(k\cdot x-\omega t)},
$$

the dispersion relation is:

$$
\omega^2(k)
=
\frac{4c_I^2}{\ell_{0,*}^2}
\sum_{a=1}^{D_S}
\sin^2
\left(
\frac{k_a\ell_{0,*}}{2}
\right).
$$

For:

$$
k\ell_{0,*}\ll1,
$$

expand:

$$
\omega^2
=
c_I^2k^2
-
\frac{c_I^2\ell_{0,*}^2}{12}
\sum_a k_a^4
+
O(k^6\ell_{0,*}^4).
$$

Status:

`minimal_link_dispersion_relation`

### 53.3. Group velocity residual

Let:

$$
n_a=\frac{k_a}{k},
\qquad
\sum_a n_a^2=1.
$$

Then:

$$
\omega
=
c_Ik
\left[
1
-
\frac{k^2\ell_{0,*}^2}{24}
\sum_a n_a^4
+
O(k^4\ell_{0,*}^4)
\right].
$$

The group velocity along fixed direction \(n\) is:

$$
\frac{v_g}{c_I}
=
1
-
\frac18
\left(
\sum_a n_a^4
\right)
(k\ell_{0,*})^2
+
O(k^4\ell_{0,*}^4).
$$

Using:

$$
\omega_{\ell,I}=\frac{c_I}{\ell_{0,*}},
\qquad
\omega\simeq c_Ik,
$$

gives:

$$
\frac{v_g}{c_I}
=
1
+
\alpha_{\ell}^{(2)}(n)
\left(
\frac{\omega}{\omega_{\ell,I}}
\right)^2
+
O(\omega^4/\omega_{\ell,I}^4),
$$

with:

$$
\alpha_{\ell}^{(2)}(n)
=
-
\frac18
\sum_a n_a^4.
$$

Status:

`minimal_group_velocity_coefficient`

### 53.4. Directional values

For propagation along one radar axis:

$$
\sum_a n_a^4=1,
$$

so:

$$
\alpha_{\ell,\mathrm{axis}}^{(2)}
=
-\frac18.
$$

For a three-dimensional body diagonal:

$$
n_a=\frac{1}{\sqrt3},
\qquad
\sum_a n_a^4=\frac13,
$$

so:

$$
\alpha_{\ell,\mathrm{diag}}^{(2)}
=
-\frac1{24}.
$$

Thus the minimal orthogonal nearest-neighbour sector is not fully fourth-order isotropic.

Its anisotropy is not hidden.

It is exactly the \(\mathcal R_4\) residual declared in the geometry class gate.

Status:

`dispersion_anisotropy_exposed`

### 53.5. Isotropic effective coefficient

If the coarse-grained geometry removes the fourth-moment anisotropy, replace:

$$
\sum_a n_a^4
$$

by an isotropic coefficient:

$$
\zeta_4.
$$

Then:

$$
\alpha_{\ell,\mathrm{iso}}^{(2)}
=
-\frac{\zeta_4}{8}.
$$

This coefficient must be derived from the actual coarse-grained neighbour distribution.

It must not be chosen from photon-dispersion data.

Status:

`isotropic_dispersion_coefficient_gate`

### 53.6. Bound insertion

The photon dispersion bound formula now has a conditional coefficient:

$$
\omega_{\ell,I}^2
\ge
\left|
\alpha_{\ell}^{(2)}(n)
\right|
\frac{L|\omega_1^2-\omega_2^2|}
{c_I\delta t_{\mathrm{obs}}}.
$$

For the axis value:

$$
|\alpha_{\ell}^{(2)}|=\frac18.
$$

For the diagonal value:

$$
|\alpha_{\ell}^{(2)}|=\frac1{24}.
$$

For an isotropic sector:

$$
|\alpha_{\ell}^{(2)}|=\frac{\zeta_4}{8}.
$$

Status:

`dispersion_bound_coefficient_inserted`

### 53.7. No-fit rule

Forbidden:

1. choose propagation direction \(n\) to satisfy \(G_N\);
2. average the anisotropy away without deriving the coarse-grained neighbour distribution;
3. call the nearest-neighbour operator physical before passing photon/clock dispersion gates;
4. change \(\alpha_{\ell}^{(2)}\) after comparing with GRB or clock data.

Allowed:

1. use \(\alpha_{\ell,\mathrm{axis}}^{(2)}=-1/8\) as a pre-declared worst-case axis sector;
2. use \(\alpha_{\ell,\mathrm{diag}}^{(2)}=-1/24\) as a pre-declared diagonal sector;
3. derive \(\zeta_4\) from an isotropic coarse-grained geometry.

Status:

`minimal_dispersion_no_fit_rule`

### 53.8. What is closed

Closed conditionally:

$$
p=2,
\qquad
\alpha_{\ell}^{(2)}(n)
=
-
\frac18
\sum_a n_a^4.
$$

Open:

1. proof that the physical propagation operator is nearest-neighbour;
2. fourth-order isotropy under coarse-graining;
3. source-cited insertion of \(L,\omega_1,\omega_2,\delta t_{\mathrm{obs}}\);
4. comparison with \(\omega_{\ell,G}\).

Next target:

use this conditional coefficient to populate the photon-dispersion row with a transparent bound, while keeping the result marked as conditional.

Photon dispersion ledger conversion:

`sections/54-photon-dispersion-ledger-conversion.md`

Status:

`first_residual_coefficient_conditionally_derived`
