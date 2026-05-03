## 55. Matter-Wave Link Phase Residual

This section derives a conditional matter-wave phase residual from the same minimal nearest-neighbour spatial operator used for photon dispersion.

It is a non-gravitational route to bounding:

$$
\omega_{\ell,I}.
$$

Status:

`matter_wave_link_phase_residual_initialized`

### 55.1. Minimal matter-wave kinetic operator

Use the minimal link Laplacian:

$$
\Delta_\ell\psi(x)
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

The conditional nonrelativistic matter-wave equation is:

$$
i\hbar_I\partial_t\psi
=
-
\frac{\hbar_I^2}{2m}
\Delta_\ell\psi.
$$

Status:

`minimal_matter_wave_link_laplacian`

### 55.2. Energy dispersion

For:

$$
\psi\sim e^{i(k\cdot x-\omega t)},
$$

the kinetic energy is:

$$
E_\ell(k)
=
\frac{2\hbar_I^2}{m\ell_{0,*}^2}
\sum_a
\left[
1-\cos(k_a\ell_{0,*})
\right].
$$

For:

$$
k\ell_{0,*}\ll1,
$$

expand:

$$
E_\ell(k)
=
\frac{\hbar_I^2k^2}{2m}
-
\frac{\hbar_I^2\ell_{0,*}^2}{24m}
\sum_a k_a^4
+
O(k^6\ell_{0,*}^4).
$$

The standard kinetic energy is:

$$
E_0(k)
=
\frac{\hbar_I^2k^2}{2m}.
$$

Status:

`matter_wave_energy_dispersion_residual`

### 55.3. Phase residual

For propagation time \(T\), the link-scale phase correction is:

$$
\Delta\phi_\ell
=
-
\frac{1}{\hbar_I}
\frac{\hbar_I^2\ell_{0,*}^2T}{24m}
\sum_a k_a^4.
$$

Thus:

$$
\Delta\phi_\ell
=
-
\frac{\hbar_I T}{24m}
\left(
\frac{c_I}{\omega_{\ell,I}}
\right)^2
\sum_a k_a^4.
$$

Using:

$$
n_a=k_a/k,
$$

gives:

$$
\Delta\phi_\ell
=
-
\frac{\hbar_I k^2T}{24m}
\left(
\frac{c_Ik}{\omega_{\ell,I}}
\right)^2
\sum_a n_a^4.
$$

Status:

`matter_wave_phase_residual_formula`

### 55.4. Relative phase residual

The ordinary kinetic phase magnitude is:

$$
\phi_0
=
\frac{E_0T}{\hbar_I}
=
\frac{\hbar_Ik^2T}{2m}.
$$

Therefore:

$$
\frac{\Delta\phi_\ell}{\phi_0}
=
-
\frac{1}{12}
\left(
\frac{c_Ik}{\omega_{\ell,I}}
\right)^2
\sum_a n_a^4.
$$

This has the same leading exponent:

$$
p=2.
$$

The matter-wave phase coefficient is:

$$
B_\phi(n)
=
-
\frac{1}{12}
\sum_a n_a^4.
$$

Status:

`matter_wave_relative_phase_coefficient`

### 55.5. Directional values

Axis propagation:

$$
B_{\phi,\mathrm{axis}}
=
-\frac{1}{12}.
$$

Three-dimensional diagonal propagation:

$$
B_{\phi,\mathrm{diag}}
=
-\frac{1}{36}.
$$

As with photon dispersion, this exposes a fourth-moment anisotropy.

It must be removed by a derived isotropic coarse-grained geometry or carried as a residual.

Status:

`matter_wave_directional_coefficients`

### 55.6. Bound insertion

If an interferometer constrains:

$$
|\Delta\phi_\ell|
\le
\delta\phi_{\mathrm{obs}},
$$

then:

$$
\omega_{\ell,I}
\ge
c_Ik
\left[
\frac{
|B_\phi(n)|\,|\phi_0|
}{
\delta\phi_{\mathrm{obs}}
}
\right]^{1/2}.
$$

Equivalently, if only a relative phase residual is bounded:

$$
\left|
\frac{\Delta\phi_\ell}{\phi_0}
\right|
\le
\delta_{\phi,\mathrm{rel}},
$$

then:

$$
\omega_{\ell,I}
\ge
c_Ik
\left[
\frac{|B_\phi(n)|}
\delta_{\phi,\mathrm{rel}}
\right]^{1/2}.
$$

Status:

`matter_wave_bound_ready`

### 55.7. No-fit rule

Forbidden:

1. choose \(B_\phi\) from observed visibility;
2. replace visibility loss by phase residual without a visibility model;
3. average directional anisotropy away without deriving the neighbour distribution;
4. tune \(\omega_{\ell,I}\) from \(G_N\).

Allowed:

1. use axis/diagonal coefficients as pre-declared conditional sectors;
2. derive an isotropic \(B_\phi\) from coarse-graining;
3. convert source-cited matter-wave experiments only after choosing a visibility-to-phase residual model.

Status:

`matter_wave_phase_no_fit_rule`

### 55.8. What is closed

Closed conditionally:

$$
p=2,
\qquad
B_\phi(n)
=
-
\frac{1}{12}
\sum_a n_a^4.
$$

Open:

1. whether matter waves use the same nearest-neighbour operator;
2. visibility-to-phase residual mapping;
3. source-cited insertion for molecular/nanoparticle experiments;
4. comparison with \(\omega_{\ell,G}\).

Next target:

convert the molecular/nanoparticle source anchors into conservative matter-wave link-frequency bounds, explicitly marking the visibility-to-phase assumption.

Matter-wave ledger conversion:

`sections/56-matter-wave-ledger-conversion.md`

Status:

`matter_wave_residual_coefficient_conditionally_derived`
