## 125. Non-Gravity Link-Scale Bound Cluster

Status: `positive_bound_cluster`, not closure.

This pass stops adding guard layers and extracts a positive result from the
already derived minimal link-dispersion residual.

### 125.1. Derived residual used

In the radar-orthogonal nearest-neighbour sector:

$$
\frac{v_g}{c_I}
=
1+
\alpha_\ell^{(2)}(n)
\left(
\frac{\omega}{\omega_{\ell,I}}
\right)^2
+O(\omega^4/\omega_{\ell,I}^4),
$$

with:

$$
\alpha_\ell^{(2)}(n)
=
-\frac18\sum_a n_a^4.
$$

For one radar-axis propagation:

$$
|\alpha_\ell^{(2)}|=\frac18.
$$

This coefficient came from the finite link Laplacian expansion, not from
photon or gravity data.

### 125.2. Photon branch

The photon-dispersion ledger records the quadratic Fermi-LAT scale:

$$
\omega_{QG,2}>1.98\times10^{35}\ \mathrm{s^{-1}}.
$$

Using the axis coefficient and an order-one convention map:

$$
\omega_{\ell,\min}^{(\gamma)}
\simeq
\sqrt{\frac18}\,\omega_{QG,2}
=
6.98\times10^{34}\ \mathrm{s^{-1}}.
$$

Therefore:

$$
\ell_0
\le
\frac{c_I}{\omega_{\ell,\min}^{(\gamma)}}
=
4.29\times10^{-27}\ \mathrm m.
$$

This is a conditional non-gravity upper bound on \(\ell_0\), not a fitted
value.

### 125.3. Matter-wave branch

The matter-wave proxy row gives:

$$
\omega_{\ell,\min}^{(\mathrm{MW})}
\gtrsim
3.24\times10^{22}\ \mathrm{s^{-1}},
$$

so:

$$
\ell_0
\lesssim
9.25\times10^{-15}\ \mathrm m.
$$

This is much weaker than the photon branch, but it is independent and
non-gravitational.

### 125.4. Composite result

The current non-gravity link-scale lower bound is:

$$
\omega_{\ell,I}
\ge
\max(
\omega_{\ell,\min}^{(\gamma)},
\omega_{\ell,\min}^{(\mathrm{MW})}
)
=
6.98\times10^{34}\ \mathrm{s^{-1}}.
$$

Thus:

$$
\ell_0
\le
4.29\times10^{-27}\ \mathrm m.
$$

For unit radar step \(N_r=1\), this also gives:

$$
\tau_{0,I}
\le
\frac{1}{\omega_{\ell,\min}}
=
1.43\times10^{-35}\ \mathrm s.
$$

### 125.5. Gap to gravity-matched target

The previous weak-gravity diagnostic target was:

$$
\omega_{\ell,G}
\approx
5.23\times10^{42}\ \mathrm{s^{-1}}.
$$

The current non-gravity bound is below that target by:

$$
\frac{\omega_{\ell,G}}{\omega_{\ell,\min}}
\approx
7.5\times10^7.
$$

So the positive conclusion is limited but real:

1. \(\ell_0\) is not closed;
2. \(\ell_0\) is now non-gravitationally bounded from above in the conditional
   minimal dispersion sector;
3. the best present branch is photon dispersion;
4. matter-wave data is currently not decisive;
5. the next useful route is a stronger clock-noise or high-frequency
   dispersion calculation, not another guard section.

Manifest symbols added:

1. `minimal_link_dispersion_residual_I`;
2. `photon_dispersion_omega_bound_obs`;
3. `matter_wave_omega_bound_proxy`;
4. `omega_ell_lower_bound_I`;
5. `ell0_upper_bound_I`;
6. `primitive_tick_upper_bound_I`.

Accepted:

`non_gravity_link_scale_bound_computed`

Not accepted:

`ell0_closure_I = derived`
