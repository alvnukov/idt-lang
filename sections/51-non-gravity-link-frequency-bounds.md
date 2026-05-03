## 51. Non-Gravity Link Frequency Bounds

This section defines how non-gravitational experiments bound:

$$
\omega_{\ell,\mathrm{NG}}.
$$

It contains formulas, not populated experimental numbers.

No \(G_N\) input is allowed in these bounds.

Status:

`non_gravity_link_frequency_bounds_initialized`

### 51.1. Dispersion time-of-flight bound

Use the declared dispersion residual:

$$
\frac{v_g(\omega)}{c_I}
=
1
+
\alpha_{\ell}^{(2)}
\left(\frac{\omega}{\omega_{\ell,I}}\right)^2
+O(\omega^4/\omega_{\ell,I}^4).
$$

For propagation distance \(L\), the differential delay between \(\omega_1,\omega_2\) is:

$$
\Delta t_{\ell}
\simeq
-
\frac{L}{c_I}
\alpha_{\ell}^{(2)}
\frac{\omega_1^2-\omega_2^2}{\omega_{\ell,I}^2}.
$$

If the observed residual satisfies:

$$
|\Delta t_{\ell}|
\le
\delta t_{\mathrm{obs}},
$$

then:

$$
\omega_{\ell,I}^2
\ge
\left|
\alpha_{\ell}^{(2)}
\right|
\frac{L|\omega_1^2-\omega_2^2|}
{c_I\delta t_{\mathrm{obs}}}.
$$

Status:

`dispersion_tof_bound_formula`

### 51.2. Clock-network noise bound

Let a clock comparison bound the unexplained fractional frequency-noise spectrum:

$$
S_y^{\mathrm{res}}(f)
\le
S_y^{\mathrm{obs}}(f).
$$

If the link-scale contribution has the form:

$$
S_y^{\ell}(f)
=
B_y
\left(
\frac{2\pi f}{\omega_{\ell,I}}
\right)^p,
$$

then:

$$
\omega_{\ell,I}
\ge
2\pi f
\left(
\frac{B_y}{S_y^{\mathrm{obs}}(f)}
\right)^{1/p}.
$$

Here \(B_y\) and \(p\) must be predicted by the clock/update sector or declared before fitting.

Status:

`clock_noise_bound_formula`

### 51.3. Matter-wave phase residual bound

For an interferometer with known quantum phase:

$$
\Delta\phi_{\mathrm{QM}}
=
\frac{\Delta S}{\hbar_I},
$$

write the link-scale residual as:

$$
\Delta\phi_{\ell}
=
B_\phi
\left(
\frac{k}{k_{\ell,I}}
\right)^p
\Delta\phi_{\mathrm{QM}},
$$

where:

$$
k_{\ell,I}
=
\frac{\omega_{\ell,I}}{c_I}.
$$

If:

$$
|\Delta\phi_{\ell}|
\le
\delta\phi_{\mathrm{obs}},
$$

then:

$$
\omega_{\ell,I}
\ge
c_Ik
\left(
\frac{|B_\phi\Delta\phi_{\mathrm{QM}}|}
{\delta\phi_{\mathrm{obs}}}
\right)^{1/p}.
$$

The coefficients \(B_\phi,p\) must be declared before using the experiment.

Status:

`matter_wave_phase_bound_formula`

### 51.4. Link-frequency lower-bound ledger

Each non-gravity route produces:

$$
\omega_{\ell,I}
\ge
\omega_{\ell,\min}^{(r)}.
$$

The combined lower bound is:

$$
\omega_{\ell,I}
\ge
\omega_{\ell,\min}
=
\max_r
\omega_{\ell,\min}^{(r)}.
$$

This becomes a consistency check against the gravity-gate target:

$$
\omega_{\ell,G}
=
\left(
\frac{\rho_{\chi,I}c_I^5}
{4\pi\hbar_I G_N}
\right)^{1/2}.
$$

If:

$$
\omega_{\ell,\min}
>
\omega_{\ell,G}
$$

and the sector has no compensating pre-declared residual, then the minimal orthogonal gravity route is excluded.

Status:

`combined_non_gravity_lower_bound`

### 51.5. Positive signal case

If a non-gravity experiment detects a residual and the kernel predicts its coefficient, it may estimate:

$$
\omega_{\ell,\mathrm{NG}}.
$$

Then the gravity comparison is:

$$
\Xi_\ell
=
\frac{\omega_{\ell,\mathrm{NG}}^2}
{\omega_{\ell,G}^2}.
$$

Successful closure:

$$
\Xi_\ell=1\pm\epsilon_G.
$$

Status:

`positive_non_gravity_signal_comparison`

### 51.6. No-fit rule

Forbidden:

1. choose \(B_y,B_\phi,\alpha_\ell^{(2)},p\) after seeing \(G_N\);
2. discard a non-gravity bound because it conflicts with the gravity gate;
3. reinterpret an experimental null result as a signal;
4. tune \(\rho_{\chi,I}\) to rescue the sector.

Allowed:

1. use null experiments to exclude sectors;
2. use positive residuals only if their coefficients were pre-declared;
3. keep \(\omega_{\ell,G}\) as a comparison target only.

Status:

`non_gravity_bound_no_fit_rule`

### 51.7. What is closed

Closed:

1. dispersion bound formula;
2. clock-noise bound formula;
3. matter-wave phase residual bound formula;
4. combined lower-bound rule.

Open:

1. actual experimental numbers;
2. kernel coefficients \(\alpha_\ell^{(2)},B_y,B_\phi,p\);
3. whether current experiments already exclude the minimal orthogonal sector;
4. positive residual search strategy.

Next target:

populate the ledger with real experimental bounds from clock comparisons, photon dispersion, and matter-wave interferometry using source-cited values.

Source-cited experimental ledger:

`sections/52-source-cited-experimental-ledger.md`

Status:

`non_gravity_bounds_calculator_ready`
