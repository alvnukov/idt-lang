## 49. Link Scale Closure Gate

This section targets the last dimensional input in the minimal weak-gravity calculator:

$$
\ell_{0,*}.
$$

It does not compute \(\ell_{0,*}\) numerically.

It defines the non-gravitational gate that must compute or bound it.

Status:

`link_scale_closure_gate_initialized`

### 49.1. Link frequency

Define the link frequency:

$$
\omega_{\ell,I}
=
\frac{c_I}{\ell_{0,*}}.
$$

Equivalently:

$$
\ell_{0,*}
=
\frac{c_I}{\omega_{\ell,I}}.
$$

This shifts the remaining scale question from a length to a clock/phase cutoff question.

Status:

`link_frequency_defined`

### 49.2. Minimal orthogonal calculator in frequency form

From the radar-orthogonal sector:

$$
G_I^{(\mathrm{orth})}
=
\frac{\rho_{\chi,I}c_I^3\ell_{0,*}^2}
{4\pi\hbar_I}.
$$

Using:

$$
\ell_{0,*}=c_I/\omega_{\ell,I},
$$

gives:

$$
G_I^{(\mathrm{orth})}
=
\frac{\rho_{\chi,I}c_I^5}
{4\pi\hbar_I\omega_{\ell,I}^2}.
$$

Thus the weak-gravity route becomes predictive if:

$$
\omega_{\ell,I}
$$

is fixed without gravitational data.

Status:

`orthogonal_G_frequency_form`

### 49.3. Dimensionless gate

The dimensionless experimental gate becomes:

$$
\Pi_G^{(\omega)}
=
\frac{4\pi\hbar_I G_N\omega_{\ell,I}^2}
{\rho_{\chi,I}c_I^5}.
$$

Successful closure requires:

$$
\Pi_G^{(\omega)}
=
1\pm\epsilon_G.
$$

This gate may use \(G_N\) only after:

$$
\omega_{\ell,I},\rho_{\chi,I},\hbar_I,c_I
$$

are independently fixed.

Status:

`link_frequency_dimensionless_G_gate`

### 49.4. Non-gravitational routes to \(\omega_{\ell,I}\)

Allowed routes:

1. phase/action cutoff in the update kernel;
2. clock-network high-frequency dispersion;
3. matter-wave phase residual at high action density;
4. vacuum response pole or correlation time in the clock sector;
5. direct inherited-update counting if a primitive update spectrum is derived.

Forbidden routes:

1. \(G_N\Rightarrow\omega_{\ell,I}\);
2. \(l_P\Rightarrow\ell_{0,*}\);
3. black-hole or Planck-unit arguments used as definitions;
4. choosing the route after seeing the gravity residual.

Status:

`non_gravitational_link_frequency_routes`

### 49.5. Dispersion residual gate

If the clock-order link scale modifies high-frequency propagation, the leading residual can be written:

$$
\frac{v_g(\omega)}{c_I}
=
1
+
\alpha_{\ell}^{(2)}
\left(\frac{\omega}{\omega_{\ell,I}}\right)^2
+
O\left(\frac{\omega^4}{\omega_{\ell,I}^4}\right).
$$

Here:

$$
\alpha_{\ell}^{(2)}
$$

must be predicted by the kernel sector or declared as a residual.

Known experimental use:

absence of observed dispersion constrains:

$$
\left|
\alpha_{\ell}^{(2)}
\left(\frac{\omega}{\omega_{\ell,I}}\right)^2
\right|.
$$

This route can bound \(\omega_{\ell,I}\) without using \(G_N\).

Status:

`link_scale_dispersion_gate`

### 49.6. Clock-noise residual gate

If the link scale appears as irreducible clock-network sampling noise, write:

$$
S_y(f)
=
S_y^{\mathrm{known}}(f)
+
\mathcal R_{\ell,y}(f;\omega_{\ell,I}).
$$

The residual must be fixed before comparison with gravity.

Allowed:

$$
\text{clock comparison bounds}
\Rightarrow
\omega_{\ell,I}\text{ lower bound}.
$$

Forbidden:

$$
G_N
\Rightarrow
\mathcal R_{\ell,y}.
$$

Status:

`link_scale_clock_noise_gate`

### 49.7. What is closed

Closed:

$$
\ell_{0,*}
\Longleftrightarrow
\omega_{\ell,I}^{-1}
$$

as the remaining scale question.

Closed formula:

$$
G_I^{(\mathrm{orth})}
=
\frac{\rho_{\chi,I}c_I^5}
{4\pi\hbar_I\omega_{\ell,I}^2}.
$$

Open:

1. numerical \(\omega_{\ell,I}\);
2. kernel prediction of \(\alpha_{\ell}^{(2)}\);
3. clock-noise residual \(\mathcal R_{\ell,y}\);
4. whether current experiments already force \(\omega_{\ell,I}\) above the value required by \(G_N\);
5. numerical \(G_I\).

Next target:

build an experimental ledger for non-gravitational bounds on \(\omega_{\ell,I}\), then compare those bounds with the gravity-gate required value without using that value as input.

Gravity-gate link frequency:

`sections/50-gravity-gate-link-frequency.md`

Status:

`ell0_gap_reduced_to_link_frequency`
