## 58. Clock-Vacuum Pole Route

This section defines the non-gravitational spectral route to:

$$
\omega_{\ell,I}.
$$

It does not compute the numerical value.

It defines what must be computed from the inherited clock vacuum.

Status:

`clock_vacuum_pole_route_initialized`

### 58.1. Clock-strain response variable

Use the dimensionless clock-strain field:

$$
\varphi(E)=\log\chi(E).
$$

For a neighbour link:

$$
s_{EF}
=
\varphi(E)-\varphi(F).
$$

Let:

$$
J_{EF}(\tau)
$$

be the inherited clock-vacuum response current conjugate to \(s_{EF}\) in flat vacuum.

Status:

`clock_strain_response_current_defined`

### 58.2. Vacuum response function

Define the retarded flat-vacuum response:

$$
\mathcal R_{\chi,EF}(t)
=
\theta(t)
\langle
[J_{EF}(t),J_{EF}(0)]_{\mathrm{readout}}
\rangle_{\mathrm{vac}}.
$$

The frequency-domain response is:

$$
\mathcal R_{\chi,EF}(\omega)
=
\int_0^\infty
e^{i\omega t}
\mathcal R_{\chi,EF}(t)\,dt.
$$

This is a readout object, not a quantum-field postulate.

The bracket denotes the antisymmetric response pairing of the inherited update algebra in the clock-vacuum sector.

Status:

`clock_vacuum_response_function_defined`

### 58.3. Pole definition of link frequency

Define:

$$
\omega_{\ell,I}
=
\min_{\omega>0}
\left\{
\omega:
\mathcal R_{\chi,EF}(\omega)
\text{ has a stable pole or spectral edge}
\right\}.
$$

This definition is accepted only if the pole/edge is:

1. independent of clock species after calibration;
2. stable under coarse-graining;
3. local in the flat clock-radar domain;
4. not inferred from \(G_N\).

Status:

`omega_link_from_clock_vacuum_pole`

### 58.4. Low-frequency expansion

Below the first pole:

$$
|\omega|\ll\omega_{\ell,I},
$$

the response must admit:

$$
\mathcal R_{\chi}(\omega)
=
\mathcal R_0
\left[
1
+
r_2
\left(
\frac{\omega}{\omega_{\ell,I}}
\right)^2
+
O(\omega^4/\omega_{\ell,I}^4)
\right].
$$

The absence of a linear term is a time-reversal / reciprocity condition in the flat vacuum.

If a linear term appears, it is a pre-declared parity/time-asymmetry residual:

$$
\mathcal R_{\mathrm{odd}}.
$$

Status:

`low_frequency_even_response_expansion`

### 58.5. Relation to dispersion coefficients

The photon and matter-wave residual coefficients must be derived from:

$$
r_2,
\qquad
\text{neighbour geometry moments}.
$$

In the minimal nearest-neighbour sector this gave:

$$
\alpha_\ell^{(2)}(n)
=
-
\frac18
\sum_a n_a^4,
$$

and:

$$
B_\phi(n)
=
-
\frac1{12}
\sum_a n_a^4.
$$

A physical clock-vacuum pole route must either reproduce these conditional coefficients or replace them with a derived improved isotropic sector.

Status:

`response_pole_links_to_residual_coefficients`

### 58.6. No-gravity input rule

Forbidden:

1. choose the first pole so that \(G_I=G_N\);
2. define \(\omega_{\ell,I}\) from the observed Planck frequency;
3. tune \(r_2\) after photon or matter-wave comparison;
4. choose clock species after seeing the desired pole.

Allowed:

1. derive \(\omega_{\ell,I}\) from clock-vacuum response;
2. derive \(r_2\) from the same response;
3. compare the resulting \(\omega_{\ell,I}\) with \(\omega_{\ell,G}\);
4. record a residual if they disagree.

Status:

`clock_vacuum_pole_no_fit_rule`

### 58.7. What is closed

Closed as a route:

$$
\omega_{\ell,I}
\Leftarrow
\text{first clock-vacuum response pole/edge}.
$$

Open:

1. explicit inherited update algebra;
2. actual \(\mathcal R_{\chi}(\omega)\);
3. numerical pole;
4. proof of clock species universality;
5. relation between the pole and \(\kappa_{\chi,I}\).

Next target:

derive the algebraic relation between \(\omega_{\ell,I}\), \(\rho_{\chi,I}\), and \(\kappa_{\chi,I}\), then use it as a consistency gate between update-action and vacuum-response routes.

Kappa-omega consistency gate:

`sections/59-kappa-omega-consistency-gate.md`

Minimal clock-vacuum oscillator:

`sections/60-minimal-clock-vacuum-oscillator.md`

Status:

`clock_vacuum_pole_route_defined_not_solved`
