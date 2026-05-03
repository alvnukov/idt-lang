## 54. Photon Dispersion Ledger Conversion

This section performs the first conditional source-cited ledger conversion.

It uses photon dispersion only.

It does not claim that the Fermi LIV convention is identical to the protolanguage dispersion convention.

Status:

`photon_dispersion_ledger_conversion_initialized`

### 54.1. Source value

Source:

`https://ntrs.nasa.gov/citations/20140005679`

Related paper:

`https://arxiv.org/abs/1305.3463`

The Fermi LAT GRB analysis reports, for the subluminal quadratic leading-order LIV case:

$$
E_{QG,2}>1.3\times10^{11}\ \mathrm{GeV}
$$

at \(95\%\) confidence, with the strongest bound from GRB 090510.

Status:

`fermi_quadratic_liv_source_value_recorded`

### 54.2. Frequency translation

Translate the quoted energy scale into an angular frequency scale:

$$
\omega_{QG,2}
=
\frac{E_{QG,2}}{\hbar}.
$$

Using:

$$
1\ \mathrm{GeV}=1.602176634\times10^{-10}\ \mathrm J,
$$

gives:

$$
\omega_{QG,2}
>
1.98\times10^{35}\ \mathrm{s}^{-1}.
$$

This is a published-LIV-convention scale, not automatically \(\omega_{\ell,I}\).

Status:

`fermi_energy_scale_to_frequency_scale`

### 54.3. Convention map

The protolanguage minimal dispersion residual is:

$$
\frac{v_g}{c_I}
=
1
+
\alpha_{\ell}^{(2)}(n)
\left(
\frac{\omega}{\omega_{\ell,I}}
\right)^2
+\cdots .
$$

The Fermi result is quoted in a standard LIV convention with a quadratic quantum-gravity energy scale \(E_{QG,2}\).

Define a convention factor:

$$
\kappa_{\mathrm{LIV}\to I}
$$

by:

$$
\left|
\alpha_{\ell}^{(2)}
\right|
\omega_{\ell,I}^{-2}
=
\kappa_{\mathrm{LIV}\to I}
\omega_{QG,2}^{-2}.
$$

Then:

$$
\omega_{\ell,I}
\ge
\sqrt{
\frac{|\alpha_{\ell}^{(2)}|}
{\kappa_{\mathrm{LIV}\to I}}
}
\;\omega_{QG,2}.
$$

The map is not closed until:

$$
\kappa_{\mathrm{LIV}\to I}
$$

is fixed by matching conventions.

Status:

`liv_convention_map_declared`

### 54.4. Order-one diagnostic

For an order-one convention comparison:

$$
\kappa_{\mathrm{LIV}\to I}\sim1.
$$

Using the axis coefficient:

$$
|\alpha_{\ell}^{(2)}|=\frac18,
$$

gives:

$$
\omega_{\ell,\min}^{(\gamma)}
\sim
7.0\times10^{34}\ \mathrm{s}^{-1}.
$$

Using the Fermi scale directly without the \(\sqrt{1/8}\) factor gives:

$$
\omega_{\ell,\min}^{(\gamma)}
\sim
2.0\times10^{35}\ \mathrm{s}^{-1}.
$$

Both are far below the minimal matched gravity-gate target:

$$
\omega_{\ell,G}
\approx
5.23\times10^{42}\ \mathrm{s}^{-1}.
$$

The ratio using the direct Fermi frequency is:

$$
\frac{\omega_{QG,2}}{\omega_{\ell,G}}
\approx
3.8\times10^{-8}.
$$

Status:

`fermi_bound_below_gravity_target`

### 54.5. Interpretation

Current conclusion:

$$
\omega_{\ell,\min}^{(\gamma)}
\ll
\omega_{\ell,G}.
$$

Therefore current photon-dispersion bounds do not exclude the minimal matched radar-orthogonal sector.

They also do not confirm it.

They only say:

$$
\omega_{\ell,I}
>
O(10^{35})\ \mathrm{s}^{-1}
$$

under the quadratic LIV convention comparison.

The gravity-gate target remains:

$$
O(10^{42})\ \mathrm{s}^{-1}.
$$

Status:

`photon_dispersion_not_yet_decisive`

### 54.6. No-fit rule

Forbidden:

1. set \(\kappa_{\mathrm{LIV}\to I}\) to make \(\omega_{\ell,\min}^{(\gamma)}=\omega_{\ell,G}\);
2. claim the Fermi quadratic LIV bound directly measures \(\omega_{\ell,I}\);
3. ignore the directional anisotropy in \(\alpha_{\ell}^{(2)}(n)\);
4. treat a lower bound far below \(\omega_{\ell,G}\) as confirmation.

Allowed:

1. use the Fermi value as a lower-bound anchor;
2. use the result to show the minimal sector is not excluded by this row;
3. improve the row only by deriving \(\kappa_{\mathrm{LIV}\to I}\) or using a source with the exact same dispersion convention.

Status:

`photon_conversion_no_fit_rule`

### 54.7. What is closed

Closed:

1. first source-cited non-gravity lower-bound row;
2. convention caveat;
3. comparison with \(\omega_{\ell,G}\).

Open:

1. exact LIV-to-protolanguage convention map;
2. stronger photon/clock bounds in the same convention;
3. matter-wave and clock-noise conversions;
4. proof of isotropic propagation.

Next target:

derive a clock-noise or matter-wave residual coefficient, because photon dispersion is currently too weak to decide the minimal sector.

Matter-wave link phase residual:

`sections/55-matter-wave-link-phase-residual.md`

Link frequency front status:

`sections/57-link-frequency-front-status.md`

Status:

`first_non_gravity_bound_inserted`
