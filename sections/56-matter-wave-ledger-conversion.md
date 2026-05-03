## 56. Matter-Wave Ledger Conversion

This section performs a conservative conditional conversion of the matter-wave source anchors.

It does not claim a decisive bound.

Status:

`matter_wave_ledger_conversion_initialized`

### 56.1. Source value

Source:

`https://www.nature.com/articles/s41567-019-0663-9`

The molecular interference source reports:

1. masses beyond \(25{,}000\ \mathrm{Da}\);
2. up to \(2{,}000\) atoms;
3. de Broglie wavelengths down to:

$$
\lambda_{\mathrm{dB}}
=
53\ \mathrm{fm};
$$

4. visibility above \(90\%\) of the expected value;
5. macroscopicity \(\mu=14.1\).

Status:

`molecule_interference_source_value_recorded`

### 56.2. Wavenumber anchor

The de Broglie wavenumber is:

$$
k
=
\frac{2\pi}{\lambda_{\mathrm{dB}}}
\approx
1.19\times10^{14}\ \mathrm{m}^{-1}.
$$

The associated light-frequency scale is:

$$
c_Ik
\approx
3.55\times10^{22}\ \mathrm{s}^{-1}.
$$

This is not \(\omega_{\ell,I}\).

It is the experimental wavenumber scale probed by the matter wave.

Status:

`molecule_wavenumber_anchor`

### 56.3. Proxy visibility-to-phase assumption

The matter-wave residual formula gives:

$$
\left|
\frac{\Delta\phi_\ell}{\phi_0}
\right|
\le
\delta_{\phi,\mathrm{rel}}.
$$

Visibility above \(90\%\) of the expected value does not directly imply:

$$
\delta_{\phi,\mathrm{rel}}\le0.1.
$$

For a conservative proxy row only, define:

$$
\delta_{\phi,\mathrm{rel}}^{\mathrm{proxy}}=0.1.
$$

This proxy must be replaced by a real visibility-to-phase model before the row becomes a strict bound.

Status:

`visibility_phase_proxy_declared`

### 56.4. Conditional bound

Use the axis coefficient:

$$
|B_\phi|=\frac{1}{12}.
$$

Then:

$$
\omega_{\ell,I}
\ge
c_Ik
\left(
\frac{|B_\phi|}
{\delta_{\phi,\mathrm{rel}}}
\right)^{1/2}.
$$

With the proxy:

$$
\delta_{\phi,\mathrm{rel}}=0.1,
$$

the conditional bound is:

$$
\omega_{\ell,\min}^{(\mathrm{MW})}
\gtrsim
3.24\times10^{22}\ \mathrm{s}^{-1}.
$$

Status:

`molecule_proxy_bound_computed`

### 56.5. Comparison with gravity-gate target

The minimal matched gravity-gate target is:

$$
\omega_{\ell,G}
\approx
5.23\times10^{42}\ \mathrm{s}^{-1}.
$$

Therefore:

$$
\frac{
\omega_{\ell,\min}^{(\mathrm{MW})}
}{
\omega_{\ell,G}
}
\sim
6.2\times10^{-21}.
$$

This matter-wave row is far below the gravity-gate target.

It does not exclude the minimal matched sector.

It also does not confirm it.

Status:

`matter_wave_bound_not_decisive`

### 56.6. Nanoparticle anchor not converted

Source:

`https://www.nature.com/articles/s41586-025-09917-9`

The nanoparticle source reports:

1. sodium clusters with more than \(7{,}000\) atoms;
2. masses above \(170{,}000\ \mathrm{Da}\);
3. spatial separation about \(133\ \mathrm{nm}\);
4. macroscopicity \(\mu=15.5\).

This row is not converted here because the source anchor recorded in this ledger does not yet specify the de Broglie wavenumber and visibility-to-phase residual in the form required by section 55.

Status:

`nanoparticle_anchor_recorded_not_converted`

### 56.7. No-fit rule

Forbidden:

1. treat the \(0.1\) proxy as a measured phase residual;
2. use the weak matter-wave lower bound as evidence for \(\omega_{\ell,G}\);
3. choose \(B_\phi\) after seeing the visibility;
4. ignore the gap between visibility loss and coherent phase residual.

Allowed:

1. record the row as a conservative non-exclusion check;
2. replace the proxy with a real interferometer likelihood model;
3. use future high-\(k\), high-visibility matter waves to strengthen the bound.

Status:

`matter_wave_conversion_no_fit_rule`

### 56.8. What is closed

Closed:

1. first conditional matter-wave bound:

$$
\omega_{\ell,\min}^{(\mathrm{MW})}
\gtrsim
3.24\times10^{22}\ \mathrm{s}^{-1};
$$

2. explicit statement that the bound is not decisive;
3. explicit proxy caveat.

Open:

1. real visibility-to-phase residual model;
2. conversion of nanoparticle data;
3. stronger matter-wave high-\(k\) bound;
4. comparison with clock-noise routes.

Next target:

derive the visibility-to-phase likelihood model or move to clock-noise residuals.

Link frequency front status:

`sections/57-link-frequency-front-status.md`

Status:

`matter_wave_row_converted_as_proxy_only`
