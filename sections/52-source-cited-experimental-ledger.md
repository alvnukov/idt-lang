## 52. Source-Cited Experimental Ledger

This section begins the source-cited ledger for:

$$
\omega_{\ell,\mathrm{NG}}.
$$

It does not claim a numerical non-gravity value yet.

It records experimental anchors and states whether they can already be converted into a bound in the present theory.

Status:

`source_cited_experimental_ledger_initialized`

### 52.1. Constants used only for diagnostic gravity target

Use CODATA/NIST 2022 values for diagnostic comparison:

Source:

`https://www.nist.gov/publications/codata-recommended-values-fundamental-physical-constants-2022`

Diagnostic minimal matched sector:

$$
\rho_{\chi,I}=1.
$$

Then:

$$
\ell_{0,G}
=
2\sqrt{\pi}\;l_{P,\mathrm{obs}}
\approx
5.72947\times10^{-35}\ \mathrm m,
$$

and:

$$
\omega_{\ell,G}
=
\frac{c}{\ell_{0,G}}
\approx
5.23246\times10^{42}\ \mathrm{s}^{-1}.
$$

These are not inputs.

They are the gravity-gate target of the already declared minimal sector.

Status:

`diagnostic_gravity_target_numeric`

### 52.2. Photon dispersion anchor

Source:

`https://www.nature.com/articles/nature08574`

Experimental anchor:

Fermi/LAT GRB 090510 reported photons up to about \(31\ \mathrm{GeV}\), found no evidence for Lorentz-invariance violation, and quoted a lower limit \(1.2E_{\mathrm{Planck}}\) on a linear energy-dependence scale.

Ledger status:

`source_anchor_recorded_not_converted`

Reason:

Our current declared residual is quadratic:

$$
\frac{v_g(\omega)}{c_I}
=
1
+
\alpha_\ell^{(2)}
\left(\frac{\omega}{\omega_{\ell,I}}\right)^2
+\cdots .
$$

The Fermi result is directly stated for a linear energy-dependence model.

It cannot be imported as a numerical \(\omega_{\ell,I}\) bound until the kernel declares:

1. whether the leading residual is linear or quadratic;
2. \(\alpha_\ell^{(2)}\) or the corresponding linear coefficient;
3. the cosmological time-of-flight integral used by the theory.

Status:

`photon_dispersion_bound_blocked_by_kernel_coefficient`

### 52.3. Clock-network anchors

Source:

`https://www.nature.com/articles/s41467-023-40629-8`

Experimental anchor:

The miniature optical-clock network measured a fractional frequency gradient:

$$
[-12.4\pm0.7_{\mathrm{stat}}\pm2.5_{\mathrm{sys}}]\times10^{-19}/\mathrm{cm},
$$

consistent with the expected gravitational redshift gradient:

$$
-10.9\times10^{-19}/\mathrm{cm}.
$$

The same source reports a deviation constraint:

$$
0.13\pm0.23
$$

for millimetre-to-centimetre height differences.

Additional source:

`https://www.nature.com/articles/s41586-018-0738-2`

Experimental anchor:

Independent Yb optical lattice clocks reported systematic uncertainty:

$$
1.4\times10^{-18},
$$

measurement instability:

$$
3.2\times10^{-19},
$$

and reproducibility:

$$
[-7\pm5_{\mathrm{stat}}\pm8_{\mathrm{sys}}]\times10^{-19}.
$$

Ledger status:

`clock_anchor_recorded_not_converted`

Reason:

These data constrain clock universality, redshift readout, and unexplained clock-network residuals.

They do not yet produce \(\omega_{\ell,I}\) until the theory declares:

$$
S_y^\ell(f)
=
B_y
\left(
\frac{2\pi f}{\omega_{\ell,I}}
\right)^p
$$

with fixed \(B_y,p\).

Status:

`clock_bounds_blocked_by_noise_model`

### 52.4. Matter-wave anchors

Source:

`https://www.nature.com/articles/s41567-019-0663-9`

Experimental anchor:

Molecular interference was demonstrated for masses beyond \(25{,}000\ \mathrm{Da}\), with up to \(2{,}000\) atoms, de Broglie wavelengths down to \(53\ \mathrm{fm}\), visibility above \(90\%\) of the expected value, and macroscopicity \(\mu=14.1\).

Additional source:

`https://www.nature.com/articles/s41586-025-09917-9`

Experimental anchor:

Nanoparticle matter-wave interferometry was reported for sodium clusters with more than \(7{,}000\) atoms, masses above \(170{,}000\ \mathrm{Da}\), spatial separation about \(133\ \mathrm{nm}\), and macroscopicity \(\mu=15.5\).

Ledger status:

`matter_wave_anchor_recorded_not_converted`

Reason:

These experiments bound any link-scale loss of quantum phase/coherence, but conversion requires a pre-declared residual:

$$
\Delta\phi_\ell
=
B_\phi
\left(
\frac{k}{k_{\ell,I}}
\right)^p
\Delta\phi_{\mathrm{QM}}.
$$

The coefficients \(B_\phi,p\) are not yet derived.

Status:

`matter_wave_bounds_blocked_by_phase_residual_model`

### 52.5. Atom-interferometry gravity-phase anchor

Source:

`https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.125.191101`

Experimental anchor:

The atom-interferometric equivalence-principle test reports a \(10^{-12}\)-level comparison using \(^{85}\mathrm{Rb}\) and \(^{87}\mathrm{Rb}\) matter waves with a \(2\ \mathrm{s}\) free-fall time.

Ledger status:

`atom_interferometry_anchor_recorded_not_converted`

Reason:

This is a direct matter-wave gravity-phase gate and constrains species-dependent acceleration residuals.

It does not by itself fix \(\omega_{\ell,I}\) unless the link-scale phase residual also predicts a species/mass dependence.

Status:

`atom_interferometry_blocks_universal_phase_residuals`

### 52.6. Current ledger conclusion

Current source-cited status:

| Route | Source anchor | Direct \(\omega_{\ell,I}\) value now? | Blocker |
|---|---|---:|---|
| photon dispersion | GRB 090510 | no | leading exponent/coefficient |
| clock network | optical clocks/redshift | no | clock-noise residual model |
| matter waves | molecules/nanoparticles | no | phase residual coefficient |
| atom interferometry | Rb WEP matter waves | no | species/mass residual model |
| gravity gate | CODATA + \(G_N\) | diagnostic only | cannot be input |

Therefore:

$$
\omega_{\ell,\mathrm{NG}}
$$

is not yet computed.

The honest next theoretical target is not another experimental number.

It is the kernel prediction of at least one coefficient:

$$
\alpha_\ell^{(2)},
\qquad
B_y,
\qquad
B_\phi,
\qquad
p.
$$

Status:

`ledger_populated_but_conversion_blocked`

### 52.7. No-fit rule

Forbidden:

1. use the gravity-gate value \(\omega_{\ell,G}\) to choose \(\alpha_\ell^{(2)}\), \(B_y\), \(B_\phi\), or \(p\);
2. quote photon linear-dispersion bounds as quadratic bounds without deriving the exponent map;
3. quote matter-wave visibility as a phase-residual bound without a visibility-to-phase model;
4. call the ledger a prediction while all non-gravity conversions are blocked.

Allowed:

1. use these sources as acceptance gates;
2. derive one residual model and then convert the corresponding row;
3. exclude sectors if a source-cited bound exceeds \(\omega_{\ell,G}\).

Status:

`source_ledger_no_fit_rule`

### 52.8. What is closed

Closed:

1. source-cited experimental anchors;
2. diagnostic gravity-target value for the minimal matched sector;
3. explicit statement that no non-gravity \(\omega_{\ell,I}\) has yet been computed.

Open:

1. kernel dispersion coefficient;
2. clock-noise coefficient;
3. matter-wave phase residual coefficient;
4. first actual non-gravity conversion.

Next target:

derive the leading link-scale residual exponent \(p\) and coefficient for one route, preferably photon/clock dispersion because it connects most directly to \(\omega_{\ell,I}\).

Minimal link dispersion residual:

`sections/53-minimal-link-dispersion-residual.md`

Photon dispersion ledger conversion:

`sections/54-photon-dispersion-ledger-conversion.md`

Matter-wave ledger conversion:

`sections/56-matter-wave-ledger-conversion.md`

Status:

`experimental_ledger_ready_for_kernel_residual`
