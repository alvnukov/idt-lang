## 130. Executable PPN No-Slip Sector

Status:

`executable_conditional_ppn_no_slip_sector`

This pass strengthens the weak-gravity front without assuming that GR is exact.
The PPN parameters remain explicit:

$$
\gamma_I^{\mathrm{PPN}},
\qquad
\beta_I^{\mathrm{PPN}}.
$$

If later data or primitive derivation requires deviations, the theory must keep
them as residuals rather than hiding them in a refit.

The checked target is:

$$
\texttt{ppn\_no\_slip\_validation\_I}.
$$

Its declared dependencies are:

$$
\Phi_I,\quad \Psi_I,\quad \gamma_I^{\mathrm{PPN}},\quad \beta_I^{\mathrm{PPN}}.
$$

### 130.1. No-slip gamma gate

Use the weak-field potentials:

$$
\Phi_I,\qquad \Psi_I.
$$

The no-slip sector is:

$$
\Psi_I=\Phi_I.
$$

Equivalently:

$$
\gamma_I^{\mathrm{PPN}}
=
\frac{\Psi_I}{\Phi_I}
=1.
$$

The verifier checks a finite sample:

$$
\Phi=[1,2,3],
\qquad
\Psi=[1,2,3],
$$

with maximum allowed slip fraction:

$$
\max_i\left|\frac{\Psi_i-\Phi_i}{\Phi_i}\right|
\le
10^{-12}.
$$

Finite gate:

`ppn_gamma_no_slip_demo`

This is not a primitive proof of no-slip. It is a machine-checkable definition
of the no-slip validation sector.

### 130.2. Light bending gate

The existing solar-limb light-bending gate uses:

$$
\Delta\theta
=
2(1+\gamma_I^{\mathrm{PPN}})
\frac{G_NM_\odot}{c^2b}.
$$

For:

$$
\gamma_I^{\mathrm{PPN}}=1,
$$

it gives:

$$
\Delta\theta
=
8.490267017584816\times10^{-6}\,\mathrm{rad}
\approx
1.75124\,\mathrm{arcsec}.
$$

Finite gate:

`ppn_light_bending_solar_limb_demo`

### 130.3. Shapiro delay gate

For a near-limb solar signal path:

$$
\Delta t
=
2(1+\gamma_I^{\mathrm{PPN}})
\frac{G_NM_\odot}{c^3}
\log\frac{4r_Er_R}{b^2}.
$$

Using:

$$
r_E=r_R=1\,\mathrm{AU},
\qquad
b=R_\odot,
\qquad
\gamma_I^{\mathrm{PPN}}=1,
$$

the verifier recomputes:

$$
\Delta t
=
2.3895007169711242\times10^{-4}\,\mathrm s.
$$

Finite gate:

`shapiro_delay_solar_limb_demo`

This uses the same \(\gamma_I^{\mathrm{PPN}}\) as light bending.

### 130.4. Perihelion gate

The PPN perihelion advance per orbit is:

$$
\Delta\omega
=
\frac{2+2\gamma_I^{\mathrm{PPN}}-\beta_I^{\mathrm{PPN}}}{3}
\frac{6\pi G_NM_\odot}{a(1-e^2)c^2}.
$$

For Mercury with:

$$
a=5.790905\times10^{10}\,\mathrm m,
\qquad
e=0.205630,
\qquad
\beta_I^{\mathrm{PPN}}=\gamma_I^{\mathrm{PPN}}=1,
$$

the verifier recomputes:

$$
\Delta\omega
=
5.018814721871578\times10^{-7}\,\mathrm{rad/orbit}
\approx
42.982\,\mathrm{arcsec/century}.
$$

Finite gate:

`ppn_perihelion_mercury_demo`

This gate prevents the theory from fitting clock/redshift and lensing while
leaving orbital dynamics disconnected.

### 130.5. Accepted and not accepted

Accepted:

`ppn_no_slip_validation_I = derived_conditional`

The accepted conditional cluster is:

$$
\Psi_I=\Phi_I
\Rightarrow
\gamma_I^{\mathrm{PPN}}=1
\Rightarrow
\text{light bending and Shapiro delay share the same parameter}.
$$

and:

$$
(\beta_I^{\mathrm{PPN}},\gamma_I^{\mathrm{PPN}})
\Rightarrow
\text{perihelion}.
$$

Not accepted:

`\Psi_I=\Phi_I` from primitives.

Not accepted:

`\gamma_I^{\mathrm{PPN}}=1` as an unconditional law.

Not accepted:

`Einstein equations = derived`.

### 130.6. Remaining hard problem

The next real derivation is:

$$
\Pi_I^{ij}\to0,
\quad
\mathcal R_{\mathrm{nonGR}}\to0,
\quad
\text{flat boundary}
\Rightarrow
\Psi_I=\Phi_I.
$$

This must come from inherited source stress, conservation, and geometry
readout, not from importing the GR field equations.
