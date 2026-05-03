## 126. Executable Link-Scale Bound

Status: `executable_positive_bound`.

The non-gravity link-scale bound is now machine checked. The verifier
recomputes each branch and rejects copied or mistyped numerical values.

### 126.1. Photon branch check

The executable photon branch uses:

$$
\omega_{\ell,\min}^{(\gamma)}
=
\sqrt{\frac{|\alpha_\ell^{(2)}|}{\kappa_{\mathrm{LIV}\to I}}}
\omega_{QG,2}.
$$

With:

$$
|\alpha_\ell^{(2)}|=\frac18,\qquad
\kappa_{\mathrm{LIV}\to I}=1,
\qquad
\omega_{QG,2}=1.9750476834523637\times10^{35}\ \mathrm{s^{-1}},
$$

the verifier checks:

$$
\omega_{\ell,\min}^{(\gamma)}
=
6.982848050679741\times10^{34}\ \mathrm{s^{-1}}.
$$

Gate:

`photon_dispersion_bound_demo`

### 126.2. Matter-wave branch check

The executable matter-wave proxy branch uses:

$$
\omega_{\ell,\min}^{(\mathrm{MW})}
=
c_Ik
\sqrt{
\frac{|B_\phi|}
{\delta_{\phi,\mathrm{rel}}}
}.
$$

With:

$$
|B_\phi|=\frac1{12},
\qquad
\delta_{\phi,\mathrm{rel}}=0.1,
\qquad
k=1.19\times10^{14}\ \mathrm{m^{-1}},
$$

the verifier checks the proxy value:

$$
\omega_{\ell,\min}^{(\mathrm{MW})}
\approx
3.256694654360982\times10^{22}\ \mathrm{s^{-1}}.
$$

Gate:

`matter_wave_bound_demo`

### 126.3. Composite bound check

The composite non-gravity lower bound is:

$$
\omega_{\ell,\min}
=
\max(
\omega_{\ell,\min}^{(\gamma)},
\omega_{\ell,\min}^{(\mathrm{MW})}
).
$$

The verifier checks:

$$
\omega_{\ell,\min}
=
6.982848050679741\times10^{34}\ \mathrm{s^{-1}}.
$$

Gate:

`composite_omega_bound_demo`

### 126.4. Length and tick checks

The verifier then computes:

$$
\ell_{0,\max}
=
\frac{c_I}{\omega_{\ell,\min}}
=
4.293269104872143\times10^{-27}\ \mathrm m,
$$

and for one radar step:

$$
\tau_{0,\max}
=
\frac1{\omega_{\ell,\min}}
=
1.4320804368943517\times10^{-35}\ \mathrm s.
$$

Gate:

`ell0_tick_bound_demo`

### 126.5. Status

This is not a closure of \(\ell_0\). It is a verified non-gravity bound:

$$
\ell_0\le4.293269104872143\times10^{-27}\ \mathrm m.
$$

Accepted:

`executable_non_gravity_link_bound`

Not accepted:

`ell0_closure_I = derived`
