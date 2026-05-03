## 138. SPARC Amplitude Obstruction Gate

Status:

`real_data_amplitude_obstruction`

Section 137 showed that the current screened demo profile is too small for the
DDO154 residual packet. This section turns that negative result into a rule:
future galaxy claims require a predeclared amplitude source or a derived
map-to-residual rule.

### 138.1. Lower-bound result

For the screened profile:

$$
\mathcal R_{\mathrm{screen}}(L)
=
A
\frac{(L/L_t)^n}{1+(L/L_t)^n},
$$

the maximum possible residual is:

$$
\max_L\mathcal R_{\mathrm{screen}}(L)=A.
$$

The DDO154 SPARC packet requires:

$$
\max_i\mathcal R_{\mathrm{SPARC},i}
=
6.842377551859201.
$$

Therefore any model that interprets \(\mathcal R_{\mathrm{screen}}\) as the
full missing acceleration fraction must satisfy:

$$
A\ge6.842377551859201.
$$

The current demo value:

$$
A=1
$$

has shortfall:

$$
6.842377551859201-1
=
5.842377551859201.
$$

### 138.2. No-postfit provenance rule

The amplitude cannot be chosen from:

$$
\texttt{sparc\_rotation\_curve\_data\_I},
\quad
\texttt{sparc\_galaxy\_residual\_packet\_I},
\quad
\texttt{observed\_centripetal\_acceleration\_I},
\quad
\texttt{baryonic\_rotation\_acceleration\_I}.
$$

Allowed future routes must be predeclared before checking additional galaxies:

1. derived source-stress amplitude;
2. derived inheritance activity amplitude;
3. derived map from screened slip to acceleration residual;
4. externally declared calibration with held-out validation.

### 138.3. Finite gates

Finite gate:

`sparc_ddo154_amplitude_lower_bound_demo`

Gate type:

`screened_amplitude_lower_bound`

It fails if:

1. the lower bound is not the maximum SPARC residual fraction;
2. the current shortfall is not recomputed;
3. a below-bound amplitude is declared to satisfy the bound.

Finite gate:

`galaxy_residual_no_postfit_demo`

Gate type:

`residual_no_postfit_provenance`

It fails if a declared pre-data amplitude route includes SPARC residual data as
one of its candidate sources.

### 138.4. Accepted and not accepted

Accepted:

`sparc_amplitude_lower_bound_I = experimental_gate`.

Accepted:

`galaxy_residual_no_postfit_policy_I = derived_conditional`.

Accepted:

the current \(A=1\) toy profile is below the DDO154 lower bound.

Not accepted:

raising \(A\) to \(6.842377551859201\) after seeing DDO154.

Not accepted:

using SPARC as both discovery and validation for the same residual amplitude.

### 138.5. Next required upgrade

The next cluster should build one of two things:

1. a derived amplitude route that produces \(A\) without SPARC input;
2. a map-to-residual route showing that \(\mathcal R_{\mathrm{screen}}\) is
   not the full acceleration residual and deriving the conversion factor.

Section 139 combines this amplitude bound with the solar residual bound and
excludes the old transition scale for the SPARC-minimum amplitude. Only after
that compatibility problem is solved should more SPARC galaxies be evaluated.
