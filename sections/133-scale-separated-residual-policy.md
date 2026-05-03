## 133. Scale-Separated Residual Policy

Status:

`executable_conditional_scale_residual_policy`

The theory should not blindly assume that the no-residual weak-field sector is
valid at every scale. The safe statement is narrower:

1. solar-system and laboratory tests define a validated weak-field domain;
2. residuals must be below the accepted bounds inside that domain;
3. galactic or cosmological residuals may be explored only as explicit
   \(\mathcal R_{\mathrm{nonGR}}\) candidates;
4. no residual may be used by refitting \(G\), \(\gamma\), or \(\beta\) inside
   the validated domain.

The checked target is:

$$
\texttt{scale\_separated\_residual\_policy\_I}.
$$

It depends on:

$$
\texttt{validated\_weak\_field\_domain\_I},
\quad
\texttt{transition\_scale\_I},
\quad
\texttt{non\_gravity\_slip\_residual\_I},
\quad
\texttt{dark\_sector\_residual\_candidate\_I}.
$$

### 133.1. Validated-domain residual bound

The verifier checks that residual samples inside the validated domain remain
below the declared bound.

Finite sample:

$$
L=[1,10,10^5],
\qquad
\mathcal R=[10^{-8},2\times10^{-8},10^{-2}].
$$

Validated domain:

$$
L\le10.
$$

Bound:

$$
\mathcal R\le10^{-5}.
$$

The computed validated-domain maximum is:

$$
2\times10^{-8}.
$$

Finite gate:

`solar_system_residual_bound_demo`

The large residual at \(L=10^5\) is not accepted as a prediction. It is outside
the validated-domain gate and must be handled by a separate residual model.

### 133.2. Activation profile gate

A scale residual candidate must declare its scale profile before comparison.
The finite demo uses:

$$
\mathcal R(L)
=
A\frac{(L/L_t)^n}{1+(L/L_t)^n}.
$$

With:

$$
A=1,
\qquad
L_t=10^4,
\qquad
n=2,
$$

the verifier checks:

$$
\mathcal R(1)=9.9999999\times10^{-9},
$$

$$
\mathcal R(10^4)=0.5,
$$

$$
\mathcal R(10^5)=0.9900990099009901.
$$

Finite gate:

`scale_residual_activation_profile_demo`

This is not a claim that this profile is true. It is a template for future
dark-sector residuals: a residual must declare where it is inactive, where it
turns on, and what it predicts.

### 133.3. No-refit domain gate

Inside the validated domain the same calibration must be used for clock,
dynamics, and lensing:

$$
G_{\mathrm{clock}}
=
G_{\mathrm{dynamics}}
=
G_{\mathrm{lensing}}.
$$

Finite gate:

`validated_domain_no_refit_demo`

The verifier checks:

$$
[6.67430,6.67430,6.67430]\times10^{-11}
$$

against the same reference value with zero fractional mismatch.

### 133.4. Accepted and not accepted

Accepted:

`scale_separated_residual_policy_I = derived_conditional`

Accepted rule:

$$
\mathcal R_{\mathrm{nonGR}}
\text{ may be studied only with an explicit domain and profile.}
$$

Not accepted:

`dark matter explained`.

Not accepted:

`dark energy explained`.

Not accepted:

`GR falsified`.

### 133.5. Why this matters

This cluster protects the theory from two opposite errors:

1. forcing GR to be exact outside its tested domain;
2. using dark-sector language as an unconstrained escape hatch.

The next strong cluster should turn one residual candidate into a real
calculation with units, source dependence, and a falsifiable bound.
