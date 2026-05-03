## 135. Screened Slip Observational Gate

Status:

`first_observational_gate_for_residual_candidate`

This section turns the screened slip candidate into a pass/fail observational
gate. It does not validate the candidate as a physical explanation. It checks
whether one declared profile can simultaneously:

1. stay under the validated solar-system residual bound;
2. produce a non-negligible galactic-scale residual prediction;
3. do both without changing \(G_N\), \(\gamma\), or the source calibration.

The checked target is:

$$
\texttt{screened\_slip\_observational\_gate\_I}.
$$

It depends on:

$$
\texttt{screened\_slip\_residual\_candidate\_I},
\quad
\texttt{validated\_weak\_field\_domain\_I},
\quad
\texttt{galactic\_residual\_test\_I}.
$$

### 135.1. One-profile rule

Use the same screened profile:

$$
\mathcal R(L)
=
A
\frac{(L/L_t)^n}{1+(L/L_t)^n}.
$$

The observational gate forbids changing \(A,L_t,n\) between domains.

### 135.2. Solar bound

Declared values:

$$
A=1,
\qquad
L_t=3162.26184874055,
\qquad
n=2,
\qquad
L_\odot=10.
$$

The verifier computes:

$$
\mathcal R(L_\odot)=10^{-5}.
$$

Accepted solar bound:

$$
\mathcal R(L_\odot)\le10^{-5}.
$$

This is deliberately saturated in the demo. A real gate should use a
source-cited bound and then either pass or reject the candidate.

### 135.3. Galactic prediction

For the same profile:

$$
L_g=10^5.
$$

The verifier computes:

$$
\mathcal R(L_g)=0.9990010089810291.
$$

The demo acceptance window is:

$$
0.1\le\mathcal R(L_g)\le1.0.
$$

This is not yet a galaxy rotation-curve fit. It is a coarse observational
survival test: the candidate is not automatically killed by the solar bound
while still producing a large galactic-scale residual. Section 136 adds the
first real SPARC rotation-curve data point that this front must eventually
explain without refitting the screened profile after inspection.

### 135.4. Finite gate

Finite gate:

`screened_solar_galactic_observation_demo`

The gate fails if:

1. the solar residual exceeds its bound;
2. the solar residual is not the declared computed value;
3. the galactic residual is not the declared computed value;
4. the galactic residual falls outside the declared observational window.

### 135.5. Accepted and not accepted

Accepted:

`screened_slip_observational_gate_I = derived_conditional`

Accepted:

one declared screened residual profile passes one coarse solar/galactic
survival gate.

Not accepted:

`screened_slip_residual_candidate_I = observed`.

Not accepted:

`dark matter explained`.

Not accepted:

the chosen numbers as physical constants.

### 135.6. Next required upgrade

Section 136 starts this upgrade with one real SPARC data point. The remaining
work is to replace the demo galactic window by a pre-registered multi-point
data comparison:

1. choose a galaxy or a normalized rotation-curve dataset;
2. compute predicted residual acceleration from the same \(A,L_t,n\);
3. compare to observed \(v^2/r-a_N\);
4. reject if the same profile fails.

Only after that can the residual candidate become empirically meaningful.
