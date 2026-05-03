## 134. Screened Slip Residual Candidate

Status:

`executable_residual_candidate_not_validated`

This section defines the first concrete non-GR residual candidate. It is not a
claim that dark matter or dark energy has been explained. It is a falsifiable
candidate profile that must stay suppressed in the validated weak-field domain
and declare its observable outputs.

The checked target is:

$$
\texttt{screened\_slip\_residual\_candidate\_I}.
$$

It depends on:

$$
\texttt{residual\_amplitude\_I},
\quad
\texttt{residual\_transition\_length\_I},
\quad
\texttt{non\_gravity\_slip\_residual\_I},
\quad
\texttt{dark\_sector\_residual\_candidate\_I}.
$$

### 134.1. Candidate profile

Use a screened residual:

$$
\mathcal R_L
=
A
\frac{(L/L_t)^n}{1+(L/L_t)^n}.
$$

Here:

* \(A\) is the large-scale amplitude;
* \(L_t\) is the transition scale;
* \(n\) is the activation exponent.

This profile is only a candidate. It becomes physically meaningful only after
\(A,L_t,n\) are derived or independently constrained.

### 134.2. Solar-domain suppression

Given a validated-domain bound:

$$
\mathcal R(L_s)\le B,
$$

the profile requires:

$$
L_t
\ge
L_s
\left(
\frac{A}{B}-1
\right)^{1/n}.
$$

Verifier sample:

$$
A=1,
\qquad
B=10^{-5},
\qquad
L_s=10,
\qquad
n=2.
$$

The verifier recomputes:

$$
L_t^{\min}=3162.26184874055.
$$

Finite gate:

`screened_transition_bound_demo`

### 134.3. Profile prediction

With:

$$
L_t=3162.26184874055,
\qquad
A=1,
\qquad
n=2,
$$

the verifier recomputes:

$$
\mathcal R(1)
=
1.0000099000980111\times10^{-7},
$$

$$
\mathcal R(10)
=
10^{-5},
$$

$$
\mathcal R(10^5)
=
0.9990010089810291.
$$

Finite gate:

`screened_profile_prediction_demo`

This intentionally shows the risk: a candidate can be invisible in the
validated domain and large outside it. That is allowed only if the external
domain is separately tested.

### 134.4. Acceleration output

The candidate produces an acceleration residual:

$$
a_{\mathrm{tot}}
=
a_N(1+\mathcal R),
\qquad
a_{\mathrm{res}}
=
\mathcal R a_N.
$$

For Earth parameters and \(\mathcal R=2\times10^{-8}\), the verifier computes:

$$
a_N=9.820302293385645,
$$

$$
a_{\mathrm{res}}
=
1.9640604586771288\times10^{-7},
$$

$$
a_{\mathrm{tot}}
=
9.820302489791692.
$$

Finite gate:

`screened_acceleration_output_demo`

### 134.5. Light-bending output

If the same residual enters:

$$
\gamma_I^{\mathrm{PPN}}=1+\mathcal R,
$$

then weak light bending changes by:

$$
\Delta\theta
=
\Delta\theta_{\mathrm{GR}}
\left(1+\frac{\mathcal R}{2}\right).
$$

For:

$$
\Delta\theta_{\mathrm{GR}}
=
8.490267017584816\times10^{-6},
\qquad
\mathcal R=2\times10^{-8},
$$

the verifier computes:

$$
\Delta\theta
=
8.490267102487485\times10^{-6}.
$$

Finite gate:

`screened_light_bending_output_demo`

### 134.6. Accepted and not accepted

Accepted:

`screened_slip_residual_candidate_I = derived_conditional`

Accepted:

the candidate has explicit scale profile, transition bound, acceleration
output, and light-bending output.

Not accepted:

`screened_slip_residual_candidate_I = observed`.

Not accepted:

`dark matter explained`.

Not accepted:

`dark energy explained`.

### 134.7. Next hard step

The candidate must now be constrained or rejected by a real data gate:

1. choose one domain: galaxy rotation, lensing, or clock/redshift residuals;
2. pre-register \(A,L_t,n\) or derive them from primitive dynamics;
3. compare without changing \(G_N\), \(\gamma\), or source calibration inside
   the validated solar-system domain.
