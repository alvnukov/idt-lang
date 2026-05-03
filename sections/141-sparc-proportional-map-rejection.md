## 141. SPARC Proportional Map Rejection

Status:

`first_radius_scale_map_candidate_rejected`

Section 140 showed that the SPARC-solar corridor is nonempty but not a fit
because no \(R\mapsto L_I(R)\) map had been derived. This section tests the
simplest explicit map candidate as a falsification baseline.

### 141.1. Candidate map

Use a proportional map anchored at the outer DDO154 radius:

$$
L_I(R)=\alpha_R R,
$$

with:

$$
R_{\max}=5.92\ \mathrm{kpc},
\qquad
L_I(R_{\max})=100000.
$$

Therefore:

$$
\alpha_R=16891.891891891893.
$$

This is not claimed as derived. It is a simple probe.

### 141.2. Profile used

Use the minimal SPARC-solar corridor profile:

$$
A=6.842377551859201,
\qquad
L_t=8271.860462954632,
\qquad
n=2.
$$

Predicted residual:

$$
\mathcal R_{\mathrm{pred}}(R)
=
A
\frac{(L_I(R)/L_t)^2}{1+(L_I(R)/L_t)^2}.
$$

### 141.3. Result

Against the full DDO154 residual vector, the verifier computes:

$$
\mathrm{RMS}=2.043579601832694,
$$

$$
\max|\Delta\mathcal R|=3.6084805124311896,
$$

$$
\langle|\Delta\mathcal R|\rangle=1.7132317672748618.
$$

With acceptance threshold:

$$
\max|\Delta\mathcal R|\le1,
$$

the candidate status is:

`rejected`.

The failure is not subtle. The proportional map overpredicts the inner
residuals while roughly approaching the outer residuals.

### 141.4. Finite gate

Finite gate:

`sparc_proportional_radius_map_rejection_demo`

Gate type:

`screened_radius_scale_prediction`

It fails if:

1. the map factor is not recomputed;
2. the predicted 12-point residual vector is not recomputed;
3. RMS, max absolute error, or mean absolute error changes;
4. a rejected map is declared accepted.

### 141.5. Accepted and not accepted

Accepted:

`sparc_radius_scale_map_candidate_I = derived_conditional`.

Accepted:

`sparc_simple_map_rejection_I = derived_conditional`.

Accepted:

the proportional \(R\mapsto L_I\) map is rejected for DDO154 under the current
corridor profile.

Not accepted:

proportional radius map fitted.

Not accepted:

screened residual route rejected entirely.

### 141.6. Next required upgrade

The next cluster should test a physically motivated non-proportional map:

1. acceleration-scale map \(L_I\sim a_0/a_{\mathrm{bar}}\) or similar;
2. source-density map using gas+stellar baryonic profile;
3. packet/nonlocal map instead of radius-local map.

Each candidate must be declared before computing the vector error.

Section 142 tests the baryonic-acceleration route and rejects it as a near
miss under the declared error threshold.
