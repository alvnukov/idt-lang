## 142. SPARC Baryonic Acceleration Map

Status:

`baryonic_acceleration_map_near_miss_rejected`

The proportional radius map was rejected. This section tests a more physical
local candidate: the scale should grow as the baryonic acceleration decreases.

### 142.1. Candidate map

Use:

$$
L_I(R)
=
L_{\mathrm{out}}
\left(
\frac{a_{\mathrm{bar,out}}}{a_{\mathrm{bar}}(R)}
\right)^q,
$$

with:

$$
L_{\mathrm{out}}=100000,
\qquad
a_{\mathrm{bar,out}}=44.62895270270271,
\qquad
q=2.
$$

The exponent \(q=2\) is tested as a diagnostic candidate, not as a derived
result.

### 142.2. Profile used

Same SPARC-solar corridor profile:

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

### 142.3. Result

The verifier computes:

$$
\mathrm{RMS}=0.9226475712953834,
$$

$$
\max|\Delta\mathcal R|=1.2041618124170617,
$$

$$
\langle|\Delta\mathcal R|\rangle=0.8163298146002157.
$$

With acceptance threshold:

$$
\max|\Delta\mathcal R|\le1,
$$

the map is:

`rejected`.

This is a near miss, not a success. It strongly improves over \(L_I\propto R\),
but it still overpredicts the inner residuals beyond the declared tolerance.

### 142.4. Inverse-residual map is forbidden

A map can always be made exact by inverting the observed residual:

$$
L_I(R)
=
L_t
\left(
\frac{\mathcal R_{\mathrm{obs}}(R)}
{A-\mathcal R_{\mathrm{obs}}(R)}
\right)^{1/n}.
$$

That is not a derivation. It uses the target residual itself as an input.

The verifier therefore records:

`sparc_inverse_residual_map_forbidden_demo`

with status:

`postfit_contaminated`.

### 142.5. Finite gates

Finite gate:

`sparc_baryonic_acceleration_power_map_demo`

Gate type:

`screened_baryonic_acceleration_map`

It fails if:

1. the predicted \(L_I\) vector is not recomputed from \(a_{\mathrm{bar}}\);
2. the predicted residual vector is not recomputed;
3. RMS, max absolute error, or mean absolute error changes;
4. a rejected near-miss is declared accepted.

Finite gate:

`sparc_inverse_residual_map_forbidden_demo`

Gate type:

`residual_no_postfit_provenance`

It passes only because the inverse-residual map is explicitly declared
postfit-contaminated.

### 142.6. Accepted and not accepted

Accepted:

`sparc_baryonic_acceleration_map_candidate_I = derived_conditional`.

Accepted:

`sparc_acceleration_map_rejection_I = derived_conditional`.

Accepted:

`sparc_inverse_residual_map_forbidden_I = derived_conditional`.

Not accepted:

baryonic acceleration map fitted.

Not accepted:

using \(\mathcal R_{\mathrm{obs}}\) to define \(L_I(R)\).

### 142.7. Next required upgrade

Section 143 follows route 2 in a controlled form: scan a small predeclared
baryonic-acceleration exponent family, while treating any q selected from DDO154
as postfit until held-out validation exists.

The next cluster should decide whether to:

1. derive a nonlocal packet map;
2. freeze the best diagnostic q before held-out validation;
3. abandon local screened maps for DDO154.
