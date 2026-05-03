## 139. SPARC-Solar Compatibility Cluster

Status:

`amplitude_bound_plus_solar_screening_obstruction`

This cluster combines two already accepted gates:

1. DDO154 requires a large-scale residual amplitude at least
   \(A_{\min}=6.842377551859201\), if the screened profile is interpreted as
   the full missing acceleration fraction.
2. The validated solar-domain residual bound requires
   \(\mathcal R(L_\odot)\le10^{-5}\) at \(L_\odot=10\).

The combined result is stronger than either gate alone.

### 139.1. Transition lower bound

For:

$$
\mathcal R(L)
=
A
\frac{(L/L_t)^n}{1+(L/L_t)^n},
$$

the solar bound:

$$
\mathcal R(L_\odot)\le B
$$

requires:

$$
L_t
\ge
L_\odot
\left(
\frac{A}{B}-1
\right)^{1/n}.
$$

Using:

$$
A=6.842377551859201,
\qquad
B=10^{-5},
\qquad
L_\odot=10,
\qquad
n=2,
$$

the verifier computes:

$$
L_t^{\min}=8271.860462954632.
$$

### 139.2. Old profile rejection

The old demo profile used:

$$
A=1,
\qquad
L_t=3162.26184874055.
$$

If the amplitude is raised to the SPARC lower bound while keeping the old
transition scale, the solar residual becomes:

$$
\mathcal R(L_\odot)
=
6.842377551859202\times10^{-5}.
$$

This exceeds the solar bound by:

$$
6.842377551859201.
$$

So the old transition scale is excluded for the SPARC-minimum amplitude.

### 139.3. Finite gates

Finite gate:

`sparc_amplitude_solar_transition_bound_demo`

Gate type:

`screened_transition_bound`

It recomputes the required \(L_t^{\min}\) from the SPARC amplitude lower bound
and the solar residual bound.

Finite gate:

`old_screened_profile_solar_rejection_demo`

Gate type:

`screened_profile_bound_status`

It passes only because the old profile is explicitly declared:

`excluded`

for the SPARC-minimum amplitude.

### 139.4. Accepted and not accepted

Accepted:

`sparc_solar_transition_bound_I = derived_conditional`.

Accepted:

`old_screened_profile_rejection_I = derived_conditional`.

Accepted:

if \(\mathcal R\) is the full acceleration residual, then SPARC plus solar
requires:

$$
A\ge6.842377551859201,
\qquad
L_t\ge8271.860462954632.
$$

Not accepted:

the old \(A=1,L_t=3162.26184874055\) toy profile as a galaxy explanation.

Not accepted:

raising \(A\) without also rechecking the validated-domain suppression.

### 139.5. Next required upgrade

The next cluster should derive one of:

1. a pre-SPARC amplitude source satisfying the lower bound;
2. a pre-SPARC transition-scale source satisfying the solar bound;
3. a map-to-residual rule showing why the full-residual interpretation is
   wrong.

Section 140 checks that the corridor is nonempty while still refusing a fit
claim until a radius-to-scale map and held-out validation exist. If none of
these can be derived, the screened residual route must be rejected as a galaxy
explanation.
