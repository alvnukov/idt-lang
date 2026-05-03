## 152. Calibrated G Calculator Path

Status:

`calibrated_G_path_initialized`

This section lays out the path to a \(G\) calculation after accepting one
calibrated action anchor.

It does not claim:

`G_I = derived`.

It defines a separate target:

`calibrated_G_I`.

### 152.1. Starting point

From the kappa-omega consistency gate:

\[
\kappa_{\chi,I}
=
\frac{\hbar_I\omega_{\ell,I}}{\rho_{\chi,I}}.
\]

With the calibrated branch, replace only the action scale:

\[
\hbar_I
\mapsto
calibrated\_hbar_I.
\]

Then:

\[
\kappa_{\chi,I}^{cal}
=
\frac{calibrated\_hbar_I\,\omega_{\ell,I}}
{\rho_{\chi,I}}.
\]

Substitute into the weak-gravity expression:

\[
G
=
\frac{c_I^4D_S\ell_{0,*}}
{2\pi\kappa_{\chi,I}z_Iq_{V,I}},
\qquad
\ell_{0,*}=\frac{c_I}{\omega_{\ell,I}}.
\]

The calibrated calculator is:

\[
calibrated\_G_I
=
\frac{
\rho_{\chi,I}D_Sc_I^5
}{
2\pi\,calibrated\_hbar_I\,z_Iq_{V,I}\omega_{\ell,I}^2
}.
\]

In the radar-orthogonal minimal sector:

\[
D_S=3,\quad z_I=6,\quad q_{V,I}=1,
\]

so:

\[
calibrated\_G_I^{orth}
=
\frac{
\rho_{\chi,I}c_I^5
}{
4\pi\,calibrated\_hbar_I\,\omega_{\ell,I}^2
}.
\]

### 152.2. What must still be derived

After one \(\hbar\)-calibration, \(G\) is computable only if the remaining
inputs are fixed without \(G_N\):

1. `omega_ell_I`: link frequency from update spectrum or clock-vacuum pole;
2. `rho_chi_I`: sampling / curvature protocol invariant;
3. `D_S`: stable spatial dimension;
4. `z_I`: stable adjacency degree;
5. `q_V_I`: cell-volume shape factor.

The hard input is:

`omega_ell_I`.

The current non-gravity rows only give weak lower bounds, not a value.

### 152.3. No-fit rule

Forbidden:

1. infer `omega_ell_I` from \(G_N\);
2. set \(z_I\), \(q_V_I\), \(D_S\), or \(\rho_{\chi,I}\) by demanding
   \(calibrated\_G_I=G_N\);
3. use Planck length or Planck frequency as an input;
4. call `calibrated_G_I` a primitive derivation.

Allowed:

1. derive `omega_ell_I` from a primitive update spectrum;
2. derive `omega_ell_I` from a clock-vacuum response pole;
3. use \(G_N\) only as a final experimental gate;
4. record a residual if the calculated value fails.

### 152.4. Computation protocol

The first real \(G\) computation must follow this order:

1. freeze `calibrated_hbar_I` from the action-anchor protocol;
2. choose minimal or non-minimal geometry sector before seeing \(G_N\);
3. derive or externally predeclare `omega_ell_I` without gravitational data;
4. derive `rho_chi_I`, `D_S`, `z_I`, and `q_V_I`;
5. compute `calibrated_G_I`;
6. compare to \(G_N\);
7. do not retune failed inputs.

The dimensionless comparison gate is:

\[
\Pi_G^{cal}
=
\frac{
calibrated\_G_I
}{
G_N
}
\]

or equivalently:

\[
\Pi_G^{cal}
=
\frac{
\rho_{\chi,I}D_Sc_I^5
}{
2\pi\,calibrated\_hbar_I\,z_Iq_{V,I}\omega_{\ell,I}^2G_N
}.
\]

Success requires:

\[
|\Pi_G^{cal}-1|\le\epsilon_G
\]

with \(\epsilon_G\) fixed before comparison.

### 152.5. Current status

Accepted:

`calibrated_G_I = target`.

Accepted:

`calibrated_G_calculator_I = target`.

Not accepted:

`G_I = derived`.

Not accepted:

`omega_ell_I = derived`.

The next decisive task is therefore not more algebra. It is to derive
`omega_ell_I` from either:

1. primitive update spectrum;
2. clock-vacuum response pole.
