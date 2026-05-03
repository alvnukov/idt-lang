## 155. Calibrated G Anchor Protocol

Status:

`calibrated_G_anchor_protocol_initialized`

This section accepts the user's decision:

calibrate on \(G\).

This is allowed only as a declared second anchor.

It is not a derivation of \(G\), and this branch will not try to derive \(G\).

### 155.1. New branch status

The branch now has two dimensional calibration anchors:

1. `calibrated_hbar_I`;
2. `calibrated_G_anchor_I`.

Therefore the programme status becomes:

`two_anchor_calibrated_reconstruction`.

The following claims remain forbidden:

1. `G_I = derived`;
2. `omega_ell_I = derived`;
3. `hbar_I = derived`;
4. "one-anchor prediction of gravity".

The target is changed from:

`derive_G`

to:

`use_G_as_calibration_anchor`.

Status:

`two_anchor_status_declared`

### 155.2. What the G anchor can calibrate

Start from the calibrated clock-vacuum calculator:

\[
calibrated\_G_I
=
\frac{
\rho_{\chi,I}D_Sc_I^5
}{
2\pi\,calibrated\_hbar_I\,z_Iq_{V,I}\omega_{\ell,I}^2
}.
\]

Set:

\[
calibrated\_G\_anchor_I := G_N.
\]

Then the \(G\)-calibrated link-frequency square is:

\[
\Omega_{Gcal,I}^2
=
\frac{
\rho_{\chi,I}D_Sc_I^5
}{
2\pi\,calibrated\_hbar_I\,z_Iq_{V,I}calibrated\_G\_anchor_I
}.
\]

and:

\[
\Omega_{Gcal,I}>0.
\]

This calibrates a target frequency scale for later non-gravity checks.

It does not prove that the primitive clock-vacuum pole has this value.

Status:

`G_anchor_calibrates_link_frequency_target`

### 155.3. Geometry/readout freeze condition

The formula above separates \(\Omega_{Gcal,I}\) only if the dimensionless
readout factors are frozen before the \(G\)-anchor is applied:

1. \(\rho_{\chi,I}\);
2. \(D_S\);
3. \(z_I\);
4. \(q_{V,I}\).

If any of these remain adjustable, the \(G\)-anchor calibrates only the
composite:

\[
\frac{\rho_{\chi,I}D_S}
{z_Iq_{V,I}\omega_{\ell,I}^2}.
\]

In that case the status is:

`G_anchor_composite_only`.

No separate \(\omega_{\ell,I}\) may be quoted.

Status:

`G_anchor_requires_geometry_readout_freeze`

### 155.4. Minimal orthogonal reconstruction

If the minimal orthogonal sector is frozen before comparison:

\[
D_S=3,
\qquad
z_I=6,
\qquad
q_{V,I}=1,
\]

then:

\[
\Omega_{Gcal,I}^{orth}
=
\left(
\frac{
\rho_{\chi,I}c_I^5
}{
4\pi\,calibrated\_hbar_I\,calibrated\_G\_anchor_I
}
\right)^{1/2}.
\]

If additionally:

\[
\rho_{\chi,I}=1,
\]

then this becomes the minimal two-anchor link-frequency scale.

This is a calibrated target, not a prediction.

Status:

`minimal_orthogonal_G_anchor_reconstruction_defined`

### 155.5. Holdout tests

After \(\Omega_{Gcal,I}\) is fixed, it must be used only as a frozen anchor in
holdout tests:

1. compare against non-gravity lower bounds;
2. compare against photon dispersion residual gates;
3. compare against matter-wave residual gates;
4. compare against any future clock-vacuum spectral law
   \(\mathcal S_{\chi,I}\);
5. reject or mark residuals if the same scale fails.

Forbidden after calibration:

1. change \(\rho_{\chi,I}\), \(D_S\), \(z_I\), or \(q_{V,I}\);
2. change the spectral law to reproduce \(\Omega_{Gcal,I}\);
3. call holdout agreement a derivation of \(G\);
4. hide the \(G\)-anchor inside a claimed primitive pole.

Status:

`G_anchor_holdout_protocol_defined`

### 155.6. Current verdict

The \(G\)-calibrated route is useful because it gives a concrete target for the
next spectral work:

\[
\mathcal S_{\chi,I}
\Rightarrow
\omega_{\ell,I}
\stackrel{?}{=}
\Omega_{Gcal,I}.
\]

But the physical status is not a derivation:

`two_anchor_calibrated_reconstruction`.

From this point in the calibrated branch, \(G\) is an input anchor. The next
nontrivial question is whether the rest of the theory can reproduce independent
non-gravity structure after that anchor is frozen.

Status:

`G_calibration_accepted_without_derivation_claim`
