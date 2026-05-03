## 24. Volume Reconstruction Bridge

Source density must not import geometry circularly.

This section separates primitive counting from reconstructed geometric volume.

Status:

`volume_reconstruction_bridge_initialized`

### 24.1. Two volume notions

Primitive counting volume:

$$
\nu_{\mathrm{count}}(U)
=
\#\{\text{primitive/coarse events in }U\}.
$$

Geometric volume of dimension \(d\):

$$
\nu_G^{(d)}(U)
$$

is not primitive.

It is reconstructed after causal/order, clock, and local dimension gates are satisfied.

Forbidden circular chain:

$$
\rho_I
\Rightarrow
\text{geometry}
\Rightarrow
\nu_G^{(d)}
\Rightarrow
\rho_I.
$$

Allowed chain:

$$
(\bar E,\le_I,\nu_{\mathrm{count}},\tau_I)
\Rightarrow
D_G
\Rightarrow
\{\nu_G^{(4)},\nu_{G,S}\}
\Rightarrow
\rho_I^G.
$$

Status:

`counting_volume_separated_from_geometric_volume`

### 24.2. Order-volume calibration

In a locally flat readout domain, event counts should scale as:

$$
\nu_{\mathrm{count}}(U)
\approx
\lambda_I
\nu_G^{(d)}(U)
$$

where:

$$
\lambda_I
$$

is primitive event density per geometric volume.

If \(\lambda_I\) is constant in a validated domain, then:

$$
\nu_G^{(d)}(U)
\approx
\frac{\nu_{\mathrm{count}}(U)}{\lambda_I}.
$$

If \(\lambda_I\) varies, the variation is a volume residual:

$$
\mathcal R_\nu(U).
$$

Status:

`order_volume_calibration_gate`

### 24.3. Dimension gate

For small balls in reconstructed spatial readout:

$$
\nu_{\mathrm{count}}(B_R)
\propto
R^{D_S}.
$$

The observed weak-field spatial target is:

$$
D_S\to3.
$$

Spacetime causal diamond counting gives:

$$
\nu_{\mathrm{count}}(\Diamond_\tau)
\propto
\tau^{D_G}.
$$

The validated macroscopic target is:

$$
D_G\to4.
$$

Status:

`dimension_from_count_scaling_gate`

### 24.4. Local metric volume

Once the local interval tensor is reconstructed:

$$
G_{\mu\nu}(E),
$$

geometric spacetime volume reads:

$$
d\nu_G^{(4)}
=
\sqrt{|\det G_{\mu\nu}|}\,d^4x.
$$

Spatial volume on a clock slice \(S\):

$$
d\nu_{G,S}
=
\sqrt{\det h_{ij}}\,d^3x.
$$

These are readout volumes, not primitives.

Bare \(\nu_G\) is allowed only when the dimension is explicitly fixed by context.
Source laws must use \(\nu_{G,S}\) for spatial density or \(\nu_G^{(4)}\) for spacetime density.

Status:

`metric_volume_after_interval_reconstruction`

### 24.5. Source density after volume reconstruction

Only after \(\nu_{G,S}\) is available define spatial source density:

$$
\rho_I^G(U)
=
\frac{1}{\nu_{G,S}(U)}
\sum_{\eta\in U}m_I(\eta).
$$

Similarly:

$$
J_I^{G,i}(U)
=
\frac{1}{\nu_{G,S}(U)}
\sum_{\eta\in U}m_I(\eta)v_I^i(\eta).
$$

The superscript \(G\) marks geometric-volume density.

Counting-density alternative:

$$
\rho_I^{\mathrm{count}}(U)
=
\frac{1}{\nu_{\mathrm{count}}(U)}
\sum_{\eta\in U}m_I(\eta).
$$

The two are related only after \(\lambda_I\) is known.

\(\mathcal N_I(U)\) denotes uncalibrated inherited activity count/weight.
\(\sum m_I(\eta)\) denotes the source-weighted moment used by the geometric field readout.

Status:

`source_density_requires_reconstructed_volume`

### 24.6. Residual gates

Volume reconstruction residuals:

$$
\mathcal R_\nu(U)
=
\nu_{\mathrm{count}}(U)
-
\lambda_I\nu_G^{(d)}(U).
$$

Dimension residual:

$$
\mathcal R_D
=
D_G-4.
$$

Metric-volume residual:

$$
\mathcal R_{\det G}
=
d\nu_G^{(4)}-\sqrt{|\det G|}d^4x.
$$

Each residual must be tied to:

1. clock network consistency;
2. causal diamond scaling;
3. lensing / distance measures;
4. source-density gates.

Status:

`volume_reconstruction_residuals_declared`

### 24.7. What v5.25 closes

This section closes the volume-density circularity.

It replaces:

$$
\rho_I=\mathcal N_I/\nu
$$

with:

$$
\rho_I^G
=
\frac{\sum m_I}{\nu_G}
$$

where:

$$
\nu_G
$$

is reconstructed from order/count/clock/interval gates before source density is used as geometry source.

It does not yet derive:

1. primitive event density \(\lambda_I\);
2. exact \(D_G=4\);
3. local Lorentzian signature;
4. microscopic link stiffness \(a_{EF}\) and matter calibration.

Next target:

derive the remaining calibration constants after reducing \(m_I(\eta)\) to source response charge.

Source-weight bridge:

`sections/25-source-weight-bridge.md`

Vacuum stiffness bridge:

`sections/26-vacuum-stiffness-bridge.md`

Event-density calibration:

`sections/31-event-density-calibration.md`

Status:

`volume_density_circularity_reduced`
