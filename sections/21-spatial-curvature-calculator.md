## 21. Spatial Curvature Calculator

Clock-rate readout gives the temporal weak-field potential.

Light propagation also requires spatial curvature.

This section defines the compressed variable needed to test light bending, Shapiro delay, and gravitational slip.

Status:

`spatial_curvature_calculator_initialized`

### 21.1. Two-potential weak-field readout

Use the weak static readout:

$$
ds_I^2
\approx
c_I^2
\left(1+\frac{2\Phi_I}{c_I^2}\right)dt^2
-
\left(1-\frac{2\Psi_I}{c_I^2}\right)d\ell^2.
$$

Here:

1. \(\Phi_I\) is the clock-rate potential;
2. \(\Psi_I\) is the spatial-curvature potential.

Clock networks primarily infer \(\Phi_I\).

Null propagation and lensing test:

$$
\Phi_I+\Psi_I.
$$

Status:

`two_potential_weak_field_readout`

### 21.2. PPN gamma / slip variable

Define:

$$
\gamma_I^{\mathrm{PPN}}
=
\frac{\Psi_I}{\Phi_I}
$$

where the ratio is used only where \(\Phi_I\neq0\) and signs are fixed by the chosen weak-field convention.

Equivalently define gravitational slip:

$$
\eta_{\mathrm{slip},I}
=
\frac{\Psi_I}{\Phi_I}.
$$

GR no-residual target:

$$
\gamma_I^{\mathrm{PPN}}
\to
1.
$$

Residual:

$$
\mathcal R_\gamma
=
\gamma_I^{\mathrm{PPN}}-1.
$$

Status:

`ppn_gamma_as_spatial_curvature_compression`

### 21.3. Light bending gate

For impact parameter \(b\), weak-field deflection has form:

$$
\Delta\theta_I
=
(1+\gamma_I^{\mathrm{PPN}})
\frac{2G_I M}{c_I^2 b}.
$$

GR target:

$$
\gamma_I^{\mathrm{PPN}}=1
\Rightarrow
\Delta\theta_I
=
\frac{4G_I M}{c_I^2 b}.
$$

Clock redshift alone fixes only the temporal half.

The spatial-curvature calculator supplies the missing \(\gamma_I^{\mathrm{PPN}}\) gate.

Status:

`light_bending_gamma_gate`

### 21.4. Shapiro delay gate

The same spatial factor enters radar time delay.

Weak-field Shapiro delay scales as:

$$
\Delta t_{\mathrm{Shapiro},I}
\propto
(1+\gamma_I^{\mathrm{PPN}})
\frac{G_I M}{c_I^3}.
$$

Thus:

$$
\gamma_I^{\mathrm{PPN}}
$$

must be shared by light bending, Shapiro delay, and lensing.

No separate \(\gamma\) fit is allowed per gate.

Status:

`shapiro_gamma_closure_gate`

### 21.5. Lensing / dynamical residual split

Dynamical acceleration reads:

$$
a_I
=
-\nabla\Phi_I.
$$

Lensing reads approximately:

$$
\Phi_{\mathrm{lens},I}
=
\frac{\Phi_I+\Psi_I}{2}.
$$

Therefore a mismatch between dynamics and lensing is:

$$
\mathcal R_{\mathrm{slip}}
=
\Psi_I-\Phi_I.
$$

Possible interpretations:

1. spatial-curvature residual;
2. missing source sector;
3. dark-sector effective stress;
4. invalid weak-field domain;
5. systematic lensing/dynamical modelling error.

Status:

`lensing_dynamics_slip_residual`

### 21.6. Spatial-curvature packet

Define compressed packet:

$$
\mathcal G_I
=
\left(
\Phi_I,
\Psi_I,
\gamma_I^{\mathrm{PPN}},
\mathcal R_\gamma,
\mathcal R_{\mathrm{slip}}
\right).
$$

Input sources:

1. clock network \(\Rightarrow\Phi_I\);
2. free fall / dynamics \(\Rightarrow\nabla\Phi_I\);
3. light bending / Shapiro / lensing \(\Rightarrow\Phi_I+\Psi_I\).

The calculator solves for:

$$
\Psi_I
$$

only after \(\Phi_I\) is fixed by clock/dynamical gates.

Status:

`spatial_curvature_packet_defined`

### 21.7. Acceptance gates

The spatial-curvature calculator must pass:

| Gate | Required |
|---|---|
| redshift | fixed by \(\Phi_I\) |
| slow free fall | fixed by \(\nabla\Phi_I\) |
| light bending | one \(\gamma_I^{\mathrm{PPN}}\) |
| Shapiro delay | same \(\gamma_I^{\mathrm{PPN}}\) |
| lensing | same \(\Phi_I+\Psi_I\) |
| perihelion | compatible \(\beta_I,\gamma_I\) in PPN sector |

If:

$$
\gamma_I^{\mathrm{PPN}}\neq1,
$$

the deviation must be declared before using it as a dark-sector or modified-gravity residual.

Status:

`spatial_curvature_acceptance_gates`

### 21.8. What v5.22 closes

This section closes the computational gap left by the clock calculator:

$$
\Phi_I
\nRightarrow
\text{full weak-field light propagation}.
$$

It introduces:

$$
\Psi_I
$$

as the compressed spatial-curvature partner of \(\Phi_I\).

It does not yet derive:

1. why \(\Psi_I=\Phi_I\) in the no-residual sector;
2. full Einstein equations;
3. strong-field behavior;
4. cosmological perturbation dynamics.

Next target:

derive the condition:

$$
\Psi_I
\to
\Phi_I
$$

from inherited source conservation / isotropic stress / fixed-point consistency.

Status:

`spatial_curvature_compressed_variable_defined`

No-slip support conditions:

`sections/22-no-slip-closure-front.md`
