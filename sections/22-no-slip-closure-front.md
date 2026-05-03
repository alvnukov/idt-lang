## 22. No-Slip Closure Front

The spatial-curvature calculator introduced \(\Psi_I\).

The next hard problem is to explain why the no-residual weak-field sector should satisfy:

$$
\Psi_I
\to
\Phi_I.
$$

This section gives support conditions for that target.

It does not derive the full Einstein equations.

Status:

`no_slip_closure_front_initialized`

### 22.1. Slip residual

Define:

$$
\mathcal R_{\mathrm{slip}}
=
\Psi_I-\Phi_I.
$$

Equivalently:

$$
\gamma_I^{\mathrm{PPN}}-1
=
\frac{\Psi_I-\Phi_I}{\Phi_I}.
$$

No-slip target:

$$
\mathcal R_{\mathrm{slip}}
\to
0.
$$

Known gate:

light bending, Shapiro delay, and lensing require \(\gamma_I^{\mathrm{PPN}}\) close to \(1\) in the tested weak-field domain.

Status:

`slip_residual_defined`

### 22.2. Source decomposition

The weak source readout must distinguish:

1. scalar density source;
2. momentum flow;
3. pressure / stress;
4. anisotropic stress.

Write compressed source packet:

$$
\mathcal T_I
=
\left(
\rho_I,
J_I^i,
P_I,
\Pi_I^{ij}
\right).
$$

Here:

$$
\Pi_I^{ij}
$$

is the traceless anisotropic stress readout.

The no-slip weak-field condition is expected only when:

$$
\Pi_I^{ij}
\to
0
$$

and source coupling is universal.

Status:

`source_stress_packet_defined`

### 22.3. Slip source law

The compressed target relation is:

$$
\Delta_S(\Psi_I-\Phi_I)
=
\mathcal C_{\Pi,I}[\Pi_I]
+
\mathcal R_{\mathrm{nonGR}}.
$$

No-slip sector:

$$
\Pi_I^{ij}=0,
\qquad
\mathcal R_{\mathrm{nonGR}}=0
\Rightarrow
\Psi_I=\Phi_I
$$

up to boundary conditions.

This mirrors the known weak-field result that gravitational slip is sourced by anisotropic stress or modified gravity residuals.

Status:

`slip_sourced_by_anisotropic_stress_target`

### 22.4. Conservation gate

Universal source coupling requires a conservation law:

$$
\nabla_\mu T_I^{\mu\nu}=0
$$

or in weak readout:

$$
\partial_t\rho_I+\partial_iJ_I^i=0.
$$

If source conservation fails, then:

$$
\Phi_I,\Psi_I
$$

cannot form a stable weak-field geometry readout.

Known gate:

energy-momentum conservation is required in the validated GR domain.

Status:

`source_conservation_for_geometry_readout`

### 22.5. Universal coupling gate

The same source packet must determine:

1. clock redshift;
2. slow free fall;
3. lensing;
4. Shapiro delay;
5. perihelion correction.

No-refit condition:

$$
G_I^{\mathrm{clock}}
=
G_I^{\mathrm{dynamics}}
=
G_I^{\mathrm{lensing}}
$$

within domain uncertainty.

If different \(G_I\) values are needed, the model has a coupling residual, not a closed weak-field geometry sector.

Status:

`universal_gravity_coupling_gate`

### 22.6. Boundary condition

The equality:

$$
\Delta_S(\Psi_I-\Phi_I)=0
$$

does not by itself imply:

$$
\Psi_I=\Phi_I.
$$

Need boundary condition:

$$
\Psi_I-\Phi_I
\to
0
$$

in the flat calibration domain.

Then:

$$
\Psi_I-\Phi_I=0
$$

in the connected no-slip weak-field domain.

Status:

`flat_boundary_condition_for_no_slip`

### 22.7. Acceptance gates

No-slip closure is accepted only if:

| Gate | Required |
|---|---|
| redshift | \(\Phi_I\) from clocks |
| dynamics | \(a=-\nabla\Phi_I\) |
| lensing | uses \(\Phi_I+\Psi_I\) |
| light bending | \(\gamma_I^{\mathrm{PPN}}\to1\) |
| Shapiro | same \(\gamma_I^{\mathrm{PPN}}\) |
| source stress | \(\Pi_I^{ij}\) bounded or declared |
| boundary | \(\Psi_I-\Phi_I\to0\) in flat domain |

Status:

`no_slip_acceptance_gates`

### 22.8. What v5.23 closes

This section does not prove:

$$
\Psi_I=\Phi_I
$$

from first principles.

It reduces the target to:

$$
\Pi_I^{ij}=0
+
\text{universal coupling}
+
\text{source conservation}
+
\text{flat boundary}
\Rightarrow
\Psi_I\to\Phi_I.
$$

The next true derivation target is:

$$
\text{primitive inheritance}
\Rightarrow
\mathcal T_I
\Rightarrow
\Pi_I^{ij}
$$

and the slip source law.

Status:

`no_slip_gap_reduced_to_source_stress_conditions`

Source-stress packet definition:

`sections/23-source-stress-packet.md`
