## 23. Source-Stress Packet

This section begins deriving the source packet needed for no-slip closure.

The target is:

$$
\text{primitive inheritance activity}
\Rightarrow
\mathcal T_I
=
(\rho_I,J_I^i,P_I,\Pi_I^{ij}).
$$

Status:

`source_stress_packet_derivation_initialized`

### 23.1. Local inherited activity distribution

Let a coarse-grained readout cell \(U\) contain inherited update activity:

$$
\mathcal N_I(U).
$$

Let each update carry:

1. scalar activity weight \(m_I(\eta)\), reduced in section 25 to clock-strain response charge;
2. local readout velocity \(v_I^i(\eta)\);
3. internal stress contribution \(s_I^{ij}(\eta)\).

Define coarse-grained density:

$$
\rho_I(U)
=
\frac{1}{\nu_{G,S}(U)}
\sum_{\eta\in U}
m_I(\eta).
$$

This uses reconstructed spatial geometric volume \(\nu_{G,S}\), not primitive counting volume.

Primitive counting remains:

$$
\nu_{\mathrm{count}}(U).
$$

Status:

`density_as_activity_moment`

### 23.2. Momentum flow

Define inherited momentum/current density:

$$
J_I^i(U)
=
\frac{1}{\nu_{G,S}(U)}
\sum_{\eta\in U}
m_I(\eta)v_I^i(\eta).
$$

In continuum readout:

$$
J_I^i
=
\rho_I u_I^i.
$$

This is the source-current part of the weak geometry packet.

Status:

`momentum_flow_as_activity_moment`

### 23.3. Stress tensor split

Define spatial stress:

$$
S_I^{ij}(U)
=
\frac{1}{\nu_{G,S}(U)}
\sum_{\eta\in U}
\left[
m_I(\eta)v_I^i(\eta)v_I^j(\eta)
+
s_I^{ij}(\eta)
\right].
$$

Split:

$$
P_I
=
\frac{1}{3}
\delta_{ij}S_I^{ij},
$$

and:

$$
\Pi_I^{ij}
=
S_I^{ij}
-
P_I\delta^{ij}.
$$

Then:

$$
\delta_{ij}\Pi_I^{ij}=0.
$$

No-slip target requires:

$$
\Pi_I^{ij}
\to
0
$$

in the isotropic weak-field domain.

Status:

`stress_split_into_pressure_and_anisotropic_part`

### 23.4. Conservation from update balance

For a readout region \(U\), inherited activity balance is:

$$
\frac{d}{dt}
\int_U \rho_I\,d\nu_G
+
\oint_{\partial U}J_I^i n_i\,dS
=
\mathcal S_U.
$$

Closed source sector:

$$
\mathcal S_U=0.
$$

Local form:

$$
\partial_t\rho_I+\partial_iJ_I^i=0.
$$

If:

$$
\mathcal S_U\neq0,
$$

then the source sector is exchanging inherited activity with an unmodelled channel.

That must be declared as a residual, not hidden in \(\Phi_I\) or \(\Psi_I\).

Status:

`source_conservation_from_activity_balance`

### 23.5. Isotropic source condition

An isotropic weak source satisfies:

$$
S_I^{ij}
=
P_I\delta^{ij}.
$$

Equivalently:

$$
\Pi_I^{ij}=0.
$$

This is expected for:

1. static pressureless matter at leading Newtonian order;
2. isotropic coarse-grained fluids;
3. no preferred spatial direction in the source microstructure.

It fails for:

1. directed streams;
2. shear stresses;
3. vector/tensor residual sources;
4. anisotropic inherited activity.

Status:

`isotropic_source_condition_defined`

### 23.6. Slip source packet

The slip equation target becomes:

$$
\Delta_S(\Psi_I-\Phi_I)
=
\mathcal C_{\Pi,I}[\Pi_I]
+
\mathcal R_{\mathrm{slip},I}.
$$

In the no-residual isotropic domain:

$$
\Pi_I^{ij}=0,
\qquad
\mathcal R_{\mathrm{slip},I}=0.
$$

Then:

$$
\Delta_S(\Psi_I-\Phi_I)=0.
$$

With flat boundary:

$$
\Psi_I-\Phi_I\to0,
$$

we get:

$$
\Psi_I=\Phi_I.
$$

Status:

`no_slip_from_isotropic_source_packet`

### 23.7. Experimental gates

The source-stress packet must be constrained by:

| Gate | Required |
|---|---|
| Newtonian dynamics | \(\rho_I\Rightarrow\nabla^2\Phi_I\) |
| lensing vs dynamics | \(\Pi_I\) controls slip residual |
| cluster / fluid systems | pressure/stress must not be ignored |
| cosmology perturbations | slip and anisotropic stress are separately constrained |
| WEP | source coupling must remain universal |

Status:

`source_stress_experimental_gates`

### 23.8. What v5.24 closes

This section defines:

$$
\mathcal T_I
=
(\rho_I,J_I^i,P_I,\Pi_I^{ij})
$$

as coarse-grained moments of inherited activity.

It gives:

$$
\Pi_I^{ij}=0
\Rightarrow
\Psi_I=\Phi_I
$$

only with:

1. source conservation;
2. universal coupling;
3. no additional slip residual;
4. flat boundary condition.

It does not yet derive:

1. the full particle mass spectrum;
2. the event-density calibration \(\lambda_I\) and exact \(\nu_G\) reconstruction;
3. full relativistic stress-energy tensor;
4. Einstein equations.

Next target:

derive \(\lambda_I\), \(a_{EF}\), and matter calibration from primitive inheritance so \(\rho_I^G\) is no longer externally calibrated.

Status:

`source_stress_packet_gap_reduced`

Volume reconstruction bridge:

`sections/24-volume-reconstruction-bridge.md`

Source-weight bridge:

`sections/25-source-weight-bridge.md`

Vacuum stiffness bridge:

`sections/26-vacuum-stiffness-bridge.md`
