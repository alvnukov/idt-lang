## 131. Executable No-Slip Stress Closure

Status:

`executable_conditional_no_slip_support`

The previous PPN pass made \(\gamma_I^{\mathrm{PPN}}\) observable in light
bending, Shapiro delay, and perihelion tests. This pass moves one layer deeper:
it checks the support conditions under which the slip field

$$
\sigma_I=\Psi_I-\Phi_I
$$

must vanish in the weak static sector.

This is still not a primitive derivation of Einstein equations. It is an
executable conditional theorem:

$$
\Pi_I=0,
\qquad
\mathcal R_{\mathrm{nonGR}}=0,
\qquad
\sigma_I|_{\partial S}=0
\Rightarrow
\sigma_I=0
$$

for the finite checked sector.

### 131.1. Slip source equation

The finite source equation is:

$$
\Delta\sigma_I
=
C_{\Pi,I}\Pi_I
+
\mathcal R_{\mathrm{nonGR}}.
$$

Verifier sample:

$$
\sigma=[0,-1,0],
\qquad
C_{\Pi,I}=2,
\qquad
\Pi=[0,1,0],
\qquad
\mathcal R_{\mathrm{nonGR}}=[0,0,0].
$$

At the interior cell:

$$
0-2(-1)+0=2=C_{\Pi,I}\Pi.
$$

Finite gate:

`slip_source_poisson_demo`

This verifies the operator form of the slip source law.

### 131.2. Zero-source boundary gate

No-slip is not implied by \(\Delta\sigma=0\) alone. The boundary condition must
also be flat:

$$
\sigma_I|_{\partial S}=0.
$$

The verifier checks:

$$
\Pi=0,
\qquad
\mathcal R_{\mathrm{nonGR}}=0,
\qquad
\sigma_{\partial S}=0,
\qquad
\sigma=0.
$$

Finite gate:

`zero_stress_boundary_no_slip_demo`

If the source vanishes but the interior slip remains nonzero, the gate fails.

### 131.3. Source continuity gate

The no-slip geometry sector also requires source conservation:

$$
\partial_t\rho+\nabla\cdot J=0.
$$

Finite sample:

$$
\Delta t=0.5,
$$

$$
\rho_0=[1.0,2.0],
\qquad
\rho_1=[1.1,1.8],
\qquad
\nabla\cdot J=[-0.2,0.4].
$$

Then:

$$
\frac{\rho_1-\rho_0}{\Delta t}
+
\nabla\cdot J
=0
$$

cell by cell.

Finite gate:

`source_continuity_demo`

This keeps the stress/no-slip route tied to a conserved source packet.

### 131.4. Accepted and not accepted

Accepted:

`no_slip_stress_closure_I = derived_conditional`

Accepted conditional chain:

$$
\Delta(\Psi_I-\Phi_I)
=
C_{\Pi,I}\Pi_I+\mathcal R_{\mathrm{nonGR}},
\quad
\Pi_I=0,
\quad
\mathcal R_{\mathrm{nonGR}}=0,
\quad
\text{flat boundary}
\Rightarrow
\Psi_I=\Phi_I.
$$

Not accepted:

`\Pi_I=0` for all physical systems.

Not accepted:

`\mathcal R_{\mathrm{nonGR}}=0` at all scales.

Not accepted:

`\gamma_I^{\mathrm{PPN}}=1` outside the validated no-slip domain.

### 131.5. What this opens

The next hard derivation is now narrower:

1. derive the source-stress packet \(\Pi_I^{ij}\) from primitive matter packets;
2. derive when \(\Pi_I^{ij}\) coarse-grains to zero;
3. derive whether \(\mathcal R_{\mathrm{nonGR}}\) can become nonzero at
   galactic/cosmological scales without spoiling solar-system gates.

This preserves the user's caution: the theory should reproduce known tests
without assuming that GR has no residual structure outside its validated
domain.
