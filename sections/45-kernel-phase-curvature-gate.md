## 45. Kernel Phase Curvature Gate

This section targets the remaining dimensionless factor:

$$
C_{\chi,I}.
$$

It does not assert that:

$$
C_{\chi,I}=1
$$

unconditionally.

It defines the gate under which the minimal positive kernel gives that value.

Status:

`kernel_phase_curvature_gate_initialized`

### 45.1. Two curvatures must be separated

The positive-kernel sector already gives the real stiffness:

$$
\bar a_{EF}
=
\left.
\frac{\partial^2}{\partial s^2}
\log\frac{Z_{EF}(s)}{Z_{EF}(0)}
\right|_{s=0}.
$$

In the minimal normalized two-mode sector:

$$
\bar a_{EF}=1.
$$

The phase-action sector needs:

$$
C_{\chi,EF}
=
\left.
\frac{\partial^2\Theta_{\chi,EF}}
{\partial s_{EF}^2}
\right|_{s_{EF}=0}.
$$

These are not automatically identical.

Status:

`real_stiffness_phase_curvature_separated`

### 45.2. Kernel-action identification gate

The identification:

$$
C_{\chi,EF}
=
\bar a_{EF}
$$

is admissible only if the same normalized positive generator controls:

1. real distinguishability stiffness;
2. inherited action-phase cost;
3. reversal symmetry \(s\mapsto -s\);
4. local flat-vacuum calibration.

If any of these fail, define a residual:

$$
\mathcal R_C
=
C_{\chi,I}-\bar a_{I}.
$$

Status:

`kernel_action_identification_gate`

### 45.3. Minimal conditional sector

Under the gate:

$$
C_{\chi,I}
=
\bar a_I.
$$

For the minimal normalized two-mode kernel:

$$
\bar a_I=1.
$$

Therefore:

$$
C_{\chi,I}^{\mathrm{min}}=1.
$$

This is a conditional sector:

$$
\text{minimal kernel}
+
\text{kernel-action identification}
\Rightarrow
C_{\chi,I}=1.
$$

It is not a universal theorem yet.

Status:

`Cchi_minimal_conditional_one`

### 45.4. Kappa in the minimal conditional sector

With:

$$
C_{\chi,I}=1,
$$

the update-action route becomes:

$$
\kappa_{\chi,I}^{(A,\mathrm{min})}
=
\frac{\hbar_I}{\tau_{\chi,*}}.
$$

Then:

$$
G_I^{(A,\mathrm{min})}
=
\frac{c_I^4D_S\ell_{0,*}\tau_{\chi,*}}
{2\pi\hbar_I z_{I,*}q_{V,*}}.
$$

If:

$$
\tau_{\chi,*}
=
\eta_\tau\frac{\ell_{0,*}}{c_I},
$$

then:

$$
G_I^{(A,\mathrm{min})}
=
\frac{\eta_\tau D_Sc_I^3\ell_{0,*}^2}
{2\pi\hbar_I z_{I,*}q_{V,*}}.
$$

Status:

`minimal_conditional_G_formula`

### 45.5. Experimental use

The formula above can become predictive only if:

$$
\ell_{0,*},z_{I,*},q_{V,*},D_S,\eta_\tau
$$

are fixed without gravitational data.

Then \(G_N\) is used only in:

$$
\mathcal R_G
=
\frac{G_I-G_N}{G_N}.
$$

If \(\mathcal R_G\neq0\), the first suspect is not automatically GR.

Possible declared residual locations are:

1. \(\mathcal R_C\): kernel-action identification fails;
2. \(\mathcal R_\tau\): sampling protocol not minimal light-time;
3. \(\mathcal R_{\mathrm{geom}}\): geometry is not regular/isotropic;
4. \(\mathcal R_{\mathrm{source}}\): source law differs outside the Newtonian gate;
5. \(\mathcal R_{\mathrm{cosmo}}\): large-scale readout contains dark-sector residuals.

Status:

`G_residual_locations_predeclared`

### 45.6. No-fit rule

Forbidden:

1. set \(C_{\chi,I}=1\) after seeing \(G_N\);
2. set \(\eta_\tau\) after seeing \(G_N\);
3. absorb \(\mathcal R_G\) into geometry factors;
4. call the minimal conditional sector a completed derivation.

Allowed:

1. use \(C_{\chi,I}=1\) as a pre-declared minimal sector;
2. test the resulting \(G_I\);
3. retain a nonzero residual as physical information;
4. compare with the independent vacuum-response route.

Status:

`Cchi_no_fit_rule`

### 45.7. What is closed

Closed conditionally:

$$
C_{\chi,I}^{\mathrm{min}}=1.
$$

Open:

1. proof that nature selects the minimal two-mode kernel;
2. proof that kernel-action identification holds;
3. numerical \(\eta_\tau\);
4. exact regular geometry;
5. numerical \(G_I\).

Next target:

combine the conditional minimal sector into a single pre-registered \(G_I\) calculator and list all required non-gravitational inputs.

Pre-registered \(G_I\) calculator:

`sections/46-preregistered-G-calculator.md`

Status:

`Cchi_gap_conditionally_reduced`
