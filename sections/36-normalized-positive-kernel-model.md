## 36. Normalized Positive Kernel Model

This section gives the first normalized positive kernel model for \(x_0\).

It does not claim that nature must choose this model.

It defines the minimal unit-response sector that can be tested and then generalized.

Status:

`normalized_positive_kernel_model_initialized`

### 36.1. Two positive modes

Let the link kernel decompose into two positive modes:

$$
u_+,\quad u_-.
$$

Flat weights:

$$
\Omega_+=\Omega_-=\frac12.
$$

Define the normalized response generator:

$$
B_{EF}u_\pm
=
\pm u_\pm.
$$

The eigenvalues \(\pm1\) define the unit response convention for the minimal sector.

Status:

`two_mode_positive_kernel_defined`

### 36.2. Kernel deformation

The strain-deformed positive kernel is:

$$
K_{EF}(s)
=
\exp[-sB_{EF}].
$$

Mode weights become:

$$
\Omega_\pm(s)
=
\frac12e^{\mp s}.
$$

Therefore:

$$
X_\pm
=
\pm1.
$$

So the minimal normalized response has:

$$
x_0=1.
$$

Status:

`x0_fixed_by_unit_kernel_generator`

### 36.3. Stiffness

The partition is:

$$
Z(s)
=
\frac12e^{-s}
+
\frac12e^{s}
=
\cosh s.
$$

The cumulant generator is:

$$
C(s)
=
\log\cosh s.
$$

Thus:

$$
a
=
C''(0)
=
1.
$$

This is the minimal dimensionless link stiffness:

$$
\bar a_{EF}=1.
$$

Status:

`minimal_dimensionless_stiffness_one`

### 36.4. Symbolic G in normalized sector

Substituting:

$$
x_0=1
$$

into the minimal link ensemble gives:

$$
G_I
=
\frac{c_I^4D_S}
{4\pi\kappa_{\chi,I}n_L\ell_0^2}.
$$

Remaining non-gravitational inputs:

$$
\kappa_{\chi,I},\quad n_L,\quad \ell_0,\quad D_S.
$$

Status:

`normalized_sector_symbolic_G`

### 36.5. Generalization residual

If the real kernel response has eigenvalues:

$$
\pm x_0
$$

with:

$$
x_0\neq1,
$$

define:

$$
\mathcal R_x
=
x_0^2-1.
$$

This residual must be derived from the kernel.

It cannot be adjusted after comparing \(G_I\) to \(G_N\).

Status:

`kernel_response_residual_defined`

### 36.6. What is closed

This section closes:

$$
x_0
$$

inside the minimal normalized positive-kernel sector:

$$
x_0=1.
$$

It does not yet derive:

1. why the physical kernel must be this minimal two-mode kernel;
2. \(\kappa_{\chi,I}\);
3. \(n_L\);
4. \(\ell_0\);
5. numerical \(G_I\).

Next target:

derive \(n_L\ell_0^2\) from event-density calibration and spatial order/count reconstruction.

Kernel phase curvature gate:

`sections/45-kernel-phase-curvature-gate.md`

Status:

`x0_minimal_sector_closed`
