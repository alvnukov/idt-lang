## 128. Executable Source-Law Variation

Status:

`executable_conditional_source_law`

This pass makes the source-law bridge less declarative. The verifier now checks
two finite facts:

1. a quadratic clock-strain functional produces a discrete Poisson equation;
2. the continuum coefficient \(c_I^4\beta_I/(\alpha_I\zeta_I)\) matches the
   calibrated Newtonian coefficient \(4\pi G_N\) when the calibration is
   explicitly declared.

The checked target is:

$$
\texttt{clock\_strain\_source\_law\_I}.
$$

It depends on:

$$
\Phi_I,\quad \rho_I^G,\quad \alpha_I,\quad \beta_I.
$$

This does not derive \(G_I\) from primitives. It proves that the proposed
minimal clock-strain functional has the right Euler-Lagrange structure and
keeps the Newtonian coefficient visible as a calibration target.

### 128.1. Discrete variational gate

Use the one-dimensional finite chain:

$$
\varphi_0=0,\qquad
\varphi_1=-1,\qquad
\varphi_2=0.
$$

Use:

$$
\alpha=3,
\qquad
\beta=2,
\qquad
\rho_1=3.
$$

The finite functional is:

$$
F[\varphi]
=
\frac{\alpha}{2}
\sum_i(\varphi_{i+1}-\varphi_i)^2
+
\beta\sum_i\rho_i\varphi_i.
$$

The stationarity condition at the interior point is:

$$
\alpha
(\varphi_{i+1}-2\varphi_i+\varphi_{i-1})
-
\beta\rho_i
=0.
$$

For the selected data:

$$
3[0-2(-1)+0]-2(3)=0.
$$

Finite gate:

`clock_strain_variational_poisson_demo`

This is a local proof-of-form check. It confirms that the functional in the
clock-rate route really produces the Poisson operator rather than merely naming
it.

### 128.2. Continuum coefficient gate

The clock-rate route uses:

$$
\varphi=\frac{\Phi_I}{c_I^2}.
$$

The continuum result is:

$$
\Delta_S\Phi_I
=
\frac{c_I^2\beta_I}{\alpha_I}\rho_I^G.
$$

With matter calibration:

$$
\rho_m c_I^2=\zeta_I\rho_I^G,
$$

the Newtonian source law requires:

$$
4\pi G_I
=
\frac{c_I^4\beta_I}{\alpha_I\zeta_I}.
$$

The verifier uses:

$$
c=299792458\,\mathrm{m\,s^{-1}},
\qquad
G_N=6.67430\times10^{-11},
\qquad
\alpha=1,
\qquad
\zeta=1,
$$

and therefore:

$$
4\pi G_N
=
8.387172739141742\times10^{-10},
$$

$$
\beta
=
1.0383237214224859\times10^{-43}.
$$

Finite gate:

`source_law_coefficient_demo`

The gate checks the coefficient numerically. It does not hide the calibration:
\(\beta\) is still the unresolved clock-source coupling that must later be
derived from primitive inheritance dynamics.

### 128.3. Accepted and not accepted

Accepted:

`clock_strain_source_law_I = derived_conditional`

The accepted result is conditional:

$$
\text{quadratic clock-strain cost}
\Rightarrow
\text{Poisson operator}.
$$

Also accepted:

$$
\frac{c_I^4\beta_I}{\alpha_I\zeta_I}
\leftrightarrow
4\pi G_N
$$

as an explicit calibration equation.

Not accepted:

`G_I = derived`

Not accepted:

`\beta_I = primitive-derived`

Not accepted:

`matter calibration \zeta_I = derived`

### 128.4. What this closes

This closes the narrow mathematical gap between the minimal clock-strain
functional and the Poisson source operator.

What remains open:

1. derive \(\alpha_I\) from clock-link stiffness;
2. derive \(\beta_I\) from source response of inherited matter packets;
3. derive \(\zeta_I\) from matter calibration rather than importing mass
   density;
4. validate the same coefficient against redshift, free fall, orbital dynamics,
   and lensing without refitting.

The source law is now executable as a conditional variational derivation, not a
complete primitive derivation.
