## 127. Executable Weak-Field Clock Calculator

Status:

`executable_conditional_weak_field_calculator`

This pass turns the clock-rate weak-field route into a finite verifier cluster.
It does not claim that \(G_I\) or \(\gamma_I^{\mathrm{PPN}}\) are derived.
It checks that, once the weak-field readout constants are fixed, the route
recomputes the standard uncontested weak-field formulas without refitting each
observable.

The checked target is:

$$
\texttt{weak\_field\_clock\_calculator\_I}.
$$

Its declared dependencies are:

$$
c_I,\quad G_N,\quad \Phi_I,\quad \gamma_I^{\mathrm{PPN}}.
$$

Here \(G_N\) remains an experimental calibration, not a primitive derivation.
The value of the cluster is that the same calibration is used across clock,
source, acceleration, and null-propagation checks.

### 127.1. Redshift gate

Clock-rate potential:

$$
\Phi_I=c_I^2\log\chi .
$$

Frequency comparison:

$$
\frac{\nu_A-\nu_B}{\nu_B}
\approx
\frac{\Phi_I(A)-\Phi_I(B)}{c_I^2}.
$$

For a 1 m near-Earth height difference, using:

$$
\Delta\Phi=g h,\qquad
g=9.80665\,\mathrm{m\,s^{-2}},\quad h=1\,\mathrm m,
$$

the verifier recomputes:

$$
\frac{\Delta\nu}{\nu}
=
\frac{9.80665}{c^2}
=
1.0911369672198217\times10^{-16}.
$$

Finite gate:

`clock_redshift_1m_demo`

This is not a fit to a clock experiment. It is the standard weak-field
redshift formula evaluated from the clock-rate definition and the chosen
potential convention.

### 127.2. Combined clock-rate gate

The weak slow-clock readout is:

$$
\frac{d\tau}{dt}
\approx
1+\frac{\Phi}{c^2}-\frac{v^2}{2c^2}.
$$

For:

$$
\Phi=100\,\mathrm{m^2s^{-2}},
\qquad
v=1000\,\mathrm{m\,s^{-1}},
$$

the verifier recomputes:

$$
\frac{d\tau}{dt}
=
0.9999999999944379.
$$

Finite gate:

`combined_clock_rate_demo`

This gate keeps gravitational redshift and special-relativistic velocity
dilation in one operational clock formula.

### 127.3. Point-mass clock field

In the calibrated weak-field domain:

$$
\Phi(r)=-\frac{G_NM}{r},
\qquad
a(r)=\frac{G_NM}{r^2},
\qquad
\frac{\Delta\nu_{\infty r}}{\nu_r}
=-\frac{\Phi(r)}{c^2}.
$$

For Earth parameters:

$$
M_\oplus=5.9722\times10^{24}\,\mathrm{kg},
\qquad
r_\oplus=6.371\times10^6\,\mathrm m,
$$

the verifier recomputes:

$$
\Phi(r_\oplus)=-62565145.91115994\,\mathrm{m^2s^{-2}},
$$

$$
a(r_\oplus)=9.820302293385645\,\mathrm{m\,s^{-2}},
$$

$$
\frac{\Delta\nu_{\infty r}}{\nu_r}
=6.961311310505493\times10^{-10}.
$$

Finite gate:

`point_mass_clock_field_demo`

This is a consistency gate. It does not derive \(G_N\); it prevents using
different hidden calibrations for potential, acceleration, and clock redshift.

### 127.4. Gauss/source flux gate

The source law is checked in integrated weak-field form:

$$
\oint_{\partial U}\nabla\Phi\cdot dS
=
4\pi G_NM.
$$

For the same Earth mass, the verifier recomputes:

$$
4\pi G_NM_\oplus
=
5008987303270231.0.
$$

Finite gate:

`source_flux_gauss_demo`

This keeps the Poisson/source route tied to one source normalization. The
theory still owes an independent derivation of the source coefficient from
primitive clock-link stiffness and matter calibration.

### 127.5. PPN light-bending gate

Weak-field null propagation requires the spatial-curvature parameter:

$$
\Delta\theta
=
2(1+\gamma_I^{\mathrm{PPN}})
\frac{G_NM}{c^2b}.
$$

For solar-limb bending with:

$$
M_\odot=1.98847\times10^{30}\,\mathrm{kg},
\qquad
b=R_\odot=6.957\times10^8\,\mathrm m,
\qquad
\gamma_I^{\mathrm{PPN}}=1,
$$

the verifier recomputes:

$$
\Delta\theta
=
8.490267017584816\times10^{-6}\,\mathrm{rad}
\approx
1.75124\,\mathrm{arcsec}.
$$

Finite gate:

`ppn_light_bending_solar_limb_demo`

This gate makes the spatial-curvature gap explicit: \(\gamma_I^{\mathrm{PPN}}\)
must be obtained from the inherited geometry/no-slip sector. Setting it to
one is the GR validation target, not yet a primitive derivation.

### 127.6. Accepted and not accepted

Accepted:

`weak_field_clock_calculator_I = derived_conditional`

The verifier now checks the same calibrated weak-field cluster:

$$
\Phi
\Rightarrow
\frac{\Delta\nu}{\nu},
\qquad
\Phi,v
\Rightarrow
\frac{d\tau}{dt},
\qquad
G_NM
\Rightarrow
\Phi,a,\oint\nabla\Phi\cdot dS,
\qquad
\gamma_I^{\mathrm{PPN}}
\Rightarrow
\Delta\theta.
$$

Not accepted:

`G_I = derived`

Not accepted:

`\gamma_I^{\mathrm{PPN}} = derived`

Not accepted:

`full_GR_I = derived`

### 127.7. What this closes

This closes a practical computation gap: the theory now has an executable
weak-field clock calculator that compares against standard formulas without
changing constants between checks.

What remains open is deeper:

1. derive \(G_I\) from primitive clock-link stiffness;
2. derive \(\gamma_I^{\mathrm{PPN}}\to1\) from no-slip inherited geometry;
3. connect the calibrated source mass to primitive matter packets without
   importing the Newtonian source law as a hidden premise.

This is therefore a strong validation scaffold, not a final gravity derivation.
