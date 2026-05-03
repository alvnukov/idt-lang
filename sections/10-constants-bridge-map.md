## 10. Constants Bridge Map

Dimensional constants are not directly physical by themselves.

Their numerical values depend on unit conventions.

The physical content lives in:

1. bridge roles between readout sectors;
2. dimensionless combinations;
3. universality across independent experimental routes.

### 10.1. Bridge constants

| Constant | Proto-role | Readout bridge |
|---|---|---|
| \(c_I\) | causal-clock conversion | time readout \(\leftrightarrow\) spatial/null readout |
| \(\hbar_I\) | action-phase conversion | inherited action \(\leftrightarrow\) actualization phase |
| \(G_I\) | source-geometry conversion | inherited activity/source \(\leftrightarrow\) curvature/potential |
| \(k_{B,I}\) | entropy-temperature conversion | state count \(\leftrightarrow\) thermal energy |
| \(e_I\) | gauge-charge scale | phase connection \(\leftrightarrow\) electromagnetic coupling |
| \(\Lambda_I\) or \(\mathcal R_H\) | cosmological residual scale | vacuum/cosmic readout \(\leftrightarrow\) expansion |

These constants are not independent assumptions unless their bridge sectors are independent.

The theory must test whether they reduce to a smaller set of primitive scales.

### 10.2. Dimensionless invariant rule

A claimed fundamental relation must be expressible as a dimensionless invariant.

Examples:

$$
\alpha_{\mathrm{em}}
=
\frac{e^2}{4\pi\epsilon_0\hbar c}
$$

$$
\alpha_G(m)
=
\frac{Gm^2}{\hbar c}
$$

$$
\Lambda l_P^2
$$

where:

$$
l_P
=
\sqrt{\frac{\hbar G}{c^3}}
$$

Dimensionful relations such as:

$$
l_P=\sqrt{\hbar G/c^3}
$$

are unit-construction formulas.

They are useful, but not by themselves a derivation.

### 10.3. Planck-unit synthesis

The three bridges:

$$
\hbar_I,\quad c_I,\quad G_I
$$

generate Planck readout scales:

$$
l_{P,I}
=
\sqrt{\frac{\hbar_I G_I}{c_I^3}}
$$

$$
t_{P,I}
=
\sqrt{\frac{\hbar_I G_I}{c_I^5}}
$$

$$
m_{P,I}
=
\sqrt{\frac{\hbar_I c_I}{G_I}}
$$

$$
E_{P,I}
=
\sqrt{\frac{\hbar_I c_I^5}{G_I}}
$$

In this theory, these are not primitive lengths/masses.

They are derived crossover scales where quantum phase, causal propagation, and source-geometry coupling meet.

Status:

`planck_units_as_bridge_crossover_scales`

### 10.4. Electromagnetic bridge

If electromagnetic readout is introduced, the fine-structure constant must appear as:

$$
\alpha_{\mathrm{em},I}
=
\frac{e_I^2}{4\pi\epsilon_{0,I}\hbar_I c_I}
$$

The physical target is dimensionless:

$$
\alpha_{\mathrm{em},I}
\to
\alpha_{\mathrm{obs}}
$$

not a separate fit of \(e,\hbar,c\) in every context.

Quantum electrical gates:

$$
K_J
=
\frac{2e}{h}
$$

$$
R_K
=
\frac{h}{e^2}
$$

These connect phase-frequency and charge transport.

The protolanguage must eventually explain why the same \(h_I\) appears in:

1. action phase;
2. spectroscopy;
3. matter-wave interference;
4. Josephson relation;
5. quantum Hall resistance.

Status:

`electromagnetic_bridge_target`

Not yet derived:

`primitive_charge_phase_connection`

### 10.5. Thermal bridge

Temperature is not primitive.

It is a readout of state-counting / entropy.

Thermal bridge:

$$
E
=
k_{B,I}T
$$

Entropy bridge:

$$
S_{\mathrm{therm}}
=
k_{B,I}\log\Omega
$$

The dimensionless object is:

$$
\frac{E}{k_{B,I}T}
$$

Status:

`thermal_bridge_target`

Not yet derived:

`primitive_entropy_temperature_readout`

### 10.6. Cosmological bridge

Dark energy must not be assumed to be exactly \(\Lambda\).

The validated-domain residual rule allows:

$$
H^2(a)
=
\frac{8\pi G}{3}\rho_b(a)
-
\frac{kc^2}{a^2}
+
\mathcal R_H(a)
$$

If:

$$
\mathcal R_H(a)
=
\frac{\Lambda c^2}{3}
$$

then the residual reduces to \(\Lambda\)CDM in that domain.

Dimensionless cosmological gate:

$$
\Lambda l_P^2
$$

or, operationally:

$$
H(a)t_P
$$

The protolanguage must explain whether \(\mathcal R_H\) is:

1. vacuum inherited activity;
2. coarse-graining residual;
3. missing source sector;
4. true cosmological constant fixed point.

Status:

`cosmological_residual_bridge_target`

### 10.7. No-magic-constant rule

A constant is accepted as primitive only if no deeper bridge decomposition is found.

A claimed relation between constants is accepted only if it gives at least one dimensionless prediction.

Required form:

$$
\mathcal C_1(\hbar_I,c_I,G_I,e_I,k_{B,I},\ldots)
=
\mathcal C_{\mathrm{obs}}
$$

where \(\mathcal C_1\) is dimensionless.

Otherwise the relation is only a unit convention.

Current status:

| Object | Status |
|---|---|
| \(\hbar_I\) | action-phase bridge defined, numerical derivation open |
| \(c_I\) | clock/causal bridge partially reconstructed |
| \(G_I\) | source-geometry coupling calibrated, derivation open |
| \(e_I,\alpha_{\mathrm{em},I}\) | electromagnetic bridge target |
| \(k_{B,I}\) | thermal bridge target |
| \(\Lambda_I,\mathcal R_H\) | cosmological residual target |

Next derivation target:

$$
\mathfrak s_I(\eta)
\Rightarrow
\hbar_I
\quad
\text{and}
\quad
\mathfrak q_I(\eta)
\Rightarrow
\alpha_{\mathrm{em},I}
$$

without per-experiment fitting.

Status:

`constants_bridge_map_initialized`

Predictive use of these constants is defined in:

`sections/11-predictive-closure.md`
