## 124. Anchor Closure Gates

Status: `finite_guard`, not physical closure.

The length and mass anchors now have their own acceptance gates.

### 124.1. Length anchor gates

For local radar calibration:

$$
\ell_0
=
\frac{c_I\Delta\tau_{ABA}}{2w_S(A,B)}.
$$

For link-frequency calibration:

$$
\ell_0
=
\frac{c_I}{\omega_{\ell,I}}.
$$

Required gates:

1. `ell0_radar_consistency_demo`;
2. `ell0_link_frequency_consistency_demo`;
3. `ell0_no_gravity_input_demo`.

The third gate forbids defining \(\ell_0\) from \(G_N\), Planck length,
black-hole formulas, or weak-gravity residuals.

### 124.2. Mass anchor gates

The mass anchor is allowed to use an inertial response protocol:

$$
m_{0,I}
=
\frac{\Delta p_{\mathrm{proto}}}{\Delta v},
$$

where \(\Delta p_{\mathrm{proto}}\) is a pre-registered impulse readout, not
\(\hbar k\), spectroscopy, \(G_N\), or Planck units.

Required gates:

1. `primitive_mass_anchor_inertia_response_demo`;
2. `primitive_mass_anchor_no_quantum_gravity_input_demo`.

### 124.3. Honest status

These gates do not derive the physical anchors. They make the next work
auditable:

1. if \(\ell_0\) is promoted, the route must pass radar/frequency consistency
   and no-gravity-source checks;
2. if `primitive_mass_anchor_I` is promoted, the route must pass inertial
   response and no-quantum/gravity-source checks.

Accepted:

`anchor_closure_gates_defined`

Not accepted:

`ell0_closure_I = derived`

`primitive_mass_anchor_closure_I = derived`
