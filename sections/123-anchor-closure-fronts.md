## 123. Anchor Closure Fronts

Status: `front_split`.

The scale obstruction theorem exposes two unresolved anchors. They are now
explicit closure fronts, not implicit assumptions.

### 123.1. Length anchor

Tick closure requires the spatial radar scale:

$$
\ell_0.
$$

The manifest therefore adds:

`ell0_closure_I`

with route:

$$
(\ell_0,c_I,\omega_{\ell,I})
\Rightarrow
\texttt{ell0\_closure\_I}.
$$

This does not derive \(\ell_0\). It records that the tick route cannot close
until the non-gravitational link-frequency / clock-radar front closes.

### 123.2. Mass anchor

Work closure requires a mass scale:

$$
\texttt{primitive\_mass\_anchor\_I}.
$$

The manifest therefore adds:

`primitive_mass_anchor_closure_I`

with route:

$$
\texttt{primitive\_mass\_anchor\_I}
\Rightarrow
\texttt{primitive\_mass\_anchor\_closure\_I}.
$$

This is intentionally unresolved. It prevents the theory from replacing a
missing mass scale with a hidden quantum or gravitational calibration.

### 123.3. Updated action-standard ladder

The honest ladder is now:

$$
\texttt{ell0\_closure\_I}
\Rightarrow
\tau_{0,I},
$$

$$
\texttt{primitive\_mass\_anchor\_closure\_I}
\Rightarrow
W_{0,I},
$$

$$
W_{0,I}\tau_{0,I}
\Rightarrow
A_{0,I}
\Rightarrow
\hbar_I.
$$

Current status:

1. `ell0_closure_I = target`;
2. `primitive_mass_anchor_closure_I = target`;
3. `primitive_tick_closure_I = target`;
4. `primitive_work_unit_closure_I = target`;
5. `A0_I = blocked`;
6. `hbar_I = blocked`.

Required anchor gates:

1. `ell0_radar_consistency_demo`;
2. `ell0_link_frequency_consistency_demo`;
3. `ell0_no_gravity_input_demo`;
4. `primitive_mass_anchor_inertia_response_demo`;
5. `primitive_mass_anchor_no_quantum_gravity_input_demo`.

Section 146 adds the lock layer above these fronts: current `ell0` evidence is
an upper bound, and current inertial response is a candidate ratio, so neither
front yet locks an absolute scale.

Accepted:

`anchor_closure_fronts_declared`

Not accepted:

`hidden_length_anchor`

`hidden_mass_anchor`
