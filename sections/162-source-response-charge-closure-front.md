## 162. Source-Response Charge Closure Front

Status:

`source_response_charge_closure_front_initialized`

This section isolates the first concrete subproblem of the joint
action-gravity anchor.

The target is:

`source_response_charge_closure_I = target`.

It asks whether the same packet property that behaves as inertial mass can also
act as the source charge for clock-strain response.

### 162.1. Required claim

The desired bridge is not:

`G_N calibrates source charge`.

That would only restate local gravity calibration.

The desired bridge is:

\[
m_{\mathrm{inertial},I}
=
q_{\Phi,I}^{\mathrm{passive}}
=
q_{\Phi,I}^{\mathrm{active}}
\]

before any comparison with local \(G\).

Status:

`active_passive_inertial_equality_required`

### 162.2. Machine target

The verifier now requires the route to include:

1. `primitive_mass_anchor_I`;
2. `primitive_mass_anchor_closure_I`;
3. `source_response_charge_I`;
4. `active_passive_inertial_equality_I`;
5. `source_stress_packet_closure_I`;
6. `clock_strain_source_law_I`.

The finite gates check:

1. source-response normalization without \(G_N\);
2. no calibrated-anchor input;
3. active/passive/inertial equality;
4. packet universality;
5. no postfit source-charge selection.

Status:

`source_response_charge_guard_registered`

### 162.3. Forbidden shortcuts

The closure may not use:

1. `G_N`;
2. Planck units;
3. `hbar_obs`;
4. `calibrated_hbar_I`;
5. `calibrated_G_anchor_I`;
6. `local_G_anchor_I`.

Those objects are allowed only after the route exists, as validation anchors.

Status:

`source_charge_calibration_shortcut_forbidden`

### 162.4. Relation to the joint anchor

The joint target now depends on:

`source_response_charge_closure_I`

instead of raw:

`source_response_charge_I`.

This prevents the global `hbar-G` bridge from consuming an unclosed source
charge placeholder.

Status:

`joint_anchor_requires_closed_source_charge`

### 162.5. Failure condition

If source charge can only be normalized by importing local \(G\), \(G_N\), or a
calibrated gravity anchor, then this front fails as a fundamental bridge.

The theory would remain:

`two_calibrated_sectors_not_unified`.

If the equality is obtained from the same primitive packets that define
inertial mass, then the next front is:

`clock_vacuum_stiffness_from_source_charge`.

Section 163 registers that next front as:

`clock_vacuum_stiffness_from_source_charge_I = target`.

Status:

`source_response_charge_front_has_binary_outcome`
