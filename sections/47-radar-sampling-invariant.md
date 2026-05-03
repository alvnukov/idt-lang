## 47. Radar Sampling Invariant

This section closes a protocol ambiguity in:

$$
\tau_{\chi,*}
$$

and:

$$
C_{\chi,I}.
$$

The issue is that clock-radar distance is directly measured by a round trip, while the link action response can be normalized per one-way link, half-radar interval, or full echo cycle.

Status:

`radar_sampling_invariant_initialized`

### 47.1. Direct radar fact

For a nearest-neighbour spatial link with:

$$
w_S(E,F)=1,
$$

the clock-order distance definition gives:

$$
\Delta\tau_{EFE}
=
\frac{2\ell_{0,*}}{c_I}.
$$

Thus the half-radar interval is:

$$
\tau_{1/2}
=
\frac{\Delta\tau_{EFE}}{2}
=
\frac{\ell_{0,*}}{c_I}.
$$

Status:

`half_radar_interval_from_clock_order_distance`

### 47.2. Protocol scaling

Let the sampling interval be:

$$
\tau_{\chi,*}
=
\eta_\tau\frac{\ell_{0,*}}{c_I}.
$$

Common choices:

| Protocol | \(\eta_\tau\) |
|---|---:|
| half-radar / one link light-time | \(1\) |
| full radar echo | \(2\) |
| \(m\)-cycle sampling | \(m\) |

If primitive action is additive over repeated identical sampling intervals, then:

$$
C_{\chi,I}^{(m)}
=
mC_{\chi,I}^{(1)}.
$$

Therefore:

$$
\frac{\tau_{\chi,*}^{(m)}}{C_{\chi,I}^{(m)}}
=
\frac{\tau_{\chi,*}^{(1)}}{C_{\chi,I}^{(1)}}.
$$

Status:

`sampling_interval_action_curvature_covary`

### 47.3. Protocol-invariant ratio

Define:

$$
\rho_{\chi,I}
=
\frac{\eta_\tau}{C_{\chi,I}}.
$$

Then:

$$
\frac{\tau_{\chi,*}}{C_{\chi,I}}
=
\rho_{\chi,I}
\frac{\ell_{0,*}}{c_I}.
$$

The \(G_I\) calculator becomes:

$$
G_I^{(A)}
=
\frac{\rho_{\chi,I}D_Sc_I^3\ell_{0,*}^2}
{2\pi\hbar_Iz_{I,*}q_{V,*}}.
$$

This is invariant under changing from half-radar to full-radar normalization, provided action curvature scales additively with the sampling interval.

Status:

`rho_chi_protocol_invariant_defined`

### 47.4. Minimal matched sector

In the minimal matched sector:

$$
C_{\chi,I}^{(1)}=1,
\qquad
\eta_\tau^{(1)}=1.
$$

Therefore:

$$
\rho_{\chi,I}^{\mathrm{min}}=1.
$$

Then:

$$
G_I^{(\mathrm{min})}
=
\frac{D_Sc_I^3\ell_{0,*}^2}
{2\pi\hbar_Iz_{I,*}q_{V,*}}.
$$

Status:

`minimal_matched_radar_sector`

### 47.5. Dimensionless gate after sampling reduction

The dimensionless gate becomes:

$$
\Pi_G^{(\rho)}
=
\frac{
2\pi\hbar_Iz_{I,*}q_{V,*}G_N
}{
\rho_{\chi,I}D_Sc_I^3\ell_{0,*}^2
}.
$$

Prediction:

$$
\Pi_G^{(\rho)}
=
1\pm\epsilon_G.
$$

For the minimal matched sector:

$$
\Pi_G^{(\mathrm{min})}
=
\frac{
2\pi\hbar_Iz_{I,*}q_{V,*}G_N
}{
D_Sc_I^3\ell_{0,*}^2
}.
$$

Status:

`sampling_reduced_dimensionless_G_gate`

### 47.6. No-fit rule

Forbidden:

1. choose half-radar or full-radar normalization after comparing with \(G_N\);
2. change \(C_{\chi,I}\) without changing the matching sampling interval;
3. absorb a failed gate into \(\rho_{\chi,I}\);
4. use observed Planck length to set \(\ell_{0,*}\).

Allowed:

1. pre-register the minimal matched sector \(\rho_{\chi,I}=1\);
2. derive a non-minimal \(\rho_{\chi,I}\) from update-action dynamics;
3. compare the final dimensionless \(\Pi_G^{(\rho)}\) with experiment.

Status:

`radar_sampling_no_fit_rule`

### 47.7. What is closed

Closed:

1. half-radar interval:

$$
\tau_{1/2}=\frac{\ell_{0,*}}{c_I};
$$

2. protocol-invariant sampling/action ratio:

$$
\rho_{\chi,I}=\frac{\eta_\tau}{C_{\chi,I}};
$$

3. minimal matched sector:

$$
\rho_{\chi,I}=1.
$$

Open:

1. proof that the physical sector is minimal matched;
2. independent derivation of \(\rho_{\chi,I}\) if non-minimal;
3. exact \(\ell_{0,*},z_{I,*},q_{V,*},D_S\);
4. numerical \(G_I\).

Next target:

derive or constrain the exact geometry class \((D_S,z_{I,*},q_{V,*})\), because the weak-gravity calculator now depends mainly on geometry and \(\ell_{0,*}\).

Geometry class gate:

`sections/48-geometry-class-gate.md`

Kappa-omega consistency gate:

`sections/59-kappa-omega-consistency-gate.md`

Status:

`sampling_ambiguity_reduced_to_rho`
