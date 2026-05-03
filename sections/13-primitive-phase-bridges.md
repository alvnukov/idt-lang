## 13. Primitive Phase Bridges

This section reduces two gaps:

1. why inherited action should be additive along histories;
2. why charge should appear as a connection phase.

It does not derive the numerical values of \(\hbar\), \(e\), or \(\alpha_{\mathrm{em}}\).

It gives the support conditions needed before such a derivation can be meaningful.

Status:

`primitive_phase_bridge_conditions_initialized`

### 13.1. Phase readout of update chains

Let a history be an ordered update chain:

$$
h
=
(\eta_1,\eta_2,\ldots,\eta_N).
$$

Let:

$$
U_I(h)\in U(1)
$$

be the phase readout of the chain.

Composition condition:

$$
U_I(h\circ k)
=
U_I(h)U_I(k).
$$

Empty-chain condition:

$$
U_I(\varnothing)=1.
$$

Reverse-chain condition:

$$
U_I(h^{-1})
=
\overline{U_I(h)}.
$$

If every elementary update has a phase increment:

$$
U_I(\eta)
=
e^{iu_I(\eta)},
$$

then:

$$
U_I(h)
=
\exp\left[
i\sum_{\eta\in h}u_I(\eta)
\right].
$$

Define inherited action density:

$$
\mathfrak s_I(\eta)
=
\hbar_I u_I(\eta).
$$

Then:

$$
S_I(h)
=
\sum_{\eta\in h}\mathfrak s_I(\eta)
$$

and:

$$
U_I(h)
=
e^{iS_I(h)/\hbar_I}.
$$

Therefore additivity of action is not an independent postulate once the phase readout is a multiplicative readout of concatenated update chains.

Status:

`additive_action_from_phase_composition`

### 13.2. Refinement invariance

The update ordering parameter \(\lambda\) is not an observable clock.

If an update is refined:

$$
\eta
\mapsto
(\eta_1,\ldots,\eta_m),
$$

then phase readout must satisfy:

$$
u_I(\eta)
=
\sum_{r=1}^{m}u_I(\eta_r)
\mod 2\pi.
$$

Equivalently:

$$
\mathfrak s_I(\eta)
=
\sum_{r=1}^{m}\mathfrak s_I(\eta_r)
\mod 2\pi\hbar_I.
$$

In a continuum readout:

$$
S_I[\gamma]
=
\int_\gamma L_I\,d\tau_I.
$$

Reparametrization:

$$
\lambda\mapsto f(\lambda)
$$

may change the density representation, but not:

$$
\int_\gamma L_I\,d\tau_I
$$

and not:

$$
e^{iS_I[\gamma]/\hbar_I}.
$$

This keeps \(\lambda\) as bookkeeping rather than absolute time.

Status:

`update_refinement_invariant_action_phase`

### 13.3. Phase gradients and known quantum gates

In a smooth readout domain, define:

$$
p_i
=
\partial_i S_I,
\qquad
E
=
-\partial_t S_I.
$$

For a local plane phase:

$$
\phi_I(x,t)
=
k_ix^i-\omega t,
$$

and:

$$
\phi_I
=
\frac{S_I}{\hbar_I}.
$$

Then:

$$
p_i
=
\hbar_I k_i,
$$

and:

$$
E
=
\hbar_I\omega
=
h_I f.
$$

Known gates:

$$
p=\hbar k,
\qquad
E=\hbar\omega=hf.
$$

This is a derivation of the gate from action-phase readout plus spatial/clock periodicity.

It is not a numerical derivation of \(\hbar\).

Status:

`de_broglie_spectral_gates_from_action_phase`

### 13.4. Coarse-grained classical limit

For many unresolved alternatives:

$$
\mathcal A
\sim
\sum_h
\exp[iS_I(h)/\hbar_I].
$$

When action differences are large compared with \(\hbar_I\), non-stationary phases cancel under coarse-graining.

Dominant histories satisfy:

$$
\delta S_I=0.
$$

With continuum action:

$$
S_I[\gamma]
=
\int L_I(x,\dot x)\,d\tau_I,
$$

the stationary condition gives:

$$
\frac{d}{d\tau_I}
\frac{\partial L_I}{\partial \dot x^i}
-
\frac{\partial L_I}{\partial x^i}
=
0.
$$

This recovers classical equations as stationary phase readout, not as primitive mechanics.

Known gate:

WKB/classical limit of quantum phase must agree with Hamilton-Jacobi / least-action mechanics.

Status:

`classical_limit_from_stationary_inherited_phase`

### 13.5. Charge as phase-response label

Charge is not introduced first as a force.

It is introduced as a label controlling response to local phase connection.

For a path \(h\):

$$
U_{q,I}(h)
=
\exp\left[
\frac{i q_I}{\hbar_I}
\int_h A_{I,\mu}\,dx^\mu
\right].
$$

The total phase readout is:

$$
U_{\mathrm{tot},I}(h)
=
\exp\left[
\frac{i}{\hbar_I}
\left(
S_I(h)
+
q_I\int_h A_{I,\mu}\,dx^\mu
\right)
\right].
$$

Thus the minimal charged action readout is:

$$
S_{q,I}(h)
=
S_I(h)
+
q_I\int_h A_{I,\mu}\,dx^\mu.
$$

This is the least additional structure needed to compare charged phases between alternatives.

Status:

`charge_as_connection_phase_response`

### 13.6. Gauge covariance

Endpoint phase relabeling:

$$
\psi(x)
\mapsto
e^{iq_I\Lambda(x)/\hbar_I}\psi(x)
$$

must not change closed readout probabilities.

Connection transformation:

$$
A_{I,\mu}
\mapsto
A_{I,\mu}-\partial_\mu\Lambda.
$$

Then:

$$
\int_{x_i}^{x_f} A_{I,\mu}dx^\mu
\mapsto
\int_{x_i}^{x_f} A_{I,\mu}dx^\mu
-
\Lambda(x_f)
+
\Lambda(x_i).
$$

The endpoint phase relabeling cancels this change.

For a closed loop:

$$
\oint A_{I,\mu}dx^\mu
\mapsto
\oint A_{I,\mu}dx^\mu.
$$

Therefore the gauge-invariant charged phase is the holonomy:

$$
\Delta\phi_{q,I}
=
\frac{q_I}{\hbar_I}
\oint A_{I,\mu}dx^\mu.
$$

Known gate:

Aharonov-Bohm phase depends on connection holonomy, not on local force along the path.

Status:

`ab_holonomy_from_gauge_covariance`

### 13.7. Field strength and force readout

The connection has curvature:

$$
F_{I,\mu\nu}
=
\partial_\mu A_{I,\nu}
-
\partial_\nu A_{I,\mu}.
$$

By Stokes readout in the static magnetic case:

$$
\oint \mathbf A_I\cdot d\mathbf x
=
\int \mathbf B_I\cdot d\mathbf S.
$$

The Aharonov-Bohm phase is sensitive to the holonomy even where:

$$
F_{I,\mu\nu}=0
$$

along the path.

Force readout is therefore secondary:

$$
F_{I,\mu\nu}
\Rightarrow
\text{local acceleration/deflection},
$$

while holonomy readout is primary for phase comparison:

$$
A_I
\Rightarrow
\text{relative phase}.
$$

Status:

`connection_before_force_readout`

### 13.8. Charge quantization gate

If allowed charged histories are single-valued under a closed phase relabeling:

$$
\Lambda
\sim
\Lambda+\Lambda_0,
$$

then:

$$
e^{iq_I\Lambda_0/\hbar_I}
=
1.
$$

Therefore:

$$
\frac{q_I\Lambda_0}{\hbar_I}
=
2\pi n.
$$

This gives a possible route to charge quantization:

$$
q_I
=
n e_I.
$$

Status:

`charge_quantization_route_not_yet_derived`

This is not yet accepted as a derivation because \(\Lambda_0\) and allowed global connection topology are not derived from primitive inheritance.

Known gates:

1. electric charge appears quantized in observed matter sectors;
2. fractional effective charges can appear in collective readout sectors;
3. AB flux period must use the charge of the interfering object.

### 13.9. Fine-structure target after gauge bridge

The bridge now has:

$$
\hbar_I
\quad
\text{from action-phase scale},
$$

and:

$$
q_I
\quad
\text{from connection response}.
$$

But:

$$
\alpha_{\mathrm{em},I}
=
\frac{e_I^2}{4\pi\epsilon_{0,I}\hbar_I c_I}
$$

also requires the normalization of field energy / vacuum response:

$$
\epsilon_{0,I}
\quad
\text{or equivalently}
\quad
g_I.
$$

Therefore:

$$
\text{AB phase}
\Rightarrow
\frac{e_I}{\hbar_I}
$$

but not yet:

$$
\alpha_{\mathrm{em},I}.
$$

To reach \(\alpha_{\mathrm{em},I}\), the next bridge must derive the electromagnetic field-cost functional:

$$
\mathcal F_A[A]
\sim
\int F_{I,\mu\nu}F_I^{\mu\nu}\,d\nu
$$

and its coupling normalization.

Status:

`alpha_requires_field_cost_not_only_ab_phase`

### 13.10. What v5.14 closes

This section closes a logical gap:

$$
U_I(h\circ k)=U_I(h)U_I(k)
\Rightarrow
S_I(h\circ k)=S_I(h)+S_I(k)
\mod 2\pi\hbar_I.
$$

It also closes the conditional AB gap:

$$
\text{local phase covariance}
\Rightarrow
A_I
\Rightarrow
\oint A_I
\Rightarrow
\Delta\phi_{AB,I}.
$$

It does not close:

1. numerical \(\hbar\);
2. numerical \(\alpha_{\mathrm{em}}\);
3. primitive topology of charge quantization;
4. field-cost normalization;
5. full electromagnetic dynamics.

Next target:

$$
A_I
\Rightarrow
\mathcal F_A[A]
\Rightarrow
g_I
\Rightarrow
\alpha_{\mathrm{em},I}.
$$

Status:

`primitive_phase_bridge_gap_reduced`

Electromagnetic field-cost normalization:

`sections/14-electromagnetic-field-cost.md`

Phase-action kappa gate:

`sections/44-phase-action-kappa-gate.md`

Action cocycle bridge:

`sections/71-action-cocycle-bridge.md`

Primitive transition phase readout:

`sections/76-primitive-transition-phase-readout.md`
