## 147. Dual Anchor Search Matrix

Status:

`dual_anchor_search_initialized`

The two anchor searches must run together. A successful length/tick lock without
a work/mass lock still leaves \(A_0\) floating. A successful work/mass lock
without a tick lock also leaves \(A_0\) floating.

The current target is therefore not:

`derive_hbar_from_one_anchor`

but:

`find_two_independent_anchor_locks`.

### 147.1. Length/tick routes

Route L1: clock-vacuum pole or spectral edge:

\[
\mathcal R_\chi(\omega)
\Rightarrow
\omega_{\ell,I}
\Rightarrow
\ell_0=\frac{c_I}{\omega_{\ell,I}}.
\]

Required closure:

1. explicit inherited response function;
2. first stable pole/edge;
3. clock-species universality;
4. no \(G_N\), Planck length, spectra, or \(\hbar\) input.

Route L2: primitive update spectrum:

\[
\mathsf T_{EF}
\Rightarrow
\theta_*,\Delta\tau_{\mathrm{step}}
\Rightarrow
\omega_{\ell,I}
=
\frac{\theta_*}{\Delta\tau_{\mathrm{step}}}.
\]

Required closure:

1. transition weights \(\mathcal T_{EF}\);
2. strain-coupled first mode;
3. independent step duration \(\Delta\tau_{\mathrm{step}}\);
4. no post-selection after residual tests.

Route L3: primitive cycle grammar:

\[
N_{\mathrm{cyc}},m_*
\Rightarrow
\theta_*=\frac{2\pi m_*}{N_{\mathrm{cyc}}}.
\]

This can lock phase denominator, but not time by itself.

Current length status:

`tick_scale_lock_I = bound_only`.

### 147.2. Work/mass routes

Route W1: inertial response:

\[
m_I=\frac{J_I}{\Delta v}.
\]

Required closure:

1. independent impulse scale \(J_I\);
2. stable inertial response across packets;
3. active/passive/inertial equality;
4. no spectroscopy, \(E=\hbar\omega\), \(G_N\), or Planck-unit input.

Route W2: kernel-strain work balance:

\[
W_{0,I}
=
\sum W_{\mathrm{in}}-\sum W_{\mathrm{out}}.
\]

Required closure:

1. physical work scale for each packet;
2. partition-invariant coarse-graining;
3. sector universality;
4. independent mass/energy anchor.

Route W3: source-response charge:

\[
q_{\Phi,I}
\Rightarrow
\text{active/passive/inertial equality gate}.
\]

This route is attractive because it can connect weak gravity, inertia, and
matter calibration, but it risks importing \(G_N\). Therefore \(G_N\) must stay
only a validation gate.

Current work/mass status:

`work_scale_lock_I = not_locked`.

### 147.3. Combined success criterion

The combined search succeeds only if:

\[
\mathrm{Lock}(\tau_0)
\wedge
\mathrm{Lock}(W_0)
\wedge
\mathrm{Lock}_{\mathrm{gauge}}(A_0).
\]

Then and only then:

\[
A_{0,I}=W_{0,I}\tau_{0,I}
\]

can become a physical action standard.

Partial success is allowed, but must be recorded as:

`route_improved_not_hbar`.

### 147.4. Next high-value move

The best next technical move is L2+W1:

1. use primitive update spectrum or cycle grammar to attack the step-duration
   problem;
2. use inertial response to define a mass anchor;
3. require active/passive/inertial equality before any gravitational comparison;
4. keep \(\hbar\), \(G_N\), Planck units, and spectroscopy as forbidden inputs.

Accepted:

`dual_anchor_search_initialized`.

Not accepted:

`length_lock_found`.

Not accepted:

`work_mass_lock_found`.

Not accepted:

`hbar_I = derived_conditional`.
