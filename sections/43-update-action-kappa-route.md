## 43. Update-Action Kappa Route

This section strengthens the update-action route for:

$$
\kappa_{\chi,I}.
$$

It does not compute its numerical value.

It defines what must be computed without gravitational fitting.

Status:

`update_action_kappa_route_initialized`

### 43.1. Clock strain coordinate

Use the dimensionless clock-rate field:

$$
\varphi(E)=\log\chi(E)
=
\frac{\Phi_I(E)}{c_I^2}.
$$

For a spatial neighbour link \(\langle EF\rangle\), define:

$$
s_{EF}
=
\varphi(E)-\varphi(F).
$$

In the weak field:

$$
s_{EF}
\approx
\frac{\Phi_I(E)-\Phi_I(F)}{c_I^2}.
$$

Status:

`clock_strain_coordinate_defined`

### 43.2. Primitive action response

Let \(\mathcal S_{\chi,EF}[s]\) be the primitive inherited update action accumulated by the flat-vacuum link \(\langle EF\rangle\) over one standard local sampling interval \(\tau_{\chi,*}\).

The action response is:

$$
A_{\chi,EF}
=
\left.
\frac{\partial^2\mathcal S_{\chi,EF}}
{\partial s_{EF}^2}
\right|_{s_{EF}=0}.
$$

Units:

$$
[A_{\chi,EF}]=\text{action}.
$$

This is not yet \(\kappa_{\chi,I}\), because \(\kappa_{\chi,I}\) is an energy scale.

Status:

`primitive_action_second_response_defined`

### 43.3. Kappa from action rate

Define the update-action route value:

$$
\kappa_{\chi,I}^{(A)}
=
\frac{A_{\chi,*}}{\tau_{\chi,*}},
$$

where:

$$
A_{\chi,*}
=
\lim_{U\to\mathrm{flat}}
\langle A_{\chi,EF}\rangle_U.
$$

Units:

$$
[\kappa_{\chi,I}^{(A)}]=\text{energy}.
$$

This gives the correct dimensional role in:

$$
G_I
=
\frac{c_I^4D_S\ell_{0,*}}
{2\pi\kappa_{\chi,I}z_{I,*}q_{V,*}}.
$$

Status:

`kappa_as_action_rate`

### 43.4. Relation to the normalized kernel

The normalized positive-kernel model gives a dimensionless response:

$$
\bar a_{EF}=1
$$

only in the minimal normalized two-mode sector.

The physical action response is then:

$$
A_{\chi,EF}
=
\mathfrak s_{\chi,*}\bar a_{EF}.
$$

Thus in that sector:

$$
\kappa_{\chi,I}^{(A)}
=
\frac{\mathfrak s_{\chi,*}}{\tau_{\chi,*}}.
$$

This is now a consequence of the second-response definition, not a dimensional guess.

Status:

`normalized_kernel_lift_to_action_rate`

### 43.5. Sampling-time gate

The interval \(\tau_{\chi,*}\) must be fixed by the flat clock-network readout before gravitational comparison.

Forbidden:

$$
\tau_{\chi,*}
\Leftarrow
G_N.
$$

Allowed:

$$
\tau_{\chi,*}
\Leftarrow
\text{flat clock-radar sampling protocol}.
$$

Clock universality gate:

$$
\left|
\frac{\tau_{\chi,*}^{(C)}}{\tau_{\chi,*}^{(C')}}-1
\right|
\le
\epsilon_\tau
$$

for admissible calibration clocks after normalization to the same local sampling protocol.

Status:

`sampling_time_no_fit_gate`

### 43.6. Action-scale gate

The action scale \(\mathfrak s_{\chi,*}\) must be fixed by primitive inheritance or by the already independent phase/action sector.

Allowed:

$$
\hbar_I
\Leftarrow
\text{phase/action gates}
\quad\text{then}\quad
\mathfrak s_{\chi,*}=C_\chi\hbar_I.
$$

Forbidden:

$$
G_N
\Rightarrow
\mathfrak s_{\chi,*}
\Rightarrow
\kappa_{\chi,I}.
$$

If \(C_\chi\) is introduced, it must be a dimensionless kernel/update-count invariant, not a gravitational fit parameter.

Status:

`action_scale_no_fit_gate`

### 43.7. Experimental closure condition

Only after:

$$
\ell_{0,*},z_{I,*},q_{V,*},D_S,
A_{\chi,*},\tau_{\chi,*}
$$

are fixed without gravitational data may the theory compute:

$$
G_I^{(A)}
=
\frac{c_I^4D_S\ell_{0,*}\tau_{\chi,*}}
{2\pi A_{\chi,*}z_{I,*}q_{V,*}}.
$$

The known experimental gate is:

$$
\left|
\frac{G_I^{(A)}-G_N}{G_N}
\right|
\le
\epsilon_G.
$$

Failure is not repaired by changing \(A_{\chi,*}\), \(\tau_{\chi,*}\), or the geometry factors.

It becomes a declared residual:

$$
\mathcal R_G^{(A)}
=
\frac{G_I^{(A)}-G_N}{G_N}.
$$

Status:

`G_gate_after_kappa_action_route`

### 43.8. What is closed

This section closes the form of the update-action route:

$$
\kappa_{\chi,I}^{(A)}
=
\frac{A_{\chi,*}}{\tau_{\chi,*}}.
$$

It does not yet close:

1. numerical \(A_{\chi,*}\);
2. numerical \(\tau_{\chi,*}\);
3. whether \(A_{\chi,*}\) equals \(\hbar_I\), \(2\pi\hbar_I\), or another derived multiple;
4. agreement with the vacuum-response route;
5. numerical \(G_I\).

Next target:

derive or constrain \(A_{\chi,*}\) from the phase/action sector without using gravitational data.

Phase-action kappa gate:

`sections/44-phase-action-kappa-gate.md`

Status:

`kappa_route_form_closed_not_value`
