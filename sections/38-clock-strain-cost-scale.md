## 38. Clock-Strain Cost Scale

This section localizes:

$$
\kappa_{\chi,I}.
$$

It is the physical cost scale that converts dimensionless kernel stiffness into physical vacuum stiffness.

It is not derived numerically here.

Status:

`clock_strain_cost_scale_initialized`

### 38.1. Why kappa is necessary

The normalized kernel model gives:

$$
\bar a_{EF}=1
$$

in the minimal sector.

But \(\alpha_I\) has physical units:

$$
[\alpha_I]
=
\frac{c^4}{G}
$$

in the Newtonian readout.

Therefore a physical cost scale is required:

$$
a_{EF}^{\mathrm{phys}}
=
\kappa_{\chi,I}\bar a_{EF}.
$$

Status:

`dimensionful_scale_required`

### 38.2. Update-action route

Let an inherited update have primitive action cost:

$$
\mathfrak s_I(\eta).
$$

Let a local clock cycle have readout duration:

$$
\tau_{\chi,I}.
$$

Then a candidate clock-strain energy scale is:

$$
\kappa_{\chi,I}
\sim
\frac{\mathfrak s_{\chi,I}}{\tau_{\chi,I}}.
$$

This is only a route, not a derivation, until:

$$
\mathfrak s_{\chi,I},
\qquad
\tau_{\chi,I}
$$

are obtained from primitive inheritance and clock readout without using \(G_N\).

Status:

`update_action_route_to_kappa`

### 38.3. Vacuum-response route

Alternatively, define \(\kappa_{\chi,I}\) as the flat-vacuum second response of the clock network:

$$
\kappa_{\chi,I}
=
\left.
\frac{\partial^2 E_{\mathrm{vac},I}}
{\partial \bar s^2}
\right|_{\bar s=0},
$$

where \(\bar s\) is normalized dimensionless clock strain and \(E_{\mathrm{vac},I}\) is the energy readout of the inherited vacuum sector.

This route requires an independent energy readout.

It cannot be fixed by demanding:

$$
\kappa_{\chi,I}
=
\frac{c_I^4D_S}
{4\pi G_Nn_Lx_0^2\ell_0^2}.
$$

Status:

`vacuum_response_route_to_kappa`

### 38.4. Relation to hbar

If the update-action route uses:

$$
\mathfrak s_{\chi,I}
\sim
\hbar_I,
$$

then \(\hbar_I\) must already be fixed by the action-phase sector without gravitational data.

Otherwise the route would only move the calibration from \(G_N\) to \(\hbar_I\).

Allowed:

$$
\hbar_I
\text{ fixed by phase/action gates}
\Rightarrow
\kappa_{\chi,I}
$$

Forbidden:

$$
G_N
\Rightarrow
\kappa_{\chi,I}
\Rightarrow
\hbar_I.
$$

Status:

`kappa_hbar_dependency_controlled`

### 38.5. Symbolic G after geometry reduction

From section 37:

$$
n_L\ell_0^2
=
\frac{z_Iq_{V,I}}{2\ell_0}.
$$

With \(x_0=1\):

$$
G_I
=
\frac{c_I^4D_S\ell_0}
{2\pi\kappa_{\chi,I}z_Iq_{V,I}}.
$$

Thus \(G_I\) will be predicted only after:

$$
\kappa_{\chi,I},
\ell_0,
z_I,
q_{V,I},
D_S
$$

are fixed without gravitational input.

Status:

`G_reduced_to_kappa_and_order_geometry`

### 38.6. Kappa residual

Define:

$$
\mathcal R_\kappa
=
\frac{\kappa_{\chi,I}^{\mathrm{route\ A}}
-
\kappa_{\chi,I}^{\mathrm{route\ B}}}
{\kappa_{\chi,I}^{\mathrm{route\ A}}}.
$$

If update-action and vacuum-response routes disagree, the theory has a physical residual, not a free parameter.

Status:

`kappa_route_residual_defined`

### 38.7. What is closed

This section closes:

$$
\kappa_{\chi,I}
\quad
\text{as a hidden }G_N\text{ container}.
$$

It replaces it with two declared routes:

1. update-action route;
2. clock-vacuum response route.

It does not yet derive:

1. \(\mathfrak s_{\chi,I}\);
2. \(\tau_{\chi,I}\);
3. \(E_{\mathrm{vac},I}\);
4. numerical \(\kappa_{\chi,I}\);
5. numerical \(G_I\).

Next target:

choose whether to close \(\kappa_{\chi,I}\) through update action or through clock-vacuum response.

Weak-gravity front status:

`sections/39-weak-gravity-front-status.md`

Update-action kappa route:

`sections/43-update-action-kappa-route.md`

Clock-vacuum pole route:

`sections/58-clock-vacuum-pole-route.md`

Status:

`kappa_gap_localized`
