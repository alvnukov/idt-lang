## 42. Geometry Input Front Status

This section updates the weak-gravity front after reducing the geometric inputs:

$$
\ell_0,\qquad z_I,\qquad q_{V,I}.
$$

Status:

`geometry_input_front_status_initialized`

### 42.1. Current reduced inputs

The current non-gravitational geometry inputs are:

$$
\ell_0(A,B)
=
\frac{c_I\Delta\tau_{ABA}}{2w_S(A,B)}
$$

in a flat local clock-radar calibration domain,

$$
z_I(U)=\frac{2N_L(U)}{N_E(U)},
$$

and:

$$
q_{V,I}(U)
=
\frac{\ell_0^3}{\langle V\rangle_U}.
$$

These are not numerical predictions yet.

They are readout definitions that remove three adjustable placeholders from the weak-gravity formula.

Status:

`geometry_inputs_reduced_not_numerical`

### 42.2. Weak-gravity expression after geometry reduction

In the minimal normalized positive-kernel sector:

$$
x_0=1.
$$

The weak-gravity expression becomes:

$$
G_I(U)
=
\frac{c_I^4D_S\ell_0(U)}
{2\pi\kappa_{\chi,I}z_I(U)q_{V,I}(U)}.
$$

In a stable isotropic flat sector:

$$
\ell_0(U)\to\ell_{0,*},
\qquad
z_I(U)\to z_{I,*},
\qquad
q_{V,I}(U)\to q_{V,*},
$$

so:

$$
G_I
=
\frac{c_I^4D_S\ell_{0,*}}
{2\pi\kappa_{\chi,I}z_{I,*}q_{V,*}}.
$$

Status:

`weak_gravity_expression_geometry_reduced`

### 42.3. Required stability residuals

Before comparing with \(G_N\), the following residuals must be declared:

$$
\mathcal R_\ell(U)
=
\frac{\ell_0(U)-\ell_{0,*}}{\ell_{0,*}},
$$

$$
\mathcal R_z(U)
=
\frac{z_I(U)-z_{I,*}}{z_{I,*}},
$$

$$
\mathcal R_q(U)
=
\frac{q_{V,I}(U)-q_{V,*}}{q_{V,*}},
$$

and:

$$
\mathcal R_Q^{ij}(U)
=
Q_I^{ij}(U)-\frac{1}{D_S}h^{ij}.
$$

Predictive use requires:

$$
|\mathcal R_\ell|,
|\mathcal R_z|,
|\mathcal R_q|,
\|\mathcal R_Q\|
\le
\epsilon_{\mathrm{geom}}
$$

in the calibration domain.

Status:

`geometry_stability_gate_declared`

### 42.4. Experimental gates not used for fitting

The geometry inputs must be fixed before these known weak-field gates:

| Gate | Known formula |
|---|---|
| gravitational redshift | \(\Delta\nu/\nu\simeq\Delta\Phi/c_I^2\) |
| slow-body free fall | \(\ddot x=-\nabla\Phi\) |
| Newtonian source law | \(\nabla^2\Phi=4\pi G_N\rho_m\) |
| light bending PPN gate | \(\Delta\theta=(1+\gamma_I^{\mathrm{PPN}})2G_NM/(c_I^2b)\) |
| GR light-bending target | \(\Delta\theta=4G_NM/(c_I^2b)\) when \(\gamma_I^{\mathrm{PPN}}=1\) |

These gates are not axioms of the theory.

They are external experimental filters.

If the inherited readout predicts a controlled residual, it must be declared before comparison.

Status:

`known_gates_external_not_fit_targets`

### 42.5. What is now closed

Closed as readout reductions:

1. \(\ell_0\) as clock-radar distance per order-distance unit;
2. \(z_I\) as mean spatial adjacency degree;
3. \(q_{V,I}\) as cell-volume shape factor;
4. \(n_L\ell_0^2=z_Iq_{V,I}/(2\ell_0)\).

Not closed:

1. exact \(D_S=3\);
2. exact regular geometry class;
3. exact isotropy;
4. global constancy of \(\ell_0,z_I,q_{V,I}\);
5. physical cost scale \(\kappa_{\chi,I}\);
6. numerical \(G_I\).

Status:

`geometry_inputs_closed_as_readout_only`

### 42.6. Next hard input

After geometry reduction, the only remaining dimensional physical input in:

$$
G_I
=
\frac{c_I^4D_S\ell_{0,*}}
{2\pi\kappa_{\chi,I}z_{I,*}q_{V,*}}
$$

is:

$$
\kappa_{\chi,I}.
$$

Therefore the next strongest route is:

$$
\kappa_{\chi,I}
\Leftarrow
\text{update-action cost}
$$

or independently:

$$
\kappa_{\chi,I}
\Leftarrow
\text{clock-vacuum response}.
$$

Agreement between the two routes would be a non-fit internal closure.

Update-action route:

`sections/43-update-action-kappa-route.md`

Status:

`kappa_is_next_hard_input`
