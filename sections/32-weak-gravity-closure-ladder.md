## 32. Weak-Gravity Closure Ladder

This section joins the adjacent weak-gravity routes into one closure ladder.

It is the current shortest route from Mode B readiness to Mode C predictive value.

Status:

`weak_gravity_closure_ladder_initialized`

### 32.1. Ordered closure chain

The closure chain is:

$$
\mathcal U_{EF},\Omega_\eta,X_\eta
\Rightarrow
a_{EF}
\Rightarrow
\alpha_I
\Rightarrow
G_I
$$

together with:

$$
\mathcal K_P
\Rightarrow
q_{\Phi,I}(P)
\Rightarrow
\sigma_{\Phi,I}^G
\Rightarrow
\rho_{\mathrm{kin},I}c_I^2
$$

and:

$$
\nu_{\mathrm{count}}
\Rightarrow
\lambda_I^{(d)}
\Rightarrow
\nu_{G,S},\nu_G^{(4)}.
$$

Only after all three chains are fixed may the weak source equation be compared to Newtonian data.

Status:

`ordered_weak_gravity_chain_defined`

### 32.2. No hidden input rule

The following cannot be used as primitive inputs:

$$
G_N,\quad
\rho_m,\quad
\nu_G,\quad
\alpha_I.
$$

They may appear only as:

1. validated comparison targets;
2. reconstructed readouts;
3. calibrated outputs from previously declared routes.

If any of them enters \(\mathcal U_{EF}\), \(\Omega_\eta\), \(X_\eta\), \(\mathcal K_P\), or \(\lambda_I\), the closure is invalid.

Status:

`no_hidden_gravity_input_rule`

### 32.3. Closure equations

Link stiffness:

$$
a_{EF}
=
\operatorname{Var}_{EF}(X)
$$

in the minimal response sector.

Vacuum stiffness:

$$
\alpha_I
=
\frac{1}{D_S}
h_{ij}
\frac{1}{\nu_{G,S}(U)}
\sum_{\langle EF\rangle\subset U}
a_{EF}\ell_{EF}^i\ell_{EF}^j.
$$

Matter calibration:

$$
\sigma_{\Phi,I}^G
=
\rho_{\mathrm{kin},I}c_I^2.
$$

Newtonian output:

$$
G_I
=
\frac{c_I^4}{4\pi\alpha_I}.
$$

Weak source equation:

$$
\Delta_S\Phi_I
=
4\pi G_I\rho_{\mathrm{kin},I}.
$$

Status:

`weak_gravity_closure_equations_collected`

### 32.4. Gate order

The gate order is:

1. clock universality and \(\lambda\)-gauge;
2. volume/dimension stability;
3. link stiffness closure;
4. matter calibration closure;
5. Newtonian source/free-fall gate;
6. WEP active/passive/source gate;
7. spatial curvature \(\gamma_I^{\mathrm{PPN}}\to1\);
8. light bending/Shapiro/perihelion gates;
9. residual windows for dark-sector phenomena.

No later gate may be used to adjust an earlier closure.

Status:

`weak_gravity_gate_order_defined`

### 32.5. Residual packet

The weak-gravity closure residual packet is:

$$
\mathcal R_{\mathrm{WG}}
=
\left(
\mathcal R_\lambda,
\mathcal R_A^{ij},
\epsilon_{\mathrm{EP},I},
\mathcal R_G,
\mathcal R_\gamma,
\mathcal R_{\mathrm{slip}}
\right).
$$

Mode C requires either:

1. all residuals are below declared \(\epsilon_k\); or
2. at least one residual has fixed sign/form before comparison and survives independent gates.

Status:

`weak_gravity_residual_packet_defined`

### 32.6. Mode C readiness condition

Mode C readiness for the weak-gravity route requires:

$$
N_{\mathrm{pred}}
=
N_{\mathrm{independent\ weak\ gravity\ gates}}
-
N_{\mathrm{free\ weak\ gravity\ closures}}
-
N_{\mathrm{unit\ conventions}}
>
0.
$$

Minimum candidate:

1. calibrate no gravitational constant from Newtonian data;
2. compute \(\alpha_I\) from link response;
3. compute matter calibration from packet generator;
4. compute \(\lambda_I\) from order/count data;
5. compare \(G_I\), WEP, redshift/free-fall, and lensing gates without refit.

Status:

`weak_gravity_mode_C_condition`

### 32.7. What is closed

This section closes the cluster architecture:

$$
\{a_{EF},\alpha_I,\sigma_{\Phi,I}^G,\lambda_I\}
\Rightarrow
\text{one weak-gravity closure ladder}.
$$

It does not yet provide:

1. numerical \(G_I\);
2. exact \(\gamma_I^{\mathrm{PPN}}=1\);
3. exact \(D_G=4\);
4. exact matter spectrum;
5. populated experimental tolerances.

Next target:

choose the first closure input to compute:

$$
\mathcal U_{EF},\Omega_\eta,X_\eta
$$

or:

$$
\mathcal K_P.
$$

Status:

`weak_gravity_cluster_integrated`
