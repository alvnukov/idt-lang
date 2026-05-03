## 5. Proto-GR Reconstruction

GR is not yet derived.
Current status:

`reconstruction_mechanism_with_known_gates`

not:

`completed_GR_derivation`

### 5.1. Local interval tensor

Fit local tensor:

$$
D_G(A,B)
\approx
G_{\mu\nu}(E)\Delta x^\mu_{AB}\Delta x^\nu_{AB}
$$

Signature gate:

$$
\mathrm{sig}(G)=(+---)
$$

Continuum target:

$$
G_{\mu\nu}(E)\to g_{\mu\nu}(x)
$$

### 5.2. Connection

Frame transport:

$$
T_{E\to F}^TG(F)T_{E\to F}
\approx
G(E)
$$

Infinitesimal readout:

$$
T_{E\to F}
=
I-\Gamma_\rho(E;F)\Delta x^\rho+O(\Delta x^2)
$$

This defines:

$$
\Gamma^\mu_{\nu\rho}
$$

### 5.3. Curvature

Loop holonomy:

$$
H_\Box
=
T_{E_3\to E_0}
T_{E_2\to E_3}
T_{E_1\to E_2}
T_{E_0\to E_1}
$$

Flatness:

$$
H_\Box=I
$$

Curvature:

$$
H_\Box=I+\mathcal R_I(\Box)+O(\mathrm{area}^{3/2})
$$

Continuum target:

$$
\mathcal R_I\to R^\mu_{\ \nu\rho\sigma}
$$

### 5.4. Source

Inheritance activity in region \(U\):

$$
\mathcal N_I(U)
=
\sum_{\eta:\mathrm{supp}(\eta)\subset U}\omega_\eta
$$

This is uncalibrated inherited activity count/weight.

Source-weighted activity in a spatial clock slice \(S\):

$$
M_I(U)
=
\sum_{\eta\in U}m_I(\eta).
$$

After volume reconstruction, define geometric spatial source density:

$$
\rho_I^G(E)
=
\lim_{U\to E}
\frac{M_I(U)}{\nu_{G,S}(U)}
$$

where \(\nu_{G,S}\) is reconstructed geometric volume on the clock slice.

Counting density:

$$
\rho_I^{\mathrm{count}}(U)
=
\frac{\mathcal N_I(U)}{\nu_{\mathrm{count}}(U)}
$$

is not yet a geometric source density.

Directional flow:

$$
J_I^\mu(E)
$$

Second moment:

$$
\Pi_I^{\mu\nu}(E)
=
\langle\omega_\eta u_\eta^\mu u_\eta^\nu\rangle_E
$$

Proto stress-energy target:

$$
T_I^{\mu\nu}
$$

with:

$$
\nabla_\mu T_I^{\mu\nu}=0
$$

### 5.5. Proto field equation

$$
\mathcal E_I[G]=\kappa_I T_I
$$

Einstein fixed point:

$$
\mathcal E_I[G]
\to
R_{\mu\nu}
-\frac12Rg_{\mu\nu}
+\Lambda g_{\mu\nu}
$$

$$
\kappa_I T_I
\to
\frac{8\pi G_N}{c^4}T_{\mu\nu}
$$

---
