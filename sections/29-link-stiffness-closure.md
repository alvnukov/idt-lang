## 29. Link Stiffness Closure

This section begins closing:

$$
a_{EF}
\Rightarrow
\alpha_I
\Rightarrow
G_I.
$$

It does not insert \(G_N\).

It defines \(a_{EF}\) as a primitive response coefficient of inherited clock-link updates.

Status:

`link_stiffness_closure_initialized`

### 29.1. Link update ensemble

For a neighbouring readout link \(\langle EF\rangle\), let:

$$
\mathcal U_{EF}
$$

be the set of inherited updates whose support couples the two local clock cells.

Let each update \(\eta\in\mathcal U_{EF}\) have:

1. base weight \(\Omega_\eta>0\);
2. clock-strain response variable \(X_\eta\);
3. higher response variables \(Y_\eta,\ldots\).

For:

$$
s_{EF}
=
\varphi(F)-\varphi(E),
$$

define the local link response partition:

$$
Z_{EF}(s)
=
\sum_{\eta\in\mathcal U_{EF}}
\Omega_\eta
\exp[-sX_\eta+O(s^2Y_\eta)].
$$

The link stiffness uses the cumulant generator:

$$
C_{EF}(s)
=
\log
\frac{Z_{EF}(s)}{Z_{EF}(0)}.
$$

Status:

`link_response_partition_defined`

### 29.2. Stiffness as response variance

The clock-link stiffness is:

$$
a_{EF}
=
\left.
\frac{\partial^2 C_{EF}}{\partial s^2}
\right|_{s=0}.
$$

If the linear mean response vanishes in the flat vacuum:

$$
\langle X\rangle_{EF}=0,
$$

then:

$$
a_{EF}
=
\operatorname{Var}_{EF}(X)
-
\langle Y\rangle_{EF}
$$

up to the chosen second-order response convention.

In the minimal quadratic-response sector:

$$
Y_\eta=0
\Rightarrow
a_{EF}
=
\operatorname{Var}_{EF}(X)
\ge0.
$$

Thus positive stiffness is not an independent sign assumption.

It follows from stability of the flat inherited link ensemble.

Status:

`a_EF_as_link_response_variance`

### 29.3. Reciprocity gate

Static reciprocity requires:

$$
\mathcal U_{EF}
\simeq
\mathcal U_{FE}
$$

and:

$$
X_{\eta,E\to F}
=
-
X_{\eta,F\to E}.
$$

Then:

$$
C_{EF}(s)=C_{FE}(-s),
$$

so the linear term cancels in the unoriented static link cost.

This supports the absence of a vacuum force when:

$$
\rho_I^G=0.
$$

Status:

`static_reciprocity_supports_flat_vacuum`

### 29.4. Coarse-graining to alpha

The stiffness tensor from section 26 becomes:

$$
A_I^{ij}(U)
=
\frac{1}{\nu_{G,S}(U)}
\sum_{\langle EF\rangle\subset U}
\operatorname{Var}_{EF}(X)
\ell_{EF}^i\ell_{EF}^j
$$

in the minimal response sector.

The isotropic fixed point requires:

$$
A_I^{ij}
\to
\alpha_Ih^{ij}.
$$

Therefore:

$$
\alpha_I
=
\frac{1}{D_S}
h_{ij}
\frac{1}{\nu_{G,S}(U)}
\sum_{\langle EF\rangle\subset U}
\operatorname{Var}_{EF}(X)
\ell_{EF}^i\ell_{EF}^j.
$$

This is the first non-fitted expression for \(\alpha_I\), conditional on the link ensemble.

Status:

`alpha_from_link_response_variance`

### 29.5. Predictive gate for G

Once the link ensemble is fixed without gravitational data:

$$
\mathcal U_{EF},\Omega_\eta,X_\eta
\Rightarrow
\alpha_I
\Rightarrow
G_I
=
\frac{c_I^4}{4\pi\alpha_I}.
$$

Acceptance requires:

$$
\left|
\frac{G_I-G_N}{G_N}
\right|
\le
\epsilon_G
$$

with \(\epsilon_G\) declared in the experimental gate ledger.

No part of:

$$
G_N
$$

may enter \(\Omega_\eta\), \(X_\eta\), \(\ell_{EF}\), or \(\nu_{G,S}\).

Status:

`G_no_input_prediction_gate`

### 29.6. Failure modes

The route fails if:

1. \(a_{EF}\) must be chosen independently for each gravitational gate;
2. \(\operatorname{Var}_{EF}(X)\) has no primitive definition;
3. isotropic coarse-graining requires inserting \(\alpha_I\) by hand;
4. \(G_N\) enters the link ensemble under another name;
5. the same \(\alpha_I\) cannot pass local, orbital, and lensing gates.

Status:

`link_stiffness_failure_modes_declared`

### 29.7. What is closed

This section closes:

$$
a_{EF}
\quad
\text{as an arbitrary edge coefficient.}
$$

It replaces it with:

$$
a_{EF}
=
\left.
\frac{\partial^2}{\partial s^2}
\left[
\log
\frac{Z_{EF}(s)}{Z_{EF}(0)}
\right]
\right|_{s=0}.
$$

It does not yet derive:

1. the microscopic distribution \(\Omega_\eta\);
2. the response variable \(X_\eta\) from \(\Gamma_I\);
3. numerical \(G_I\);
4. isotropic fixed point from first principles;
5. coupling to matter calibration.

Next target:

derive \(X_\eta\) from the same update action that sets clock-rate and source response.

Kernel link response:

`sections/33-kernel-link-response.md`

Status:

`a_EF_arbitrariness_reduced`
