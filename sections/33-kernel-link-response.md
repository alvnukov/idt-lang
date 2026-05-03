## 33. Kernel Link Response

This section derives the link response variables:

$$
\Omega_\eta,\quad X_\eta,\quad Y_\eta
$$

from deformation of inherited distinguishability.

It corrects the stiffness sign convention by using the cumulant generator:

$$
C_{EF}(s)=\log[Z_{EF}(s)/Z_{EF}(0)].
$$

Status:

`kernel_link_response_initialized`

### 33.1. Link-local kernel update

For a link \(\langle EF\rangle\), let an inherited update \(\eta\) induce a local kernel factor:

$$
K_{\eta,EF}(s)
$$

where:

$$
s=s_{EF}=\varphi(F)-\varphi(E).
$$

The updated distinguishability sector is:

$$
\Gamma_{I,\eta}^{EF}(s)
=
\Gamma_I^{EF}
\circ
K_{\eta,EF}(s)
$$

in the Schur-positive sector.

Admissibility requires:

$$
K_{\eta,EF}(s)\succeq0
$$

for small \(s\), so inherited positivity is preserved.

Status:

`link_kernel_update_defined`

### 33.2. Base weight

The base link weight is the flat-domain contribution:

$$
\Omega_\eta
=
\Omega_{\eta,EF}(0)
>
0.
$$

It may be computed from the local actualization weight:

$$
\Omega_{\eta,EF}(0)
=
\sum_{h,h'\in\mathcal H_{\eta,EF}}
W(h)\overline{W(h')}
\Gamma_I^{EF}(h,h')
K_{\eta,EF}(0;h,h')
$$

only if the result is real positive in the coarse link sector.

If not, the link ensemble must be diagonalized into positive modes before defining \(\Omega_\eta\).

Status:

`base_weight_from_flat_kernel_sector`

### 33.3. Response variable

Define the real link response action:

$$
\Lambda_{\eta,EF}(s)
=
-
\log
\frac{\Omega_{\eta,EF}(s)}
{\Omega_{\eta,EF}(0)}.
$$

Then:

$$
X_\eta
=
\left.
\frac{\partial\Lambda_{\eta,EF}}{\partial s}
\right|_{s=0},
$$

and:

$$
Y_\eta
=
\left.
\frac{\partial^2\Lambda_{\eta,EF}}{\partial s^2}
\right|_{s=0}.
$$

Thus:

$$
\Omega_{\eta,EF}(s)
=
\Omega_\eta
\exp
\left[
-sX_\eta
-\frac12s^2Y_\eta
+O(s^3)
\right].
$$

Status:

`X_eta_from_kernel_log_response`

### 33.4. Link partition and stiffness

The link partition is:

$$
Z_{EF}(s)
=
\sum_{\eta\in\mathcal U_{EF}}
\Omega_{\eta,EF}(s).
$$

The cumulant generator is:

$$
C_{EF}(s)
=
\log
\frac{Z_{EF}(s)}{Z_{EF}(0)}.
$$

Then:

$$
a_{EF}
=
\left.
\frac{\partial^2 C_{EF}}{\partial s^2}
\right|_{s=0}
=
\operatorname{Var}_{EF}(X)
-
\langle Y\rangle_{EF}.
$$

If \(Y_\eta=0\), then:

$$
a_{EF}
=
\operatorname{Var}_{EF}(X).
$$

If \(Y_\eta\neq0\), stability requires:

$$
\operatorname{Var}_{EF}(X)
-
\langle Y\rangle_{EF}
>
0.
$$

Status:

`stiffness_from_kernel_cumulants`

### 33.5. Reciprocity and gauge safety

A reparametrization of the bookkeeping order:

$$
\lambda\mapsto f(\lambda)
$$

may rescale raw clock update rates.

It must not change:

$$
s_{EF}
=
\varphi(F)-\varphi(E),
$$

because \(\varphi=\log\chi\) is defined from clock-rate ratios.

Therefore \(X_\eta\) is admissible only if it responds to \(s_{EF}\), not to raw \(\lambda\)-rates.

Static reciprocity requires:

$$
\mathcal U_{EF}\simeq\mathcal U_{FE},
\qquad
X_{E\to F}=-X_{F\to E}.
$$

Status:

`kernel_response_reparametrization_safe`

### 33.6. What is closed

This section closes:

$$
X_\eta
\quad
\text{as an undefined response variable.}
$$

It replaces it with:

$$
X_\eta
=
\left.
\partial_s
\left[
-
\log
\frac{\Omega_{\eta,EF}(s)}
{\Omega_{\eta,EF}(0)}
\right]
\right|_{s=0}.
$$

It also fixes the sign convention for \(a_{EF}\):

$$
a_{EF}
=
\operatorname{Var}_{EF}(X)-\langle Y\rangle_{EF}.
$$

It does not yet derive:

1. the explicit microscopic kernel \(K_{\eta,EF}(s)\);
2. the positive-mode decomposition for complex sectors;
3. the numerical variance;
4. isotropic coarse-graining;
5. \(G_I\).

Next target:

construct the minimal computable positive link ensemble.

Minimal link ensemble:

`sections/34-minimal-link-ensemble.md`

Status:

`kernel_response_gap_reduced`
