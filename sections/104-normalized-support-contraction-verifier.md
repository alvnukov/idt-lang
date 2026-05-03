## 104. Normalized Support Contraction Verifier

This section moves the transfer phase readout from the raw cross block \(X\) to
the normalized support contraction.

The new executable chain is:

$$
K_\eta=
\begin{pmatrix}
G_0 & X^\dagger\\
X & G_1
\end{pmatrix}
\succeq0
\Rightarrow
C_\eta=G_1^{-1/2}XG_0^{-1/2}
\Rightarrow
T_\eta
\Rightarrow
\lambda_{\theta C}^{(\gamma)}.
$$

Status:

`normalized_support_contraction_verifier_initialized`

### 104.1. Diagonal support normalization

The current finite gate handles the diagonal-support case:

$$
G_0=\operatorname{diag}(g_{0,1},\ldots,g_{0,n}),
\qquad
G_1=\operatorname{diag}(g_{1,1},\ldots,g_{1,n}),
$$

with:

$$
g_{0,k}>0,\qquad g_{1,k}>0.
$$

It computes:

$$
C_{ij}
=
\frac{X_{ij}}{\sqrt{g_{1,i}g_{0,j}}}.
$$

Then it checks:

$$
C^\dagger C\le I.
$$

Status:

`diagonal_support_normalization_executable`

### 104.2. Phase readout

The finite phase readout is now:

$$
T_\eta
=
\frac{\det C_\eta}{|\det C_\eta|}.
$$

This matters because raw \(X\) contains support-scale factors. Those factors
should not affect the transfer phase.

Status:

`support_contraction_phase_readout_executable`

### 104.3. Current manifest

The current manifest:

`theory_verifier_manifest_v6_0.json`

contains a toy non-identity support example:

$$
G_0=\operatorname{diag}(2,3),
\qquad
G_1=\operatorname{diag}(5,7).
$$

The cross block \(X\) is larger than the corresponding normalized contraction
because it carries the \(\sqrt{G_1}\) and \(\sqrt{G_0}\) factors.

After normalization, the same transfer phases used in Sections 101-103 are
recovered.

Status:

`toy_normalized_support_manifest_registered`

### 104.4. What is closed

Closed:

1. non-identity diagonal supports are executable;
2. transfer phase is read from \(C\), not raw \(X\);
3. block-kernel positivity is checked before normalization;
4. support-normalized validation failures are executable.

Open:

1. larger matrix spectral support;
2. pseudoinverse support handling for rank-deficient kernels;
3. non-diagonal kernel-strain cost;
4. grammar-derived winding;
5. independent action standard \(A_{0,I}\);
6. non-toy calibration/validation family.

Closed by Section 105:

generalize from diagonal support to spectral support:

$$
G_a=V_aD_aV_a^\dagger,
\qquad
C=G_1^{-1/2}XG_0^{-1/2}.
$$

Status:

`normalized_support_contraction_verifier_closed`
