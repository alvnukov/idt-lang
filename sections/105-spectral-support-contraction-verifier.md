## 105. Spectral Support Contraction Verifier

This section extends support normalization beyond diagonal supports.

The executable chain is:

$$
G_a=V_aD_aV_a^\dagger
\Rightarrow
G_a^{-1/2}
\Rightarrow
C=G_1^{-1/2}XG_0^{-1/2}
\Rightarrow
T_\eta
\Rightarrow
\lambda_{\theta C}^{(\gamma)}.
$$

Status:

`spectral_support_contraction_verifier_initialized`

### 105.1. Finite spectral scope

The current gate deliberately supports only:

1. \(1\times1\) Hermitian positive definite supports;
2. \(2\times2\) Hermitian positive definite supports.

It rejects rank-deficient supports because pseudoinverse support handling is a
separate problem.

Status:

`finite_2x2_spectral_support_scope_defined`

### 105.2. Spectral inverse square root

For a Hermitian positive definite support:

$$
G=VDV^\dagger,
$$

the verifier computes:

$$
G^{-1/2}=VD^{-1/2}V^\dagger.
$$

For \(2\times2\) matrices this is implemented through the two eigenvalues and
the spectral functional calculus, not by assuming diagonal form.

Status:

`spectral_inverse_square_root_executable`

### 105.3. Transfer phase readout

The normalized support contraction is:

$$
C_\eta=G_1^{-1/2}X_\eta G_0^{-1/2}.
$$

Then:

$$
T_\eta
=
\frac{\det C_\eta}{|\det C_\eta|}.
$$

The verifier also checks the full block kernel:

$$
\begin{pmatrix}
G_0 & X^\dagger\\
X & G_1
\end{pmatrix}
\succeq0.
$$

Status:

`spectral_support_phase_readout_executable`

### 105.4. Current manifest

The current manifest:

`theory_verifier_manifest.json`

contains a toy non-diagonal support:

$$
G_0=G_1=
\begin{pmatrix}
2 & 0.4\\
0.4 & 3
\end{pmatrix}.
$$

The cross blocks are built as:

$$
X=G^{1/2}CG^{1/2}
$$

for contraction phases chosen to reproduce the previous toy cycle slopes.

Status:

`toy_spectral_support_manifest_registered`

### 105.5. What is closed

Closed:

1. non-diagonal \(2\times2\) Hermitian supports are executable;
2. phase is read from \(C=G_1^{-1/2}XG_0^{-1/2}\);
3. singular support is an executable failure;
4. block-kernel positivity is checked before phase readout.

Open:

1. larger matrix spectral support;
2. pseudoinverse support handling;
3. non-diagonal kernel-strain cost beyond the finite \(2\times2\) executable gate;
4. grammar-derived winding;
5. independent action standard \(A_{0,I}\);
6. non-toy calibration/validation family.

Closed by Section 106 for the finite \(2\times2\) scope:

the verifier now computes non-diagonal kernel-strain cost:

$$
\rho_{0\to1}^{(\eta)},\rho_1
\Rightarrow
d_B^2(\rho_{0\to1}^{(\eta)},\rho_1)
$$

without restricting \(\rho\) to diagonal distributions, and uses the same
spectral block to extract the cycle phase.

Status:

`spectral_support_contraction_verifier_closed`
