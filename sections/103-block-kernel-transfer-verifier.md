## 103. Block Kernel Transfer Verifier

This section connects transfer phase readout to an explicit positive block
kernel.

The executable chain is now:

$$
\begin{pmatrix}
G_0 & X^\dagger\\
X & G_1
\end{pmatrix}
\succeq0
\Rightarrow
X_\eta
\Rightarrow
T_\eta
\Rightarrow
U_\gamma
\Rightarrow
\Theta_\gamma
\Rightarrow
\lambda_{\theta C}^{(\gamma)}.
$$

Status:

`block_kernel_transfer_verifier_initialized`

### 103.1. Positive block kernel gate

For each finite transition edge \(\eta\), the verifier accepts:

$$
G_0,\quad G_1,\quad X.
$$

It constructs:

$$
K_\eta
=
\begin{pmatrix}
G_0 & X^\dagger\\
X & G_1
\end{pmatrix}
$$

and requires:

$$
K_\eta\succeq0.
$$

This is the finite executable form of the cross-kernel positivity condition.

Status:

`finite_block_kernel_psd_gate_executable`

### 103.2. Transfer phase readout

For the current finite gate, the transfer phase is still:

$$
T_\eta
=
\frac{\det X}{|\det X|}.
$$

But now \(X\) is not accepted alone. It is accepted only inside a positive block
kernel.

For identity \(G_0,G_1\), this implies the usual contraction condition:

$$
X^\dagger X\le I.
$$

Status:

`block_kernel_to_transfer_phase_executable`

### 103.3. Current manifest

The current manifest:

`theory_verifier_manifest_v6_0.json`

contains a toy block-kernel family with:

$$
G_0=G_1=I_2,
$$

and diagonal \(X\)-blocks matching Section 102.

The gate rejects:

1. non-positive block kernels;
2. singular phase blocks;
3. failed \(\lambda_{\theta C}\) validation.

Status:

`toy_block_kernel_transfer_manifest_registered`

### 103.4. What is closed

Closed:

1. transfer \(X\) is now embedded in an explicit positive block kernel;
2. block-kernel positivity is executable;
3. determinant phase readout remains connected to cycle holonomy;
4. non-positive block kernels are executable failures.

Open:

1. full non-diagonal square-root normalization;
2. non-diagonal kernel-strain cost;
3. grammar-derived winding;
4. independent action standard \(A_{0,I}\);
5. non-toy calibration/validation family.

Closed by Section 104:

derive the transfer phase from the normalized support contraction:

$$
X
=
G_1^{1/2}CG_0^{1/2},
\qquad
C^\dagger C\le I.
$$

Status:

`block_kernel_transfer_verifier_closed`
