## 102. Transfer Block Phase Verifier

This section replaces scalar transfer elements with finite matrix contraction
blocks.

The executable chain is now:

$$
X_\eta^\dagger X_\eta\le I
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

`transfer_block_phase_verifier_initialized`

### 102.1. Matrix contraction gate

For each finite transition edge:

$$
\eta:i\to j,
$$

the verifier accepts a square complex matrix:

$$
X_\eta.
$$

It requires:

$$
I-X_\eta^\dagger X_\eta\succeq0.
$$

This is the finite matrix version of the cross-kernel contraction condition.

Status:

`finite_transfer_block_contraction_executable`

### 102.2. Phase readout

For the current finite gate, the transfer phase is the determinant phase:

$$
T_\eta
=
\frac{\det X_\eta}{|\det X_\eta|}.
$$

The verifier rejects singular blocks because the phase is undefined when:

$$
\det X_\eta=0.
$$

This is still a finite toy readout, but it is stricter than scalar transfer
phase because contraction is checked at the matrix level.

Status:

`determinant_phase_readout_executable`

### 102.3. Cycle closure

The cycle holonomy remains:

$$
U_\gamma
=
\prod_{\eta\in\gamma}
T_\eta.
$$

The lifted phase is:

$$
\Theta_\gamma
=
\operatorname{atan2}(\operatorname{Im}U_\gamma,\operatorname{Re}U_\gamma)
+
2\pi n_\gamma.
$$

The cost side remains independently generated from diagonal kernel strain:

$$
\bar C_\gamma^K
=
\sum_{\eta\in\gamma}
d_B^2(\rho_{0\to1}^{(\eta)},\rho_1).
$$

Then:

$$
\lambda_{\theta C}^{(\gamma)}
=
\frac{\Theta_\gamma}{\bar C_\gamma^K}.
$$

Status:

`transfer_block_cost_phase_closure_executable`

### 102.4. Current manifest

The current manifest:

`theory_verifier_manifest_v6_0.json`

contains a toy matrix-block family.

The blocks are diagonal \(2\times2\) contractions whose determinant phases
reproduce the scalar transfer phase from Section 101.

For example:

$$
X_{ab}
=
\begin{pmatrix}
0.7998285325522299+0.01656256367071822i & 0\\
0 & 0.5
\end{pmatrix}.
$$

The determinant phase is unchanged by the positive real second diagonal entry,
but contraction is now checked through:

$$
I-X_{ab}^\dagger X_{ab}\succeq0.
$$

Status:

`toy_transfer_block_manifest_registered`

### 102.5. What is closed

Closed:

1. scalar transfer element is replaced by finite matrix block;
2. transfer block contraction is executable;
3. determinant phase readout feeds the same cycle holonomy gate;
4. non-contraction blocks are executable failures.

Open:

1. non-identity \(G_0,G_1\) normalization into support contraction form;
2. non-diagonal kernel-strain cost;
3. grammar-derived winding;
4. independent action standard \(A_{0,I}\);
5. non-toy calibration/validation family.

Closed by Section 103:

connect transfer blocks to explicit positive block kernels:

$$
\begin{pmatrix}
G_0 & X^\dagger\\
X & G_1
\end{pmatrix}
\succeq0
\Rightarrow
X_\eta^\dagger X_\eta\le I.
$$

Status:

`transfer_block_phase_verifier_closed`
