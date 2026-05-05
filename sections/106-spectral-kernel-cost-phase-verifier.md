## 106. Spectral Kernel Cost-Phase Verifier

This section closes a local split in the executable clock route.

Before this gate, the verifier could read phase from a non-diagonal spectral
block:

$$
C_\eta=G_1^{-1/2}X_\eta G_0^{-1/2},
\qquad
T_\eta=\frac{\det C_\eta}{|\det C_\eta|},
$$

but the cycle cost still came from a separate diagonal kernel ledger. That was
not acceptable as a predictive closure step: phase and cost had different data
sources.

Status:

`spectral_kernel_cost_phase_split_closed`

### 106.1. Common finite input

The new finite input for each edge is one block kernel:

$$
\mathcal K_\eta=
\begin{pmatrix}
G_0 & X_\eta^\dagger\\
X_\eta & G_1
\end{pmatrix}
\succeq0,
$$

with \(G_0,G_1\) Hermitian positive definite and currently restricted to
\(1\times1\) or \(2\times2\).

The same block yields:

1. a normalized support contraction \(C_\eta\);
2. a unit phase \(T_\eta\);
3. a transported density \(\rho_{0\to1}^{(\eta)}\);
4. a Bures strain cost \(\bar c_K(\eta)\).

Status:

`single_spectral_block_input_defined`

### 106.2. Transported density

Define:

$$
\rho_0=\frac{G_0}{\operatorname{tr}G_0},
\qquad
\rho_1=\frac{G_1}{\operatorname{tr}G_1}.
$$

The edge transports the first density through the normalized contraction:

$$
\tilde\rho_{0\to1}^{(\eta)}
=
C_\eta\rho_0 C_\eta^\dagger,
\qquad
\rho_{0\to1}^{(\eta)}
=
\frac{\tilde\rho_{0\to1}^{(\eta)}}
{\operatorname{tr}\tilde\rho_{0\to1}^{(\eta)}}.
$$

Uniform loss therefore does not count as shape strain; only the normalized
readout deformation does.

Status:

`transported_density_readout_defined`

### 106.3. Non-diagonal Bures cost

For \(2\times2\) density matrices the verifier uses the standard qubit root
fidelity formula:

$$
F_R(\rho,\sigma)
=
\sqrt{
\operatorname{tr}(\rho\sigma)
+2\sqrt{\det\rho\,\det\sigma}
}.
$$

The dimensionless edge cost is:

$$
\bar c_K(\eta)
=
\arccos^2
\left[
F_R
\left(
\rho_{0\to1}^{(\eta)},\rho_1
\right)
\right].
$$

This reduces to the earlier diagonal Bhattacharyya/Bures expression when both
density matrices commute.

Status:

`non_diagonal_bures_cost_executable`

### 106.4. Cost-phase cycle closure

For a cycle:

$$
\gamma=(E_0\to E_1\to\cdots\to E_0),
$$

the verifier now computes:

$$
\bar C_\gamma^K
=
\sum_{\eta\in\gamma}\bar c_K(\eta),
\qquad
U_\gamma
=
\prod_{\eta\in\gamma}T_\eta,
\qquad
\Theta_\gamma=\arg(U_\gamma)+2\pi n_\gamma.
$$

The same relative closure gate is then applied:

$$
\lambda_{\theta C}^{(\gamma)}
=
\frac{\Theta_\gamma}{\bar C_\gamma^K}.
$$

There is no copied cost field and no copied phase field in the active gate.

Status:

`same_block_phase_cost_closure_executable`

### 106.5. Current manifest

The current manifest:

`theory_verifier_manifest.json`

adds two finite gates:

1. `spectral_kernel_strain_cost_demo`;
2. `phase_cost_from_spectral_kernel_blocks_demo`.

The second gate computes calibration and validation slopes entirely from
non-diagonal \(G_0,G_1,X\) blocks. A failure in the same gate can now come from:

1. non-PSD block kernel;
2. singular support;
3. non-PSD transported density;
4. Bures cost mismatch;
5. phase-cost validation residual.

Status:

`spectral_kernel_cost_phase_manifest_registered`

### 106.6. Remaining limits

This is still a finite verifier gate, not a continuum theorem.

Open:

1. \(n>2\) density fidelity;
2. pseudoinverse support for rank-deficient sectors;
3. grammar-derived winding \(n_\gamma\);
4. non-toy experimental calibration family;
5. independent action standard \(A_{0,I}\).

Status:

`spectral_kernel_cost_phase_verifier_closed`
