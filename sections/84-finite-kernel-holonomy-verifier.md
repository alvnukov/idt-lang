## 84. Finite Kernel Holonomy Verifier

This section registers the first finite-model mathematical gates in the executable verifier.

Status:

`finite_kernel_holonomy_verifier_initialized`

### 84.1. PSD kernel gate

The verifier can now check a finite Hermitian kernel:

$$
\Gamma\succeq0.
$$

For small matrices it tests all principal minors.

Failure means the proposed finite kernel is not an admissible positive distinguishability kernel.

Status:

`finite_psd_kernel_gate_executable`

### 84.2. Cross-update block positivity gate

The verifier can now check:

$$
\mathbb G_\eta
=
\begin{pmatrix}
G_0 & X_\eta^\dagger\\
X_\eta & G_1
\end{pmatrix}
\succeq0.
$$

This is the finite gate for admissible before-after coherence.

Failure means the proposed \(X_\eta\) cannot be accepted as a cross-update coherence readout.

Status:

`finite_cross_update_block_psd_gate_executable`

### 84.3. Cycle holonomy gauge gate

The verifier can now check discrete cycle phase invariance under endpoint relabeling:

$$
\mathcal A_{ij}
\mapsto
\mathcal A_{ij}+\alpha_j-\alpha_i.
$$

For a closed cycle:

$$
\gamma=i_0i_1\cdots i_0,
$$

the holonomy phase:

$$
\sum_{(i\to j)\in\gamma}\mathcal A_{ij}
\mod2\pi
$$

must remain invariant.

Status:

`finite_cycle_holonomy_gauge_gate_executable`

### 84.4. Current manifest gates

The current manifest:

`theory_verifier_manifest.json`

contains executable examples for:

1. positive \(\Gamma\);
2. positive cross-update block \(\mathbb G_\eta\);
3. gauge-invariant cycle holonomy.

These are sanity gates.

They are not numerical predictions for \(\hbar_I\) or \(G_I\).

Status:

`finite_gate_manifest_examples_registered`

### 84.5. What is closed

Closed:

1. finite PSD kernel verification;
2. finite cross-update block positivity verification;
3. finite cycle holonomy gauge-invariance verification;
4. negative tests for non-PSD, non-Hermitian, and invalid holonomy inputs.

Open:

1. extraction of finite gates from Markdown;
2. Schur product finite gate in the new verifier package;
3. exact vs non-exact cocycle classifier;
4. contraction norm gate for \(\mathsf C_\eta\);
5. actual finite model for \(\bar C_\gamma\).

Next target:

add exact/non-exact cocycle classification and contraction norm checking:

$$
\|\mathsf C_\eta\|\le1,
\qquad
U_\gamma=1\ \text{or}\ U_\gamma\ne1.
$$

Contraction holonomy classifier:

`sections/85-contraction-holonomy-classifier.md`

Status:

`finite_kernel_holonomy_verifier_closed`
