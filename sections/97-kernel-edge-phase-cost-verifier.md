## 97. Kernel-Edge Phase-Cost Verifier

This section closes the next executable gap:

$$
\rho_{0\to1}^{(\eta)},\rho_1
\Rightarrow
\bar c_K(\eta)
\Rightarrow
\bar C_\gamma^K
\Rightarrow
\lambda_{\theta C}^{(\gamma)}.
$$

Status:

`kernel_edge_phase_cost_verifier_initialized`

### 97.1. Kernel-edge rule

For a finite diagonal transition edge \(\eta:i\to j\), the verifier accepts:

$$
G_{0,\eta}^{\mathrm{diag}},
\qquad
G_{1,\eta}^{\mathrm{diag}},
\qquad
\pi_\eta.
$$

It normalizes the two diagonal positive kernels into probability vectors:

$$
p_0=\frac{G_{0,\eta}^{\mathrm{diag}}}{\sum_kG_{0,\eta,k}},
\qquad
p_1=\frac{G_{1,\eta}^{\mathrm{diag}}}{\sum_kG_{1,\eta,k}},
$$

transports \(p_0\) through the alignment \(\pi_\eta\), and computes:

$$
\bar c_K(\eta)
=
d_B^2(p_{0\to1},p_1)
=
\arccos^2
\left(
\sum_k\sqrt{p_{0\to1,k}p_{1,k}}
\right).
$$

This generated value becomes the edge cost used by the linked phase-cost gate.

Status:

`diagonal_bures_edge_cost_generated`

### 97.2. Closure rule

For each active cycle:

$$
\gamma=i_0i_1\cdots i_N,\qquad i_N=i_0,
$$

the verifier computes:

$$
\bar C_\gamma^K
=
\sum_{r=0}^{N-1}
\bar c_K(i_r\to i_{r+1}),
$$

then tests:

$$
\lambda_{\theta C}^{(\gamma)}
=
\frac{\Theta_\gamma}{\bar C_\gamma^K}.
$$

The same calibration/validation split from Section 96 is reused.

Status:

`kernel_edge_phase_cost_closure_executable`

### 97.3. Current manifest

The current manifest:

`theory_verifier_manifest.json`

contains a toy diagonal kernel-edge family.

Calibration cycle:

$$
\gamma_{\mathrm{cal}}=aba,
\qquad
\bar c_K(a\to b)=\bar c_K(b\to a)=0.10352341925454667,
$$

so:

$$
\bar C_{aba}^K=0.20704683850909334,
\qquad
\Theta_{aba}=0.04140936770181867.
$$

Validation cycle:

$$
\gamma_{\mathrm{val}}=aca,
\qquad
\bar c_K(a\to c)=\bar c_K(c\to a)=0.21496910533216443,
$$

so:

$$
\bar C_{aca}^K=0.42993821066432886,
\qquad
\Theta_{aca}=0.08598764213286577.
$$

Both cycles give:

$$
\lambda_{\theta C}=0.2.
$$

These are still toy values.

The gain is structural: the cycle cost is now computed from kernel data before
the relative phase-cost validation runs.

Status:

`toy_kernel_edge_phase_cost_manifest_registered`

### 97.4. What is closed

Closed:

1. diagonal kernel-strain cost can generate finite edge costs;
2. generated edge costs can feed the cycle cost sum;
3. generated cycle costs can feed \(\lambda_{\theta C}\) validation;
4. invalid kernel alignments are executable failures.

Open:

1. non-diagonal Bures cost;
2. primitive cycle grammar generation;
3. physical action standard \(A_{0,I}\).

Closed by Section 98:

replace declared lifted phases with cycle holonomy phases:

$$
U_\gamma
\Rightarrow
\Theta_\gamma
\Rightarrow
\lambda_{\theta C}^{(\gamma)}.
$$

Status:

`kernel_edge_phase_cost_verifier_closed`
