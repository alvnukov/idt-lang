## 98. Holonomy Phase-Cost Verifier

This section removes the next manual field from the finite \(\hbar\)-route
machinery.

The previous executable chain computed:

$$
\bar c_K(\eta)
\Rightarrow
\bar C_\gamma^K,
$$

but still declared \(\Theta_\gamma\) directly.

The new gate computes both sides of the dimensionless slope test:

$$
\rho_{0\to1}^{(\eta)},\rho_1
\Rightarrow
\bar c_K(\eta)
\Rightarrow
\bar C_\gamma^K,
\qquad
\alpha_\eta
\Rightarrow
\Theta_\gamma.
$$

Status:

`holonomy_phase_cost_verifier_initialized`

### 98.1. Phase ledger

The verifier accepts a finite phase-edge ledger:

$$
(i\to j)\mapsto\alpha_{ij}.
$$

For a cycle:

$$
\gamma=i_0i_1\cdots i_N,\qquad i_N=i_0,
$$

it computes:

$$
\Theta_\gamma
=
\sum_{r=0}^{N-1}
\alpha_{i_ri_{r+1}}
+
2\pi n_\gamma.
$$

For the current finite gate, the supported branch sources are:

1. `principal`, with \(n_\gamma=0\);
2. `winding`, with explicitly declared integer \(n_\gamma\).

The gate does not yet infer winding from primitive grammar.

Status:

`finite_holonomy_phase_lift_executable`

### 98.2. Combined slope test

The same gate computes:

$$
\bar C_\gamma^K
=
\sum_{\eta\in\gamma}
d_B^2(\rho_{0\to1}^{(\eta)},\rho_1),
$$

then tests:

$$
\lambda_{\theta C}^{(\gamma)}
=
\frac{\Theta_\gamma}{\bar C_\gamma^K}
$$

across pre-registered calibration and validation cycles.

It rejects missing kernel edges, missing phase edges, invalid alignments,
non-closed active cycles, zero phases, nonpositive costs, and failed validation
slopes.

Status:

`kernel_cost_and_holonomy_phase_closure_executable`

### 98.3. Current manifest

The current manifest:

`theory_verifier_manifest_v6_0.json`

contains a toy combined gate.

For \(aba\):

$$
\bar C_{aba}^K
=
2\times0.10352341925454667,
\qquad
\Theta_{aba}
=
2\times0.020704683850909334.
$$

For \(aca\):

$$
\bar C_{aca}^K
=
2\times0.21496910533216443,
\qquad
\Theta_{aca}
=
2\times0.04299382106643289.
$$

Both give:

$$
\lambda_{\theta C}=0.2.
$$

These numbers are deliberately toy values.

The verifier gain is not a physical value of \(\hbar\); the gain is that both
cycle phase and cycle cost are now computed before the no-fit closure test.

Status:

`toy_holonomy_phase_cost_manifest_registered`

### 98.4. What is closed

Closed:

1. \(\Theta_\gamma\) no longer has to be copied into the cycle entry;
2. kernel-derived edge costs and phase-edge holonomy feed the same slope gate;
3. missing phase edges are executable failures;
4. principal-vs-winding branch source is explicit.

Open:

1. primitive grammar reconstruction of winding;
2. non-diagonal kernel-strain cost;
3. independent action standard \(A_{0,I}\);
4. experimental calibration family that is not a toy manifest.

Closed by Section 99:

make branch reconstruction executable:

$$
U_\gamma
\Rightarrow
\Theta_\gamma
$$

without manually declared edge phases being allowed to fit the cost ledger.

Status:

`holonomy_phase_cost_verifier_closed`
