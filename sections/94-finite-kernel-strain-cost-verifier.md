## 94. Finite Kernel-Strain Cost Verifier

This section registers the first executable cost gate for:

$$
\bar c_K(\eta)
=
d_B^2(\rho_{0\to1}^{(\eta)},\rho_1).
$$

Status:

`finite_kernel_strain_cost_verifier_initialized`

### 94.1. Diagonal finite sector

The first executable version is restricted to diagonal finite kernel states.

Given:

$$
G_0=\operatorname{diag}(g^0_i),
\qquad
G_1=\operatorname{diag}(g^1_i),
$$

the verifier normalizes:

$$
p^0_i
=
\frac{g^0_i}{\sum_jg^0_j},
\qquad
p^1_i
=
\frac{g^1_i}{\sum_jg^1_j}.
$$

Status:

`diagonal_kernel_state_cost_sector_defined`

### 94.2. Alignment

The support alignment is represented by a finite permutation:

$$
\pi_\eta.
$$

The transported before-distribution is:

$$
p^{0\to1}_i
=
p^0_{\pi_\eta(i)}.
$$

This is the diagonal restriction of the support-aligned kernel-state construction.

Status:

`finite_alignment_permutation_defined`

### 94.3. Executable Bures cost

For diagonal states, fidelity is:

$$
F(p,q)
=
\sum_i
\sqrt{p_iq_i}.
$$

The executable cost is:

$$
\bar c_K(\eta)
=
\arccos^2F(p^{0\to1},p^1).
$$

The current manifest checks:

$$
G_0=\operatorname{diag}(1,1),
\qquad
G_1=\operatorname{diag}(4,1),
$$

which gives:

$$
\bar c_K
\approx
0.10352341925454667.
$$

Status:

`diagonal_bures_kernel_strain_cost_executable`

### 94.4. What this does not prove

This gate does not yet cover:

1. non-diagonal Gram kernels;
2. non-permutation support maps;
3. full matrix square-root Bures fidelity;
4. physical derivation of \(G_0,G_1,\mathsf P_\eta\);
5. relation to observed \(\hbar\).

It only verifies the finite diagonal cost calculation.

Status:

`diagonal_cost_gate_scope_limited`

### 94.5. What is closed

Closed:

1. finite diagonal kernel-strain cost calculation;
2. normalization check;
3. alignment permutation check;
4. expected-cost mismatch detection.

Open:

1. full finite Bures gate;
2. automatic feeding of computed \(\bar c_K\) into cycle-family closure;
3. real primitive cycle-family data;
4. action standard \(A_{0,I}\).

Next target:

connect computed costs to cycle-family manifests:

$$
\bar c_K(\eta)
\Rightarrow
\bar C_\gamma^K
\Rightarrow
\lambda_{\theta C}^{(\gamma)}.
$$

Finite cycle cost composition verifier:

`sections/95-finite-cycle-cost-composition-verifier.md`

Status:

`finite_kernel_strain_cost_verifier_closed`
