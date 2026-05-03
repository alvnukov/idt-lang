## 107. Spectral Readout Consistency Verifier

This section adds consistency gates around the finite spectral cost-phase
readout. The point is not to add a new physical assumption, but to prevent a
bad extension: the non-diagonal gate must reduce to the previous diagonal
Bures gate and must not depend on arbitrary active-basis labels.

Status:

`spectral_readout_consistency_verifier_initialized`

### 107.1. Diagonal-limit gate

When \(G_0\), \(G_1\), and the support transport commute, the spectral density
formula must reduce to the earlier diagonal rule:

$$
\bar c_K
=
\arccos^2
\left(
\sum_i\sqrt{p_{0\to1,i}p_{1,i}}
\right).
$$

The verifier now builds the diagonal block kernel:

$$
X_{ij}
=
\sqrt{G_{1,i}G_{0,j}}\,
P_{ij},
$$

where \(P\) is the declared alignment permutation, and checks:

$$
\bar c_K^{\mathrm{spectral}}
=
\bar c_K^{\mathrm{diagonal}}.
$$

Status:

`spectral_diagonal_limit_executable`

### 107.2. Basis-covariance gate

For independent source and target basis relabelings:

$$
G_0' = U_0G_0U_0^\dagger,
\qquad
G_1' = U_1G_1U_1^\dagger,
\qquad
X' = U_1XU_0^\dagger,
$$

the readout must be unchanged:

$$
\bar c_K(G_0',G_1',X')
=
\bar c_K(G_0,G_1,X),
$$

and:

$$
\frac{\det C'}{|\det C'|}
=
\frac{\det C}{|\det C|}.
$$

This is an executable no-label-dependence gate. If it fails, the proposed
non-diagonal cost is a coordinate artifact, not a primitive readout.

Status:

`spectral_readout_basis_covariance_executable`

### 107.3. Current manifest

The current manifest:

`theory_verifier_manifest_v6_0.json`

adds:

1. `spectral_kernel_diagonal_limit_demo`;
2. `spectral_kernel_readout_covariance_demo`.

Together with Section 106, the finite spectral gate now checks:

1. block-kernel positivity;
2. positive support normalization;
3. non-diagonal Bures cost;
4. determinant phase readout;
5. phase-cost slope validation;
6. diagonal-limit reduction;
7. unitary basis covariance.

Status:

`spectral_readout_consistency_manifest_registered`

### 107.4. Remaining limits

The consistency gates are still finite \(2\times2\) checks. They do not prove
the continuum source law, do not fix \(\hbar_I\), and do not derive an
experimental action standard.

Open:

1. \(n>2\) spectral fidelity;
2. rank-deficient support pseudoinverse;
3. non-toy calibration/validation families;
4. connection between \(\bar C_\gamma^K\) and \(A_{0,I}\).

Status:

`spectral_readout_consistency_verifier_closed`
