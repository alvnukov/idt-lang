## 99. Unit Holonomy Branch Verifier

This section closes one more manual branch in the finite \(\hbar\)-route
machinery.

Section 98 computed \(\Theta_\gamma\) from a phase-edge ledger. The new gate
accepts the cycle holonomy itself:

$$
U_\gamma\in U(1),
$$

then reconstructs the lifted phase:

$$
U_\gamma
\Rightarrow
\Theta_\gamma.
$$

Status:

`unit_holonomy_branch_verifier_initialized`

### 99.1. Unit gate

For every active cycle, the verifier requires:

$$
|U_\gamma|=1
$$

within tolerance.

It then computes the principal phase:

$$
\theta_\gamma^{(0)}
=
\operatorname{atan2}(\operatorname{Im}U_\gamma,\operatorname{Re}U_\gamma),
$$

and the lifted phase:

$$
\Theta_\gamma
=
\theta_\gamma^{(0)}+2\pi n_\gamma.
$$

For now, \(n_\gamma\) is either:

1. fixed to \(0\) by `principal`;
2. explicitly declared by `winding`.

The grammar-derived winding rule remains open.

Status:

`unit_holonomy_to_lifted_phase_executable`

### 99.2. Combined cost-phase test

The same finite gate still computes:

$$
\bar c_K(\eta)
=
d_B^2(\rho_{0\to1}^{(\eta)},\rho_1)
$$

from diagonal kernel-edge data, then:

$$
\bar C_\gamma^K
=
\sum_{\eta\in\gamma}\bar c_K(\eta),
$$

and finally:

$$
\lambda_{\theta C}^{(\gamma)}
=
\frac{\Theta_\gamma}{\bar C_\gamma^K}.
$$

This removes the explicit phase-edge ledger from the closure test.

Status:

`unit_holonomy_phase_cost_closure_executable`

### 99.3. Current manifest

The current manifest:

`theory_verifier_manifest.json`

contains a toy unit-holonomy family:

$$
U_{aba}
=
0.9991427546395419
+
0.04139753436266696\,i,
$$

and:

$$
U_{aca}
=
0.9963053400297743
+
0.0858817176595564\,i.
$$

These reconstruct:

$$
\Theta_{aba}=0.04140936770181867,
\qquad
\Theta_{aca}=0.08598764213286577,
$$

with the same kernel-derived costs as Section 98, giving:

$$
\lambda_{\theta C}=0.2
$$

for both toy cycles.

These numbers are not a physical prediction. They test that the executable
pipeline no longer accepts copied \(\Theta_\gamma\) or copied phase-edge sums.

Status:

`toy_unit_holonomy_manifest_registered`

### 99.4. What is closed

Closed:

1. active holonomies must be unit magnitude;
2. \(\Theta_\gamma\) is reconstructed from \(U_\gamma\);
3. kernel-derived costs and unit-holonomy phases feed the same
   calibration/validation slope gate;
4. nonunit holonomies are executable failures.

Open:

1. deriving \(T_\eta\) from primitive cross-kernel blocks;
2. grammar-derived winding;
3. non-diagonal kernel-strain cost;
4. independent action standard \(A_{0,I}\);
5. non-toy calibration/validation cycle family.

Closed by Section 100:

move from declared cycle holonomy to primitive transfer elements:

$$
T_\eta
\Rightarrow
U_\gamma
\Rightarrow
\Theta_\gamma.
$$

Status:

`unit_holonomy_branch_verifier_closed`
