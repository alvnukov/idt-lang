## 101. Transfer Element Phase Verifier

This section replaces declared unit transfer edges with finite transfer elements
that must satisfy a contraction bound.

The executable chain is now:

$$
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

`transfer_element_phase_verifier_initialized`

### 101.1. Finite transfer element

For each finite edge:

$$
\eta:i\to j,
$$

the verifier accepts a complex transfer element:

$$
X_\eta\in\mathbb C.
$$

It requires:

$$
0<|X_\eta|\le1.
$$

The upper bound is the finite scalar version of the contraction condition.

The phase readout is:

$$
T_\eta
=
\frac{X_\eta}{|X_\eta|}.
$$

Status:

`finite_transfer_phase_readout_executable`

### 101.2. Cycle pipeline

The transfer phases compose:

$$
U_\gamma
=
\prod_{\eta\in\gamma}
T_\eta.
$$

Then:

$$
\Theta_\gamma
=
\operatorname{atan2}(\operatorname{Im}U_\gamma,\operatorname{Re}U_\gamma)
+
2\pi n_\gamma.
$$

The cost side is still computed independently:

$$
\bar C_\gamma^K
=
\sum_{\eta\in\gamma}
d_B^2(\rho_{0\to1}^{(\eta)},\rho_1).
$$

Finally:

$$
\lambda_{\theta C}^{(\gamma)}
=
\frac{\Theta_\gamma}{\bar C_\gamma^K}.
$$

Status:

`transfer_element_cost_phase_closure_executable`

### 101.3. Current manifest

The current manifest:

`theory_verifier_manifest_v6_0.json`

contains a toy transfer-element family.

For \(a\to b\) and \(b\to a\):

$$
X_{ab}=X_{ba}
=
0.7998285325522299
+
0.01656256367071822\,i.
$$

For \(a\to c\) and \(c\to a\):

$$
X_{ac}=X_{ca}
=
0.6993531356241243
+
0.030086403784854224\,i.
$$

The magnitudes are below one, so the contraction gate passes. Their normalized
phases reproduce the transfer holonomies from Section 100.

Status:

`toy_transfer_element_manifest_registered`

### 101.4. What is closed

Closed:

1. unit transfer phase no longer has to be declared directly;
2. transfer elements must be nonzero;
3. transfer elements must satisfy \(|X_\eta|\le1\);
4. phase-cost closure uses contraction-bounded transfer phase readout.

Open:

1. deriving the transfer block from the full cross-kernel block
   \(\Xi_\eta\);
2. grammar-derived winding;
3. non-diagonal kernel-strain cost;
4. independent action standard \(A_{0,I}\);
5. non-toy calibration/validation family.

Closed by Section 102:

replace scalar transfer elements with finite matrix contraction blocks:

$$
X_\eta^\dagger X_\eta\le I
\Rightarrow
T_\eta.
$$

Status:

`transfer_element_phase_verifier_closed`
