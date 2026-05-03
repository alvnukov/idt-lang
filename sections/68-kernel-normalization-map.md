## 68. Kernel Normalization Map

This section derives the candidate fixed-point map:

$$
F_G
$$

from positivity-preserving kernel normalization.

It also states what positivity alone does not fix.

Status:

`kernel_normalization_map_initialized`

### 68.1. Two-event normalized kernel

For a local two-readout sector, use the normalized positive kernel:

$$
K(q)
=
\begin{pmatrix}
1 & q\\
\bar q & 1
\end{pmatrix},
\qquad
q=re^{i\Theta}.
$$

Positivity is equivalent to:

$$
|q|\le1.
$$

Thus the local coherence parameter lives in:

$$
q\in\mathbb D
=
\{z\in\mathbb C:|z|\le1\}.
$$

Status:

`two_event_positive_kernel_disk`

### 68.2. Schur composition

For sequential inherited updates:

$$
K(q_1)\circ K(q_2)
=
K(q_1q_2).
$$

Therefore the coherence parameter composes as:

$$
q\mapsto q_1q_2.
$$

For \(b\) identical blocked updates:

$$
q\mapsto q^b.
$$

The phase map is:

$$
\Theta\mapsto b\Theta
\mod 2\pi.
$$

This map does not select a stable irrational fixed point by itself.

Status:

`schur_blocking_phase_map`

### 68.3. Convex coarse-graining

A coarse-grained mixture of admissible positive kernels:

$$
K'
=
\sum_j p_jK(q_j),
\qquad
p_j\ge0,
\qquad
\sum_jp_j=1,
$$

is positive and diagonally normalized.

Its coherence parameter is:

$$
q'
=
\sum_jp_jq_j.
$$

For update words \(w_j\) with phase contribution \(\Theta_j(\Theta)\):

$$
q'
=
\sum_jp_jr_j
e^{i\Theta_j(\Theta)}.
$$

Therefore the induced rotation map is:

$$
F_G(\Theta)
=
\arg
\left[
\sum_jp_jr_j
e^{i\Theta_j(\Theta)}
\right].
$$

Status:

`convex_kernel_coarse_graining_map`

### 68.4. What positivity fixes

Positivity and normalization fix:

1. the state space:

$$
q\in\mathbb D;
$$

2. admissible Schur composition:

$$
q\to q_1q_2;
$$

3. admissible convex mixing:

$$
q\to\sum_jp_jq_j;
$$

4. the condition that coherence cannot exceed:

$$
|q|\le1.
$$

Status:

`positivity_normalization_constraints`

### 68.5. What positivity does not fix

Positivity alone does not fix:

1. the weights \(p_j\);
2. the word phases \(\Theta_j\);
3. the block lengths \(b_j\);
4. the fixed point \(\Theta_*\);
5. the step clock invariant \(\zeta_{\mathrm{step}}\).

Therefore:

$$
\text{positivity + normalization}
\nRightarrow
\Theta_*.
$$

Status:

`positivity_alone_does_not_select_rotation`

### 68.6. Fixed-point equation

If \(p_j,r_j,\Theta_j\) are derived from update grammar, then:

$$
\Theta_*
=
F_G(\Theta_*)
$$

becomes:

$$
\Theta_*
=
\arg
\left[
\sum_jp_jr_j
e^{i\Theta_j(\Theta_*)}
\right].
$$

The fixed point is accepted only if:

$$
|F_G'(\Theta_*)|<1
$$

and:

$$
\Theta_*=\zeta_{\mathrm{step}}
\pm
\epsilon_\Theta.
$$

Status:

`kernel_map_fixed_point_equation`

### 68.7. No-fit rule

Forbidden:

1. choose \(p_j\) to reproduce \(G_N\);
2. choose \(r_j\) to reproduce \(\omega_{\ell,G}\);
3. choose word phases after seeing experimental residuals;
4. call positivity alone a derivation of \(\Theta_*\).

Allowed:

1. use positivity to constrain the allowed map class;
2. derive \(p_j,r_j,\Theta_j\) from update grammar;
3. solve the fixed-point equation only after the map is fixed;
4. declare `underderived` if the map coefficients remain free.

Status:

`kernel_normalization_no_fit_rule`

### 68.8. What is closed

Closed:

$$
F_G(\Theta)
=
\arg
\left[
\sum_jp_jr_j
e^{i\Theta_j(\Theta)}
\right]
$$

as the positivity-preserving kernel-normalization map class.

Closed:

positivity and diagonal normalization alone do not select a unique \(\Theta_*\).

Open:

1. update-word weights \(p_j\);
2. coherence magnitudes \(r_j\);
3. word phase functions \(\Theta_j\);
4. stable fixed point \(\Theta_*\);
5. compatibility with \(\zeta_{\mathrm{step}}\).

Next target:

derive \(p_j,r_j,\Theta_j\) from a non-arbitrary update grammar, or classify the fixed-point route as underderived.

Perron-Frobenius grammar weights:

`sections/69-perron-frobenius-grammar-weights.md`

Grammar phase cocycle:

`sections/70-grammar-phase-cocycle.md`

Coherence magnitude bridge:

`sections/72-coherence-magnitude-bridge.md`

Fixed-point map front status:

`sections/73-fixed-point-map-front-status.md`

Status:

`kernel_normalization_map_class_defined`
