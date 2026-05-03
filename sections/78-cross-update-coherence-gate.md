## 78. Cross-Update Coherence Gate

This section corrects the transfer route.

Event transport:

$$
\Pi_\eta
$$

gives support.

It does not by itself give a complex transfer phase.

For a true oriented transfer from a source event before an update to a target event after the update, the theory needs a cross-update coherence kernel:

$$
\Xi_\eta(h',h).
$$

Status:

`cross_update_coherence_gate_initialized`

### 78.1. The missing before-after object

The ordinary actualization kernel compares histories within one readout layer:

$$
\Gamma_I(h,h').
$$

The updated kernel compares histories after the update:

$$
\Gamma_{\eta,I}(h',h'').
$$

Neither one is automatically a transition amplitude from before to after.

The missing object is:

$$
\Xi_\eta(h_{\mathrm{after}},h_{\mathrm{before}}).
$$

It compares a target history after \(\eta\) with a source history before \(\eta\), through the update act itself.

Status:

`before_after_coherence_kernel_required`

### 78.2. Support relation and cross kernel

Let:

$$
R_\eta\subset H_{\mathrm{before}}\times H_{\mathrm{after}}
$$

be the update support relation.

Then:

$$
(h,h')\in R_\eta
$$

means that \(h'\) is an admissible inherited continuation or image of \(h\) under \(\eta\).

The support map is:

$$
\Pi_\eta A
=
\{h'\in H_{\mathrm{after}}:\exists h\in A,\ (h,h')\in R_\eta\}.
$$

But support alone has no phase.

The phase-carrying object is the pair:

$$
(R_\eta,\Xi_\eta).
$$

Status:

`support_relation_separated_from_cross_phase_kernel`

### 78.3. Oriented transfer element

For source and target readout events:

$$
A_i\subset H_{\mathrm{before}},
\qquad
B_j\subset H_{\mathrm{after}},
$$

define:

$$
\mathcal T_{ji}^{(\eta)}
=
\frac{
\sum_{\substack{h\in A_i,\ h'\in B_j\\(h,h')\in R_\eta}}
W_\eta(h')
\overline{W(h)}
\Xi_\eta(h',h)
}{
\sqrt{
\mu(A_i)\mu_\eta(B_j)
}
}.
$$

This is defined only when:

$$
\mu(A_i)>0,
\qquad
\mu_\eta(B_j)>0.
$$

Then:

$$
U_{ji}^{(\eta)}
=
\frac{\mathcal T_{ji}^{(\eta)}}{|\mathcal T_{ji}^{(\eta)}|}
$$

when:

$$
|\mathcal T_{ji}^{(\eta)}|>0.
$$

Status:

`oriented_transfer_from_support_and_cross_kernel`

### 78.4. Positivity consistency

The cross kernel is admissible only if the block kernel:

$$
\mathbb G_\eta
=
\begin{pmatrix}
\Gamma_I & \Xi_\eta^\dagger\\
\Xi_\eta & \Gamma_{\eta,I}
\end{pmatrix}
$$

is positive:

$$
\mathbb G_\eta\succeq0.
$$

Then the transfer readout obeys a Cauchy-Schwarz bound:

$$
|\mathcal T_{ji}^{(\eta)}|
\le
1
$$

for normalized admissible events.

This prevents the cross-update transfer from becoming an unconstrained complex matrix.

Status:

`cross_update_block_positivity_gate`

### 78.5. Identity and composition

For the identity update:

$$
\eta=\mathrm{id},
$$

the gate requires:

$$
R_{\mathrm{id}}
=
\{(h,h):h\in H\},
\qquad
\Xi_{\mathrm{id}}=\Gamma_I.
$$

For composable updates:

$$
\eta_2\circ\eta_1,
$$

the support relation must compose:

$$
R_{\eta_2\circ\eta_1}
\subseteq
R_{\eta_2}\circ R_{\eta_1}.
$$

The cross kernel must compose through admissible intermediate histories:

$$
\Xi_{\eta_2\circ\eta_1}(h_2,h_0)
\sim
\sum_{h_1}
\Xi_{\eta_2}(h_2,h_1)
\Xi_{\eta_1}(h_1,h_0).
$$

The equality may fail only by declared loss into unobserved sectors.

Status:

`cross_update_identity_and_composition_gates`

### 78.6. Same-slice proxy status

The earlier same-slice expression:

$$
\mathcal A_\eta(A_j,\Pi_\eta A_i)
$$

can be used only as a proxy when the update supplies a canonical identification between the transported source event and after-update histories.

Without such identification:

$$
\mathcal A_\eta(A_j,\Pi_\eta A_i)
$$

is not an oriented before-after transfer.

Therefore:

$$
\Pi_\eta
\nRightarrow
\mathcal T_{ji}^{(\eta)}
$$

unless:

$$
\Xi_\eta
$$

or an equivalent before-after coherence readout is derived.

Status:

`same_slice_transfer_proxy_not_full_derivation`

### 78.7. Known gates

In ordinary quantum mechanics, before-after transfer is represented by a propagator or unitary matrix element:

$$
\langle x_f,t_f|x_i,t_i\rangle.
$$

In the short-time limit:

$$
U(t+\Delta t,t)
\approx
I-\frac{i}{\hbar}H\Delta t.
$$

The protolanguage transfer must reproduce these forms only after:

$$
R_\eta,\Xi_\eta
$$

have been fixed without using the known quantum answer as input.

Status:

`propagator_gate_registered_without_import`

### 78.8. No-fit rule

Forbidden:

1. set \(\Xi_\eta\) equal to a known quantum propagator and call it primitive;
2. choose \(R_\eta\) after inspecting the desired cycle phase;
3. tune \(\Xi_\eta\) to produce observed \(\hbar\), \(G_N\), or \(\omega_{\ell,G}\);
4. hide missing before-after structure inside notation \(\mathcal T_{ij}\).

Allowed:

1. derive \(R_\eta\) from update support;
2. derive \(\Xi_\eta\) from inherited distinguishability across the update;
3. classify the transfer route as open if \(\Xi_\eta\) is absent;
4. use standard propagator formulas only as final gates.

Status:

`cross_update_no_fit_rule`

### 78.9. What is closed

Closed:

1. event transport supplies support, not phase;
2. oriented complex transfer requires cross-update coherence \(\Xi_\eta\);
3. block positivity is the admissibility gate for \(\Xi_\eta\);
4. same-slice overlap is only a proxy unless a canonical identification is derived.

Open:

1. primitive derivation of \(R_\eta\);
2. primitive derivation of \(\Xi_\eta\);
3. explicit clock-vacuum transfer elements;
4. non-exact cycle holonomies;
5. independent action-cost readout and numerical \(\hbar_I\).

Next target:

derive the cross-update kernel from inheritance consistency:

$$
\eta
\Rightarrow
(R_\eta,\Xi_\eta).
$$

Cross-kernel contraction theorem:

`sections/79-cross-kernel-contraction-theorem.md`

Status:

`cross_update_coherence_gap_exposed`
