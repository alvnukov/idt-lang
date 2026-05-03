## 79. Cross-Kernel Contraction Theorem

This section reduces the freedom in:

$$
\Xi_\eta.
$$

It does not select \(\Xi_\eta\) numerically.

It identifies the exact remaining mathematical freedom allowed by positivity.

Status:

`cross_kernel_contraction_theorem_initialized`

### 79.1. Finite Gram sector

In a finite admissible sector, write the before-update Gram kernel as:

$$
G_0\succeq0
$$

and the after-update Gram kernel as:

$$
G_1\succeq0.
$$

The cross-update kernel is a matrix:

$$
X_\eta.
$$

Block positivity requires:

$$
\mathbb G_\eta
=
\begin{pmatrix}
G_0 & X_\eta^\dagger\\
X_\eta & G_1
\end{pmatrix}
\succeq0.
$$

Status:

`finite_block_kernel_problem_defined`

### 79.2. Contraction form

The block kernel is positive iff there exists a contraction:

$$
\mathsf C_\eta
$$

with:

$$
\|\mathsf C_\eta\|\le1
$$

such that, on the supports of \(G_0\) and \(G_1\):

$$
X_\eta
=
G_1^{1/2}
\mathsf C_\eta
G_0^{1/2}.
$$

Equivalently:

$$
\Xi_\eta
=
\Gamma_{\eta}^{1/2}
\mathsf C_\eta
\Gamma^{1/2}
$$

in operator notation.

Proof sketch:

this is the standard positive block-matrix contraction factorization, obtained by applying the Schur complement or Douglas factorization on the support subspaces.

Status:

`cross_kernel_is_kernel_square_roots_plus_contraction`

### 79.3. Consequence: positivity still does not select phase

The contraction:

$$
\mathsf C_\eta
$$

is not fixed by:

$$
G_0,\quad G_1
$$

alone.

Therefore:

$$
G_0,G_1,\mathbb G_\eta\succeq0
\nRightarrow
\Xi_\eta
$$

as a unique object.

The free phase information has not disappeared.

It has been localized into:

$$
\mathsf C_\eta.
$$

Status:

`cross_phase_freedom_localized_in_contraction`

### 79.4. Identity and lossless limits

For the identity update with:

$$
G_1=G_0,
$$

the gate requires:

$$
\mathsf C_{\mathrm{id}}=I
$$

on the support of \(G_0\).

For a lossless reversible update, \(\mathsf C_\eta\) must be a partial isometry on the active support:

$$
\mathsf C_\eta^\dagger \mathsf C_\eta=I_{\mathrm{active}}.
$$

For an irreversible or coarse-grained update:

$$
\mathsf C_\eta^\dagger \mathsf C_\eta<I
$$

on at least one active direction.

Status:

`identity_reversible_and_lossy_contractions_classified`

### 79.5. Composition gate

For compatible lossless updates:

$$
\eta_2\circ\eta_1,
$$

the contraction must compose:

$$
\mathsf C_{\eta_2\circ\eta_1}
=
\mathsf C_{\eta_2}\mathsf C_{\eta_1}.
$$

For lossy updates, composition can only contract further:

$$
\|\mathsf C_{\eta_2\circ\eta_1}v\|
\le
\|\mathsf C_{\eta_1}v\|.
$$

This gives a non-fit consistency check on any proposed \(\mathsf C_\eta\).

Status:

`contraction_composition_gate_defined`

### 79.6. Transfer phase in contraction form

Using:

$$
X_\eta
=
G_1^{1/2}\mathsf C_\eta G_0^{1/2},
$$

the oriented transfer element becomes:

$$
\mathcal T_{ji}^{(\eta)}
=
\frac{
\langle b_j,
G_1^{1/2}\mathsf C_\eta G_0^{1/2}
a_i\rangle
}{
\sqrt{\mu(A_i)\mu_\eta(B_j)}
},
$$

where \(a_i,b_j\) are the event indicator/readout vectors in the finite sector.

Then:

$$
U_{ji}^{(\eta)}
=
\frac{\mathcal T_{ji}^{(\eta)}}{|\mathcal T_{ji}^{(\eta)}|}
$$

when nonzero.

Thus the phase problem is now:

$$
\eta
\Rightarrow
\mathsf C_\eta.
$$

Status:

`transfer_phase_reduced_to_contraction_selection`

### 79.7. Candidate selection principles

Allowed candidate principles for selecting \(\mathsf C_\eta\):

1. maximal recoverable inheritance;
2. minimal distinguishability disturbance;
3. support-respecting partial isometry;
4. stable coarse-graining fixed point;
5. composition consistency across independently generated updates.

Rejected selection principles:

1. choose \(\mathsf C_\eta\) to match \(G_N\);
2. choose \(\mathsf C_\eta\) to match measured \(\hbar\);
3. choose cycle phases after comparing with optical-clock or matter-wave residuals;
4. choose the simplest-looking unitary without deriving why it is selected.

Status:

`contraction_selection_principles_registered`

### 79.8. Known gates

In a unitary quantum readout sector:

$$
\mathsf C_\eta
$$

must reduce to the corresponding unitary propagator on the active support.

In a decohering readout sector:

$$
\mathsf C_\eta^\dagger \mathsf C_\eta<I
$$

must reproduce visibility loss without violating positivity.

In a quantum eraser context, recovery is possible only if the relevant contraction has not destroyed the controlled phase subspace.

Status:

`contraction_gates_match_unitary_decohering_and_eraser_limits`

### 79.9. What is closed

Closed:

1. admissible \(\Xi_\eta\) has exact contraction form;
2. positivity localizes but does not remove phase freedom;
3. the next mathematical object is \(\mathsf C_\eta\);
4. lossless, lossy, identity, and composition cases are separated.

Open:

1. primitive selection of \(\mathsf C_\eta\);
2. derivation of support relation \(R_\eta\);
3. non-exact cycle holonomies;
4. independent action-cost readout \(C_{ij}\);
5. numerical \(\hbar_I,\omega_{\ell,I},G_I\).

Next target:

test whether maximal recoverable inheritance selects a unique support-respecting contraction:

$$
\eta
\Rightarrow
\mathsf C_\eta.
$$

Maximal recoverability contraction test:

`sections/80-maximal-recoverability-contraction-test.md`

Status:

`cross_kernel_contraction_gap_reduced`
