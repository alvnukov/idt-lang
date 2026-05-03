## 109. QM Finite Readout Closure

This section records the large finite QM pass after the two-path result.

The purpose is to close the strongest finite readout gaps that can be closed
from the present actualization calculus without importing Schrodinger dynamics,
\(\hbar\), or Born rule as primitive inputs.

Status:

`qm_finite_readout_closure_initialized`

### 109.1. Born context table

For a probability-admissible readout context:

$$
K=\{A_i\}_{i=1}^N,
$$

the verifier now computes:

$$
P_K(A_i)
=
\frac{\mu(A_i)}
{\sum_j\mu(A_j)}.
$$

The gate requires:

$$
|\mathcal A(A_i,A_j)|
\le
\delta_K
\sqrt{\mu(A_i)\mu(A_j)}
\qquad(i\ne j).
$$

It then compares the computed probability table against a declared known table.
This is a finite Born-readout gate, not a global probability measure on all
events.

Current manifest gate:

`born_context_probability_table_demo`

Status:

`finite_born_context_table_executable`

### 109.2. Normalized Sorkin parameter

The bilinear actualization sector implies:

$$
I_3(A,B,C)=0.
$$

The verifier now also computes a normalized experimental-style parameter:

$$
\kappa_{I_3}
=
\frac{|I_3(A,B,C)|}
{|I_2(A,B)|+|I_2(A,C)|+|I_2(B,C)|}.
$$

The finite gate checks:

$$
\kappa_{I_3}
\le
\epsilon_{I_3}.
$$

Current manifest gate:

`triple_path_sorkin_parameter_demo`

Status:

`finite_sorkin_parameter_gate_executable`

### 109.3. Marker visibility and eraser recovery

For a balanced two-path context with initial visibility \(V_0\), a marker
subsystem with overlap:

$$
m=\langle M_0|M_1\rangle
$$

gives:

$$
V_{\mathrm{marked}}
=
V_0|m|.
$$

For a pure marker channel, which-way distinguishability is:

$$
D=\sqrt{1-|m|^2}.
$$

Thus:

$$
\left(\frac{V_{\mathrm{marked}}}{V_0}\right)^2+D^2=1.
$$

Conditional eraser recovery is represented by a conditioned overlap
\(m_{\mathrm{cond}}\):

$$
V_{\mathrm{eraser}}
=
V_0|m_{\mathrm{cond}}|.
$$

Current manifest gate:

`marker_eraser_visibility_demo`

Status:

`finite_marker_eraser_visibility_gate_executable`

### 109.4. Bell no-signalling / CHSH table

The verifier now checks a finite bipartite readout table:

$$
P(a,b|x,y),
\qquad
a,b\in\{-1,+1\},
\qquad
x,y\in\{0,1\}.
$$

The gate checks:

1. nonnegative normalized probabilities for each context;
2. no-signalling marginals;
3. CHSH value:

$$
S=E_{00}+E_{01}+E_{10}-E_{11};
$$

4. declared Tsirelson-compatible bound:

$$
|S|\le2\sqrt2.
$$

Current manifest gate:

`bell_chsh_table_demo`

uses the standard zero-marginal maximal-CHSH table with:

$$
|S|=2\sqrt2.
$$

This is deliberately classified as a table/readout gate. It is not yet a full
derivation of Bell probabilities from \((W,\Gamma_I,\mathsf M)\). The remaining
hard bridge is:

$$
(W,\Gamma_I,\mathsf M)
\Rightarrow
P(a,b|x,y).
$$

Status:

`finite_bell_chsh_table_gate_executable_not_full_derivation`

### 109.5. What is now closed on the QM front

Closed in finite executable form:

1. context Born table from \(\mu(A)\);
2. two-path cosine fringe from \(\mathcal A\);
3. visibility from off-diagonal coherence;
4. Sorkin \(I_3=0\) and normalized \(\kappa_{I_3}\);
5. marker visibility loss;
6. conditional eraser recovery;
7. Bell no-signalling table validation;
8. CHSH/Tsirelson table validation.

These are known-formula gates, not new residual predictions.

Status:

`qm_finite_known_formula_gates_closed`

### 109.6. What remains open

Open:

1. derive propagation phases \(\phi(x)\) from primitive update geometry;
2. derive de Broglie scale \(p\lambda=h_I\);
3. derive full measurement context map \(\mathsf M\);
4. derive Bell tables from actualization plus local setting contexts;
5. derive collapse/facticity update as an irreversible readout limit;
6. produce a non-fitted experimental residual beyond standard QM.

Therefore the QM front is not finished as a full theory. It is now much more
closed as a finite readout reconstruction programme.

Status:

`qm_front_finite_reconstruction_advanced_but_not_complete`
