## 69. Perron-Frobenius Grammar Weights

This section derives non-arbitrary update-word weights:

$$
p_j
$$

from the primitive grammar graph.

It does not derive the phase functions:

$$
\Theta_j.
$$

Status:

`perron_frobenius_grammar_weights_initialized`

### 69.1. Grammar adjacency matrix

Given primitive grammar:

$$
\mathcal G_{EF}
=
(\mathcal A_{EF},\mathcal P_{EF},\mathcal R_{EF}),
$$

define the adjacency matrix:

$$
A_{ij}
=
\begin{cases}
1,&(a_i,a_j)\in\mathcal P_{EF},\\
0,&\text{otherwise}.
\end{cases}
$$

Assume the allowed transition graph is primitive:

$$
\exists n:
A^n_{ij}>0
\quad
\text{for all }i,j.
$$

If this fails, the grammar decomposes into sectors and must be handled sector by sector.

Status:

`grammar_adjacency_matrix_defined`

### 69.2. Perron-Frobenius data

Let:

$$
\Lambda>0
$$

be the Perron-Frobenius eigenvalue:

$$
Av=\Lambda v,
\qquad
u^TA=\Lambda u^T,
$$

with:

$$
u_i>0,\qquad v_i>0.
$$

Normalize:

$$
\sum_i u_iv_i=1.
$$

Status:

`pf_eigenvectors_defined`

### 69.3. Maximum-entropy transition rule

The maximum-entropy Markov transition compatible with the grammar is:

$$
P_{ij}
=
\frac{A_{ij}v_j}
{\Lambda v_i}.
$$

It satisfies:

$$
\sum_jP_{ij}=1.
$$

The stationary distribution is:

$$
\pi_i=u_iv_i.
$$

The entropy rate is:

$$
h_{\mathrm{top}}
=
\log\Lambda.
$$

This is fixed by grammar topology, not by gravity.

Status:

`maximum_entropy_grammar_transition`

### 69.4. Word weights

For an allowed word:

$$
w=a_{i_0}a_{i_1}\cdots a_{i_L},
$$

define:

$$
p(w)
=
\pi_{i_0}
\prod_{r=0}^{L-1}
P_{i_ri_{r+1}}.
$$

These weights provide the \(p_j\) entering the kernel-normalization map:

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

`word_weights_from_pf_measure`

### 69.5. Reciprocity gate

If reversal symmetry requires:

$$
a_i\leftrightarrow a_{\bar i},
$$

then the PF measure must satisfy:

$$
p(w)
=
p(\bar w)
\left[
1+O(\epsilon_{\mathrm{rec}})
\right],
$$

where \(\bar w\) is the reversed/involuted word.

If this fails, the grammar carries a time-orientation residual:

$$
\mathcal R_{\mathrm{rec}}.
$$

Status:

`pf_reciprocity_gate`

### 69.6. What this closes

Closed, if the primitive grammar graph is known:

$$
\mathcal G_{EF}
\Rightarrow
A
\Rightarrow
(\Lambda,u,v)
\Rightarrow
P_{ij},\pi_i
\Rightarrow
p(w).
$$

Thus:

$$
p_j
$$

can be derived from grammar topology without \(G_N\).

Status:

`grammar_weights_closed_conditionally`

### 69.7. What remains open

This does not fix:

$$
r_j,
\qquad
\Theta_j(\Theta),
\qquad
\zeta_{\mathrm{step}}.
$$

The fixed-point map remains underderived until word phases and coherence magnitudes are obtained from the update kernels:

$$
K_\eta.
$$

Status:

`phases_and_magnitudes_still_open`

### 69.8. No-fit rule

Forbidden:

1. alter \(A_{ij}\) after comparing with \(G_N\);
2. choose non-PF weights to improve the gravity gate without a declared cost principle;
3. add forbidden transitions to tune \(\Theta_*\);
4. discard sectors because their PF weights produce the wrong pole.

Allowed:

1. use PF weights as the default no-cost grammar measure;
2. replace PF weights only with a derived primitive cost functional;
3. carry non-reciprocity as \(\mathcal R_{\mathrm{rec}}\).

Status:

`pf_weights_no_fit_rule`

### 69.9. What is closed

Closed conditionally:

$$
p_j
\Leftarrow
\text{Perron-Frobenius grammar measure}.
$$

Open:

1. actual grammar graph \(A\);
2. word phase functions \(\Theta_j\);
3. coherence magnitudes \(r_j\);
4. stable fixed point \(\Theta_*\);
5. step compatibility.

Next target:

derive word phase functions \(\Theta_j\) as a cocycle of the update grammar.

Grammar phase cocycle:

`sections/70-grammar-phase-cocycle.md`

Status:

`pf_weight_route_defined_not_full_FG`
