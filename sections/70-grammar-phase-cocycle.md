## 70. Grammar Phase Cocycle

This section defines the structure required to derive word phase functions:

$$
\Theta_j.
$$

It does not assign numerical phases.

Status:

`grammar_phase_cocycle_initialized`

### 70.1. Edge phase labels

For each allowed grammar transition:

$$
(a_i,a_j)\in\mathcal P_{EF},
$$

define a phase label:

$$
\vartheta_{ij}
\in
\mathbb R/2\pi\mathbb Z.
$$

For a word:

$$
w=a_{i_0}a_{i_1}\cdots a_{i_L},
$$

the word phase is:

$$
\Theta(w)
=
\sum_{r=0}^{L-1}
\vartheta_{i_ri_{r+1}}
\mod 2\pi.
$$

Status:

`edge_phase_labels_defined`

### 70.2. Cocycle condition

For concatenated words:

$$
w\circ v,
$$

the phase must satisfy:

$$
\Theta(w\circ v)
=
\Theta(w)+\Theta(v)
\mod 2\pi.
$$

This is the grammar analogue of action additivity.

It is required for transfer eigenphases to be stable under blocking.

Status:

`grammar_phase_cocycle_condition`

### 70.3. Gauge relabeling

Local symbol phase relabeling:

$$
a_i\mapsto e^{i\beta_i}a_i
$$

changes edge labels by:

$$
\vartheta_{ij}
\mapsto
\vartheta_{ij}
\beta_j-\beta_i.
$$

Cycle phases:

$$
\Theta(\gamma)
=
\sum_{(i,j)\in\gamma}
\vartheta_{ij}
\mod2\pi
$$

are gauge-invariant.

Therefore only cycle phases can enter:

$$
F_G.
$$

Status:

`grammar_phase_gauge_covariance`

### 70.4. Phase functions in the kernel map

For a coarse-grained word class \(w_j\), write:

$$
\Theta_j(\Theta)
=
b_j\Theta
+
\Phi_j,
$$

where:

1. \(b_j\) is the number of times the running transfer phase appears in the word;
2. \(\Phi_j\) is the gauge-invariant cocycle phase of the update word.

Then the kernel-normalization map is:

$$
F_G(\Theta)
=
\arg
\left[
\sum_jp_jr_j
e^{i(b_j\Theta+\Phi_j)}
\right].
$$

Status:

`kernel_map_phase_functions_defined`

### 70.5. What topology can fix

The grammar graph can fix:

1. allowed cycles;
2. integer coefficients \(b_j\);
3. gauge-invariant cycle basis.

It cannot fix:

$$
\Phi_j
$$

unless the primitive update algebra assigns a nontrivial phase cocycle.

If the cocycle is exact:

$$
\vartheta_{ij}=\beta_i-\beta_j,
$$

then all cycle phases vanish:

$$
\Theta(\gamma)=0.
$$

Status:

`topology_needs_phase_cocycle`

### 70.6. No-fit rule

Forbidden:

1. choose \(\Phi_j\) to reproduce \(\omega_{\ell,G}\);
2. hide gauge-dependent edge phases as physical phases;
3. infer cocycle phases from \(G_N\);
4. change cycle basis after residual comparison.

Allowed:

1. derive \(\vartheta_{ij}\) from primitive update action;
2. use only gauge-invariant cycle phases;
3. declare the cocycle exact and accept zero rotation if that follows;
4. classify the route as underderived if \(\Phi_j\) remains free.

Status:

`phase_cocycle_no_fit_rule`

### 70.7. What is closed

Closed:

$$
\Theta_j(\Theta)
=
b_j\Theta+\Phi_j.
$$

Closed:

Only gauge-invariant cycle phases may enter \(F_G\).

Open:

1. primitive update phase cocycle \(\vartheta_{ij}\);
2. gauge-invariant \(\Phi_j\);
3. coherence magnitudes \(r_j\);
4. fixed point \(\Theta_*\);
5. step compatibility.

Next target:

connect the grammar phase cocycle to the inherited action-phase bridge, or classify \(F_G\) as still underderived.

Action cocycle bridge:

`sections/71-action-cocycle-bridge.md`

Status:

`grammar_phase_cocycle_form_defined`
