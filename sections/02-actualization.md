## 2. Actualization Calculus

For \(A,B\in\mathcal E\):

$$
\mathcal A(A,B)
=
\sum_{h\in A,h'\in B}
W(h)\overline{W(h')}
\Gamma_I(h,h')
$$

Diagonal measure:

$$
\mu(A)=\mathcal A(A,A)
$$

Raw contextual probability readout:

$$
P_K(A_i)
=
\frac{\mu(A_i)}
{\sum_j\mu(A_j)}
$$

is allowed only for admissible readout contexts defined below and only when the denominator is positive.

### 2.0. Domain Conditions

The minimal well-formed sector assumes:

1. \(H\) is finite or countable, or a measurable history space with the same formulas interpreted as integrals;
2. \(\mathcal E\) is an event algebra over \(H\);
3. \(W\in\ell^2(H)\) in the countable sector;
4. \(\Gamma_I\) is Hermitian:

$$
\Gamma_I(h,h')
=
\overline{\Gamma_I(h',h)};
$$

5. \(\Gamma_I\succeq0\);
6. diagonal normalization is allowed but not automatic:

$$
\Gamma_I(h,h)=1
$$

only for normalized distinguishability readouts;
7. all used event sums converge:

$$
\sum_{h,h'\in A}
\left|
W(h)\overline{W(h')}\Gamma_I(h,h')
\right|
<
\infty
$$

or are defined by a declared limiting procedure.

If:

$$
\mu(A)=0
$$

then \(A\) is a null actualization event.

Facticity ratio:

$$
\varepsilon(A,B)
$$

is undefined unless:

$$
\mu(A)>0,
\qquad
\mu(B)>0.
$$

For a reported readout table, null events may be omitted or assigned zero probability by convention.
The convention must be declared and cannot be used to hide interference terms.

Status:

`actualization_domain_conditions_defined`

### 2.0A. Theorem Block

Theorem 1 — positivity.

If \(\Gamma_I\succeq0\), then for any \(A_1,\ldots,A_N\in\mathcal E\):

$$
\left[
\mathcal A(A_i,A_j)
\right]_{ij}
\succeq0.
$$

Proof sketch:
write each event as a weighted indicator vector and restrict the positive kernel to the span of those vectors.

Theorem 2 — Born-like representation.

If:

$$
\Gamma_I(h,h')
=
\langle e_h,e_{h'}\rangle,
$$

then:

$$
\mu(A)
=
\left\|
\sum_{h\in A}W(h)e_h
\right\|^2.
$$

Theorem 3 — second-order interference only.

For pairwise disjoint \(A,B,C\):

$$
I_3(A,B,C)=0
$$

in the bilinear actualization sector.

Theorem 4 — inherited positivity under Schur update.

If:

$$
\Gamma_\eta
=
\Gamma\circ K_\eta,
\qquad
\Gamma\succeq0,
\qquad
K_\eta\succeq0,
$$

then:

$$
\Gamma_\eta\succeq0.
$$

This uses the Schur product theorem.

Status:

`actualization_theorem_block_initialized`

### 2.0B. Admissible Probability Contexts

A finite readout context:

$$
K=\{A_i\}_{i=1}^N
$$

is probability-admissible only if:

$$
\left|
\mathcal A(A_i,A_j)
\right|
\le
\delta_K
\sqrt{\mu(A_i)\mu(A_j)}
\qquad
(i\neq j)
$$

and:

$$
\sum_j\mu(A_j)>0.
$$

Then:

$$
P_K(A_i)
=
\frac{\mu(A_i)}
{\sum_j\mu(A_j)}
$$

is a context probability, not a global additive probability measure on all of \(\mathcal E\).

Status:

`admissible_probability_context_defined`

### 2.1. Action / phase bridge

Amplitude weight decomposes into magnitude and phase:

$$
W(h)
=
|W(h)|
e^{i\phi_I(h)}
$$

The action bridge defines:

$$
\phi_I(h)
=
\frac{S_I(h)}{\hbar_I}
$$

where \(S_I(h)\) is inherited action and \(\hbar_I\) is the universal phase-action scale.

Equivalently:

$$
S_I
\sim
S_I+2\pi\hbar_I
$$

The theory must not choose \(\hbar_I\) separately for each experiment.

One universal value must pass all action/phase gates.

Inherited action is not yet a primitive.

It must be derived from accumulated update cost:

$$
S_I(h)
=
\sum_{\eta\in h}
\mathfrak s_I(\eta)
$$

or in a continuum readout:

$$
S_I[\gamma]
=
\int_\gamma L_I\,d\tau_I
$$

Status:

`action_phase_bridge_defined`

Not yet derived:

`primitive_update_action_density`

Positivity:

$$
\Gamma_I\succeq0
$$

and:

$$
\left[
\mathcal A(A_i,A_j)
\right]\succeq0
$$

Facticity:

$$
\varepsilon(A,B)
=
\frac{|\mathcal A(A,B)|}
{\sqrt{\mathcal A(A,A)\mathcal A(B,B)}}
$$

$$
f(A,B)=1-\varepsilon(A,B)
$$

Classical limit:

$$
f(A_i,A_j)\to1
\quad(i\neq j)
$$

Coherent limit:

$$
f(A_i,A_j)\to0
$$

---
