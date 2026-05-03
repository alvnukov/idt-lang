## 114. Generator / Translation Closure

This pass closes the mathematical part of the QM dynamics route as far as it
can be closed without fitting \(\hbar_I\).

It does not derive numerical \(\hbar_I\). It derives the protected form:

$$
U(t)\Rightarrow\Omega_I,
\qquad
T(a)\Rightarrow k_I,
\qquad
H_I=\hbar_I\Omega_I,
\qquad
p_I=\hbar_Ik_I.
$$

Status:

`qm_generator_translation_closure_I = target`

The route remains target because the continuum route is still only conditional
and the \(\hbar_I\) action-standard route is not yet closed from primitives.

### 114.1. Generator from unitary update flow

Given a reversible one-parameter readout family:

$$
U(0)=I,\qquad
U(t+s)=U(t)U(s),\qquad
U(t)^\dagger U(t)=I,
$$

and a stable continuum limit, the generator form is:

$$
U(t)=e^{-it\Omega_I},
\qquad
\Omega_I^\dagger=\Omega_I.
$$

Therefore:

$$
i\partial_t\psi=\Omega_I\psi.
$$

This is the Schrodinger generator in frequency units, not yet the energy
equation. The energy equation is allowed only after \(\hbar_I\) is independently
obtained:

$$
i\hbar_I\partial_t\psi=H_I\psi,
\qquad
H_I=\hbar_I\Omega_I.
$$

The verifier gate `unitary_generator_reconstruction_demo` now computes a finite
diagonal generator example:

$$
U(\Delta t)=\operatorname{diag}(e^{-i\omega_j\Delta t}),
\qquad
H_j=\hbar_I\omega_j.
$$

This validates the algebraic split:

`generator first, action scale second`.

### 114.2. Translation from spatial update flow

The spatial analogue is:

$$
T(0)=I,\qquad
T(a+b)=T(a)T(b),\qquad
T(a)^\dagger T(a)=I.
$$

In the continuum translation sector:

$$
T(a)=e^{-iak_I}.
$$

Momentum is not primitive:

$$
p_I=\hbar_Ik_I.
$$

The de Broglie wavelength is then:

$$
\lambda=\frac{2\pi}{|k_I|}
=
\frac{h_I}{|p_I|}.
$$

The verifier gate `translation_de_broglie_scale_demo` checks:

$$
T(a)=e^{-iak},
\qquad
p=\hbar k,
\qquad
\lambda=2\pi/|k|.
$$

This is still conditional on \(\hbar_I\), but it prevents importing \(p=\hbar k\)
as a primitive rule.

### 114.3. Canonical sector as Weyl sector first

Exact finite-dimensional canonical commutators are impossible because:

$$
\operatorname{tr}([X,P])=0,
\qquad
\operatorname{tr}(i\hbar I)=i\hbar N\ne0.
$$

Therefore the finite verifier must not pretend to prove:

$$
[x,p]=i\hbar
$$

in finite dimension.

The correct finite gate is the Weyl relation:

$$
ZX=e^{2\pi i/N}XZ.
$$

The continuum canonical commutator is then the limiting tangent relation:

$$
[x,k]=i,
\qquad
[x,p]=i\hbar_I.
$$

The verifier gate `finite_weyl_relation_demo` checks the exact finite Weyl
identity. This is stronger and cleaner than a fake finite commutator test.

### 114.4. Machine status

The manifest now registers:

`qm_generator_translation_closure_I`

with required nodes:

1. `unitary_evolution_I`;
2. `continuum_limit_I`;
3. `qm_continuum_limit_closure_I`;
4. `schrodinger_generator_I`;
5. `hbar_I`;
6. `hamiltonian_energy_operator_I`;
7. `translation_generator_I`;
8. `momentum_operator_I`;
9. `de_broglie_relation_I`;
10. `canonical_commutator_I`.

The verifier requires three finite gates:

1. `unitary_generator_reconstruction_demo`;
2. `translation_de_broglie_scale_demo`;
3. `finite_weyl_relation_demo`.

It rejects:

1. missing route symbols;
2. missing explicit derivation;
3. missing finite gates;
4. premature `derived` status while \(\hbar_I\), continuum, or dependent nodes
   remain unclosed.

### 114.5. What this actually closes

Closed conditionally:

1. generator equation form \(i\partial_t\psi=\Omega_I\psi\);
2. Hamiltonian scale relation \(H_I=\hbar_I\Omega_I\);
3. translation generator form \(T(a)=e^{-iak_I}\);
4. momentum scale relation \(p_I=\hbar_Ik_I\);
5. de Broglie wavelength \(\lambda=2\pi/|k_I|\);
6. finite Weyl relation as the finite canonical gate.

Still open:

1. primitive derivation of generic strongly continuous continuum limits;
2. independent numerical \(\hbar_I\) through \(A_{0,I}\);
3. physical apparatus selection of \(U_K,\{P_i\}\);
4. irreversible facticity law.

Status:

`generator_translation_math_closed_conditional`

Not accepted:

`full_qm_derived`
