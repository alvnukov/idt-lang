## 116. Continuum Limit Closure

Status: `conditional_closure`, not full derivation.

Target:

`qm_continuum_limit_closure_I`

The goal is to prevent a hidden import of continuum quantum mechanics. The
proto-language may use the standard continuous generator only after a finite
reversible update family has passed the minimal closure tests below.

### 116.1. Finite input

Start with a finite admissible readout context \(K_N\) and a reversible update
family

$$
U_N(t)=e^{-it\Omega_N}.
$$

Here \(\Omega_N\) is the dimensionless frequency generator recovered from the
phase evolution of the finite update packet. No energy scale is used at this
stage. Energy enters only later through

$$
H_I=\hbar_I\Omega_I.
$$

This keeps the generator route independent of a fitted numerical \(\hbar\).

### 116.2. Required closure properties

For the finite family to be accepted as a continuum candidate, it must satisfy:

1. identity:

$$
U_N(0)=I;
$$

2. one-parameter group law:

$$
U_N(t)U_N(s)=U_N(t+s);
$$

3. unitarity:

$$
U_N(t)^\dagger U_N(t)=I;
$$

4. continuity at the identity:

$$
\lim_{t\to0}\|U_N(t)-I\|=0;
$$

5. stable generator recovery:

$$
\Omega_N\psi
=
i\lim_{\Delta t\to0}
\frac{U_N(\Delta t)-I}{\Delta t}\psi .
$$

These are not decorative assumptions. Without them the expression

$$
i\partial_t\psi=\Omega_I\psi
$$

would be an imported Schrödinger-form postulate, not a reconstructed readout.

### 116.3. Continuum candidate

A sequence \((K_N,U_N,\Omega_N)\) defines a conditional continuum candidate when
the readout states embed into a limiting Hilbert packet space and the finite
flows converge strongly on the admissible packet domain:

$$
\lim_{N\to\infty}
\|J_NU_N(t)\psi_N-U_I(t)J_N\psi_N\|=0 .
$$

The limit is accepted only if \(U_I(t)\) remains a strongly continuous
one-parameter unitary group. Then the standard generator theorem gives a
self-adjoint generator \(\Omega_I\) with

$$
U_I(t)=e^{-it\Omega_I},
\qquad
i\partial_t\psi=\Omega_I\psi .
$$

This is a conditional mathematical bridge. It does not compute \(\hbar_I\), and
it does not by itself select the physical Hamiltonian.

### 116.4. Machine gates

The manifest now requires three finite gates for the continuum route:

1. `one_parameter_unitary_flow_demo`;
2. `strong_continuity_modulus_demo`;
3. `generator_difference_convergence_demo`.

The verifier now registers:

`qm_continuum_limit_closure_I`

with dependencies:

1. `unitary_evolution_I`;
2. `continuum_limit_I`.

It rejects:

1. missing route symbols;
2. missing explicit derivation;
3. missing finite flow gates;
4. premature `derived` status while the continuum node remains only
   conditional.

### 116.5. Known formula recovered

When the closure conditions hold, the accepted readout equation is:

$$
i\partial_t\psi=\Omega_I\psi,
\qquad
i\hbar_I\partial_t\psi=H_I\psi .
$$

The second equation is not independent of the first. It is obtained only after
the separate action-scale route supplies a universal \(\hbar_I\). Therefore the
current pass closes the continuum generator form conditionally, but leaves the
numeric Planck-scale route honest and still open.

### 116.6. What remains open

Still not closed:

1. primitive proof that generic inheritance networks admit the required
   strongly continuous limit;
2. uniqueness of the limiting packet space;
3. physical selection of the Hamiltonian beyond \(\Omega_I\);
4. independent computation of \(\hbar_I\);
5. a beyond-standard-QM residual.

Current accepted status:

`continuum_limit_I = derived_conditional`

`qm_continuum_limit_closure_I = target`

Not accepted:

`full_QM_I = derived`
