## 115. Apparatus / Facticity Closure

This pass attacks the measurement gap without importing collapse.

The goal is to make apparatus selection and facticity computable as finite
conditions:

$$
\text{pointer stability}
\Rightarrow
\text{premeasurement decoherence}
\Rightarrow
\text{recoverability loss}
\Rightarrow
\text{stable fact}.
$$

Status:

`qm_apparatus_facticity_closure_I = target`

The route is conditional because the physical primitive construction of a
macroscopic apparatus is not yet derived. But the operational conditions are now
machine-checkable.

### 115.1. Pointer sectors

An apparatus context cannot be supplied as magic projectors.

The first condition is a stable pointer-sector kernel:

$$
\Gamma_M(i,j)=\langle M_i,M_j\rangle,
\qquad
\Gamma_M(i,i)=1.
$$

Pointer sectors are stable only if:

$$
|\Gamma_M(i,j)|\le\epsilon_{\mathrm{pointer}}
\quad(i\ne j).
$$

The verifier gate `pointer_sector_stability_demo` checks:

1. Hermitian/PSD pointer kernel;
2. normalized diagonal;
3. off-diagonal distinguishability bound.

This is the finite condition that lets a projector context become apparatus
selected rather than externally declared.

### 115.2. Premeasurement decoherence

The finite premeasurement form is:

$$
\sum_i c_i |i\rangle|M_0\rangle
\Rightarrow
\sum_i c_i |i\rangle|M_i\rangle|E_i\rangle.
$$

Tracing uncontrolled environment sectors suppresses off-diagonal terms:

$$
\rho_{ij}^{(S)}
=
c_i\overline{c_j}\langle E_j,E_i\rangle.
$$

Born weights stay:

$$
p_i=|c_i|^2.
$$

The verifier gate `premeasurement_decoherence_demo` checks:

1. normalized amplitudes;
2. Born weights;
3. PSD environment kernel;
4. residual coherence bound:

$$
\max_{i\ne j}
|c_i\overline{c_j}\Gamma_E(i,j)|
\le
\epsilon_{\mathrm{coh}}.
$$

This turns "measurement context" into a finite dynamical constraint.

### 115.3. Recoverability loss

Visibility loss is not automatically facticity.

Quantum eraser cases show that a lost fringe can return if the relevant
environment degrees of freedom remain controllable.

The facticity quantity is:

$$
\Lambda_{\mathrm{irrev}}
=
-\log
\frac{V_{\mathrm{rec,obs}}}{V_{\mathrm{rec,env}}}.
$$

Interpretation:

1. \(V_{\mathrm{rec,env}}\) is the visibility recoverable if the full
   environment record is controlled;
2. \(V_{\mathrm{rec,obs}}\) is the visibility recoverable by the observer's
   accessible operations;
3. large \(\Lambda_{\mathrm{irrev}}\) means operationally irreversible
   facticity.

The verifier gate `recoverability_loss_demo` computes \(\Lambda_{\mathrm{irrev}}\)
and checks a facticity threshold.

This keeps reversible erasure and irreversible measurement distinct.

### 115.4. Machine guard

The manifest now registers:

`qm_apparatus_facticity_closure_I`

with dependencies:

1. `born_readout_I`;
2. `observable_context_I`;
3. `apparatus_context_dynamics_I`;
4. `measurement_facticity_I`.

The verifier requires three finite gates:

1. `pointer_sector_stability_demo`;
2. `premeasurement_decoherence_demo`;
3. `recoverability_loss_demo`.

It rejects:

1. missing route symbols;
2. missing explicit derivation;
3. missing finite gates;
4. premature `derived` status while apparatus/facticity nodes remain only
   conditional.

### 115.5. What this closes

Closed conditionally:

1. finite pointer-sector stability criterion;
2. finite premeasurement decoherence criterion;
3. Born-weight preservation during premeasurement;
4. recoverability-loss distinction between erasure and facticity;
5. machine guard against fake collapse derivation.

Still open:

1. primitive construction of macroscopic apparatus sectors;
2. quantitative scaling law for \(\epsilon_{\mathrm{pointer}}\);
3. quantitative scaling law for \(\Lambda_{\mathrm{irrev}}\);
4. independent experimental residual beyond standard decoherence.

Status:

`apparatus_facticity_math_closed_conditional`

Not accepted:

`collapse_derived`

Not accepted:

`full_qm_derived`
