## 113. QM Dynamics / Action / Facticity Single Pass

This section ties the current QM gaps into one route.

It does not mark them as solved. It makes their order and anti-import rules
explicit enough that the verifier can reject a fake closure.

Target:

`qm_dynamics_action_facticity_closure_I = target`

Not accepted:

`qm_dynamics_action_facticity_closure_I = derived`

### 113.1. One route, not five independent patches

The five route groups are coupled:

1. `continuum_limit_I` / `qm_continuum_limit_closure_I`;
2. `schrodinger_generator_I`;
3. `hbar_action_standard_closure_I` / `hbar_I`;
4. `de_broglie_relation_I` / `canonical_commutator_I`;
5. `apparatus_context_dynamics_I` / `measurement_facticity_I`.

They must close in one dependency order:

$$
U_I(\Delta t)
\Rightarrow
\Omega_I
\Rightarrow
\hbar_I
\Rightarrow
H_I=\hbar_I\Omega_I,
$$

and:

$$
T(a)
\Rightarrow
k_I
\Rightarrow
p_I=\hbar_Ik_I
\Rightarrow
\lambda=\frac{h_I}{p_I},
\qquad
[x,p]=i\hbar_I.
$$

The measurement side must then be:

$$
\Gamma_I,W,\text{apparatus inheritance}
\Rightarrow
U_K,\{P_i\}
\Rightarrow
\text{stable fact}.
$$

### 113.2. Continuum generator

The first closure is generator-only. It must not use \(\hbar_I\).

Assume a stable reversible update family:

$$
U_I(0)=I,\qquad
U_I(t+s)=U_I(t)U_I(s),\qquad
U_I(t)^\dagger U_I(t)=I.
$$

If the continuum limit is strongly continuous, Stone-type reconstruction gives:

$$
U_I(t)=e^{-it\Omega_I},
\qquad
\Omega_I^\dagger=\Omega_I.
$$

The generator equation is:

$$
i\partial_t\psi=\Omega_I\psi.
$$

This is not yet the Schrodinger equation in energy form. It is the
dimension-\(T^{-1}\) frequency-generator form. This protects the theory from
importing \(\hbar\) through the Hamiltonian.

Status:

`continuum_generator_route_registered`

Open condition:

derive strong continuity and stable coarse-graining from primitive update
chains, not from a Hilbert-space postulate.

### 113.3. Independent action scale

The action scale enters only after \(\Omega_I\) exists.

The required route is:

$$
\mathfrak s_I(\eta)
\Rightarrow
A_{0,I}
\Rightarrow
\hbar_I
=
\frac{A_{0,I}\bar C_\gamma}{\theta_\gamma}.
$$

Here:

1. \(A_{0,I}\) is an independently reconstructed action standard;
2. \(\bar C_\gamma\) is dimensionless cycle cost;
3. \(\theta_\gamma\) is branch-safe phase holonomy.

Forbidden inputs:

$$
hbar_{\mathrm{obs}},\quad G_N,\quad \text{Planck units}.
$$

If \(A_{0,I}\), \(\bar C_\gamma\), or \(\theta_\gamma\) remain open, then
\(\hbar_I\) remains blocked. This is not a weakness in bookkeeping; it is the
anti-fit rule.

After closure:

$$
H_I=\hbar_I\Omega_I.
$$

Known gates:

$$
E=\hbar\omega,
\qquad
\Delta\phi=\frac{1}{\hbar}\int L\,dt.
$$

They are validation outputs. They are not used to derive \(\hbar_I\).

### 113.4. de Broglie and canonical sector

The spatial side follows the same split.

First derive translation:

$$
T(a+b)=T(a)T(b),
\qquad
T(a)=e^{-iak_I}.
$$

Then define momentum only through the independently obtained action scale:

$$
p_I=\hbar_Ik_I.
$$

Then:

$$
\lambda=\frac{2\pi}{k_I}
=
\frac{h_I}{p_I}.
$$

The canonical sector is not a postulate. It must arise from translation acting
on position readout:

$$
T(a)^\dagger xT(a)=x+a.
$$

Taking the infinitesimal form gives:

$$
[x,k_I]=i,
\qquad
[x,p_I]=i\hbar_I.
$$

Known gates:

1. electron diffraction;
2. neutron interferometry;
3. atom interferometry;
4. molecule matter-wave interference.

The gates test \(p=\hbar k\) and \(\lambda=h/p\). They cannot be used as hidden
calibration inputs for \(\hbar_I\).

### 113.5. Apparatus dynamics

The finite verifier already checks ideal readout once \(U_K\) and \(\{P_i\}\)
are supplied. That is not enough.

The missing physical route is:

$$
\text{apparatus inheritance packet }M
\Rightarrow
\text{stable pointer sectors }M_i
\Rightarrow
\{P_i\}
$$

and:

$$
\text{controlled coupling }S\otimes M
\Rightarrow
U_K.
$$

The selection rule must come from stable distinguishability:

$$
|\Gamma_I(M_i,M_j)|\le\epsilon_{\mathrm{pointer}}
\quad(i\ne j).
$$

If this is not derived, then measurement contexts remain externally supplied.

Status:

`apparatus_context_dynamics_open`

### 113.6. Irreversible facticity

Collapse is not primitive.

The admissible route is:

$$
\psi
\Rightarrow
\sum_i c_i|i\rangle|M_i\rangle|E_i\rangle
\Rightarrow
|\Gamma_I(E_i,E_j)|\to0
\Rightarrow
\text{stable fact}.
$$

The irreversible quantity must be recoverability loss:

$$
\Lambda_{\mathrm{irrev}}
=
-\log
\frac{V_{\mathrm{rec,obs}}}{V_{\mathrm{rec,env}}}.
$$

If \(V_{\mathrm{rec,env}}\) can be restored, this is reversible erasure, not
facticity. If only \(V_{\mathrm{rec,obs}}\) is available and remains suppressed,
the outcome is operationally stable.

Known gates:

1. quantum eraser visibility recovery;
2. decoherence experiments;
3. macroscopic pointer stability;
4. matter-wave loss of visibility under controlled environmental coupling.

### 113.7. Machine guard

The manifest now registers:

`qm_dynamics_action_facticity_closure_I`

with dependencies:

1. `continuum_limit_I`;
2. `qm_continuum_limit_closure_I`;
3. `schrodinger_generator_I`;
4. `A0_I`;
5. `bar_C_gamma`;
6. `theta_gamma`;
7. `hbar_action_standard_closure_I`;
8. `hbar_I`;
9. `hamiltonian_energy_operator_I`;
10. `translation_generator_I`;
11. `momentum_operator_I`;
12. `de_broglie_relation_I`;
13. `canonical_commutator_I`;
14. `qm_generator_translation_closure_I`;
15. `observable_context_I`;
16. `apparatus_context_dynamics_I`;
17. `measurement_facticity_I`;
18. `qm_apparatus_facticity_closure_I`.

The verifier rejects:

1. missing route nodes;
2. missing explicit closure derivation;
3. premature `derived` status while any node remains unclosed;
4. an \(\hbar_I\) route that omits \(A_{0,I}\), \(\bar C_\gamma\), or
   \(\theta_\gamma\).

This makes the single-pass closure falsifiable at the theory-construction
level.

### 113.8. Current status

Closed by this pass:

1. the order of closure;
2. the no-\(\hbar\)-import split between \(\Omega_I\) and \(H_I\);
3. the no-fit route for \(\hbar_I\);
4. the translation-to-momentum route;
5. the conditional generator/translation finite gates;
6. the conditional apparatus/facticity finite gates;
7. the apparatus/facticity dependency order;
8. a verifier guard against false closure.

Still open:

1. primitive proof of generic strongly continuous continuum limits;
2. primitive computation of \(A_{0,I}\);
3. primitive derivation of physical apparatus pointer sectors;
4. quantitative scaling law for \(\Lambda_{\mathrm{irrev}}\);
5. first non-fitted numerical residual.

Therefore:

`qm_dynamics_action_facticity_closure_I = target`

and:

`full_QM_I = target`.
