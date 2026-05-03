## 112. Full QM Foundation Front

This section is the single-pass foundation spine for the QM front.

The goal is not to add another finite effect gate. The goal is to state what
must exist before the protolanguage can honestly say:

`full_QM_I = derived`.

The current answer is:

`full_QM_I = target`.

### 112.1. Non-negotiable target

The protolanguage must reconstruct, without using QM as primitive input:

1. complex amplitude packets;
2. Born/context probability readout;
3. reversible unitary evolution;
4. continuum time generator;
5. universal action-phase scale \(\hbar_I\);
6. Hamiltonian energy operator;
7. translation generator and momentum operator;
8. de Broglie relation;
9. canonical commutator sector;
10. observable/readout contexts;
11. apparatus context dynamics;
12. measurement facticity / irreversible readout.

Only after these are closed may the theory claim full QM.

### 112.2. Foundation spine

The required dependency chain is:

$$
\Gamma_I,W
\Rightarrow
\psi_I
\Rightarrow
P_K
\Rightarrow
U_I
\Rightarrow
\Omega_I
\Rightarrow
H_I=\hbar_I\Omega_I
$$

and:

$$
T(a)
\Rightarrow
k_I
\Rightarrow
p_I=\hbar_I k_I
\Rightarrow
\lambda=\frac{h_I}{p_I}.
$$

The readout side must then close:

$$
\{P_i\},U_K,\Gamma_I
\Rightarrow
\text{apparatus context}
\Rightarrow
\text{stable fact}.
$$

Manifest symbols:

| Symbol | Meaning | Current status |
|---|---|---|
| `complex_amplitude_packet_I` | \(\psi_I\) as a packet readout of positive actualization | `derived_conditional` |
| `born_readout_I` | \(P_i=|\psi_i|^2\) in admissible contexts | `derived_conditional` |
| `unitary_evolution_I` | reversible context evolution | `derived_conditional` |
| `continuum_limit_I` | stable continuous limit of update chains | `derived_conditional` |
| `qm_continuum_limit_closure_I` | continuum/unitary-generator finite closure route | `target` |
| `schrodinger_generator_I` | \(i\partial_t\psi=\Omega_I\psi\) generator | `derived_conditional` |
| `hbar_action_standard_closure_I` | no-fit action-standard route for \(\hbar_I\) | `target` |
| `hbar_I` | universal action-phase conversion scale | `blocked` |
| `hamiltonian_energy_operator_I` | \(H_I=\hbar_I\Omega_I\) | `derived_conditional` |
| `translation_generator_I` | spatial phase generator \(k_I\) | `derived_conditional` |
| `momentum_operator_I` | \(p_I=\hbar_I k_I\) | `derived_conditional` |
| `de_broglie_relation_I` | \(\lambda=h_I/p_I\) | `derived_conditional` |
| `canonical_commutator_I` | \([x,p]=i\hbar_I\) sector | `derived_conditional` |
| `observable_context_I` | self-adjoint / projector readout contexts | `derived_conditional` |
| `apparatus_context_dynamics_I` | physical production of \(U_K,\{P_i\}\) | `derived_conditional` |
| `measurement_facticity_I` | irreversible stable outcome | `derived_conditional` |
| `qm_apparatus_facticity_closure_I` | apparatus/facticity finite closure route | `target` |
| `qm_dynamics_action_facticity_closure_I` | one-pass closure of generator/action/apparatus/facticity route | `target` |

### 112.3. Wave function emergence

The wave function is not primitive.

For a positive kernel:

$$
\Gamma_I(h,h')=\langle e_h,e_{h'}\rangle,
$$

define the amplitude packet:

$$
\psi_A=\sum_{h\in A}W(h)e_h.
$$

Then:

$$
\mu(A)
=
\mathcal A(A,A)
=
\|\psi_A\|^2.
$$

This gives the wave-function object as a compressed readout of the inherited
distinguishability kernel. It is currently conditional because the continuum
state space and the apparatus-selected context are not yet derived.

### 112.4. Born readout boundary

The Born rule is accepted only inside an admissible context:

$$
K=\{A_i\},
\qquad
|\mathcal A(A_i,A_j)|
\le
\delta_K
\sqrt{\mathcal A(A_i,A_i)\mathcal A(A_j,A_j)}.
$$

Then:

$$
P_K(A_i)
=
\frac{\mu(A_i)}{\sum_j\mu(A_j)}.
$$

This is not a global classical probability measure. It is a context probability
after off-diagonal facticity is sufficiently suppressed or controlled.

### 112.5. Dynamics split

The theory must not hide \(\hbar\) inside the Schrodinger generator.

First derive the frequency generator:

$$
i\partial_t\psi=\Omega_I\psi.
$$

Only after the action-phase scale is closed may this become:

$$
i\hbar_I\partial_t\psi=H_I\psi,
\qquad
H_I=\hbar_I\Omega_I.
$$

This split prevents a fake derivation where \(\hbar_I\) is silently imported
through the Hamiltonian.

### 112.6. Spatial generator and de Broglie

The same rule applies to momentum.

First derive a translation generator:

$$
T(a)=e^{-ia k_I}.
$$

Then the momentum scale is:

$$
p_I=\hbar_I k_I.
$$

The de Broglie relation follows only after \(h_I=2\pi\hbar_I\) is closed:

$$
\lambda=\frac{2\pi}{k_I}=\frac{h_I}{p_I}.
$$

The known experimental gates are electron diffraction, neutron interferometry,
atom interferometry, and molecule interference. They are validation gates, not
inputs for deriving \(\hbar_I\).

### 112.7. Measurement is not a postulate

Projectors and collapse cannot be primitive.

The required route is:

$$
\text{primitive apparatus inheritance}
\Rightarrow
U_K,\{P_i\}
\Rightarrow
p_i=\langle\psi|P_i|\psi\rangle
\Rightarrow
\psi_i'=\frac{P_i\psi}{\sqrt{p_i}}
\Rightarrow
\text{stable fact}.
$$

The finite verifier already checks the ideal projective limit. It does not yet
derive why a macroscopic apparatus selects those projectors, nor why an outcome
becomes irreversible. These remain required open nodes.

### 112.8. Known gates already covered

The current finite layer checks:

1. positive-kernel Born readout;
2. two-path interference visibility;
3. Sorkin \(I_3=0\);
4. marker/eraser visibility;
5. unitary measurement contexts;
6. finite unitary networks;
7. ideal projective update repeatability;
8. Bell/CHSH tables;
9. Bell/CHSH from amplitudes;
10. singlet angle model with \(|S|=2\sqrt2\).

These gates verify compatibility with standard finite QM. They do not by
themselves derive full QM.

### 112.9. Anti-overclaim verifier rule

The verifier now enforces a QM foundation spine:

`full_QM_I` may exist only with all required backbone symbols declared.

The verifier also enforces the intermediate single-pass milestone:

`qm_dynamics_action_facticity_closure_I`.

If a future manifest marks:

`full_QM_I = derived`

or:

`qm_dynamics_action_facticity_closure_I = derived`

while any backbone node is not closed, the verifier reports a premature closure
issue:

`qm_full_claim_premature`.

or:

`qm_single_pass_closure_premature`.

This makes a false full-QM or false single-pass closure claim mechanically
detectable.

### 112.10. Next hard closure

The next hard closure is not another Bell table.

It is:

$$
U_I(\Delta t)
\Rightarrow
\Omega_I
\Rightarrow
H_I=\hbar_I\Omega_I,
$$

and:

$$
T(a)
\Rightarrow
k_I
\Rightarrow
p_I=\hbar_I k_I.
$$

Therefore the immediate work is:

1. derive the continuum generator from update-chain composition;
2. derive the universal action standard \(A_{0,I}\);
3. compute \(\hbar_I=A_{0,I}\bar C_\gamma/\theta_\gamma\) without using
   \(hbar_{\mathrm{obs}}\), \(G_N\), or Planck units;
4. verify \(E=\hbar\omega\), \(p=\hbar k\), and \([x,p]=i\hbar\) as outputs.

Status:

`full_qm_foundation_spine_registered`

Not accepted:

`full_qm_derived`
