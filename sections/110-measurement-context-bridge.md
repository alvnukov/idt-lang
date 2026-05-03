## 110. Measurement Context Bridge

This section closes the next finite QM gap:

$$
\text{amplitude packet}+\text{readout context}
\Rightarrow
\text{probability table}.
$$

The previous finite gates could validate probability tables. This bridge makes
the finite context map executable.

Status:

`measurement_context_bridge_initialized`

### 110.1. Finite amplitude packet

Let the finite inherited amplitude packet be:

$$
\psi=(\psi_1,\ldots,\psi_N),
\qquad
\sum_i|\psi_i|^2=1.
$$

In this finite bridge, \(\psi\) is not a primitive physical wave in space. It is
the compressed coordinate representation of the actualization amplitude packet
inside a chosen readout sector.

Status:

`finite_wavefunction_as_amplitude_packet_defined`

### 110.2. Measurement context map

A finite measurement context is represented by a unitary map:

$$
U_K.
$$

The context amplitudes are:

$$
\alpha^{(K)}
=
U_K\psi.
$$

The actualization kernel in the resolved readout basis is diagonal:

$$
\Gamma_K(i,j)=\delta_{ij}.
$$

Therefore:

$$
\mu_K(i)=|\alpha_i^{(K)}|^2,
\qquad
P_K(i)=|\alpha_i^{(K)}|^2.
$$

This is the finite Born table as actualization measure, not a separate Born
postulate.

Status:

`unitary_measurement_context_probability_executable`

### 110.3. Current manifest

The current manifest:

`theory_verifier_manifest_v6_0.json`

adds:

`unitary_measurement_context_demo`

with:

$$
\psi=(1,0),
\qquad
U_K=
\frac1{\sqrt2}
\begin{pmatrix}
1&1\\
1&-1
\end{pmatrix}.
$$

The computed finite readout table is:

$$
P=(1/2,1/2).
$$

Status:

`unitary_measurement_context_manifest_registered`

### 110.4. Bell from amplitudes

The previous Bell gate consumed probability tables:

$$
P(a,b|x,y).
$$

The new gate consumes amplitude tables:

$$
\alpha_{ab}^{xy}
\Rightarrow
P(a,b|x,y)=|\alpha_{ab}^{xy}|^2.
$$

It then checks:

1. normalized amplitudes in every context;
2. no-signalling marginals;
3. CHSH:

$$
S=E_{00}+E_{01}+E_{10}-E_{11};
$$

4. Tsirelson-compatible bound:

$$
|S|\le2\sqrt2.
$$

Current manifest gate:

`bell_chsh_from_amplitudes_demo`

Status:

`bell_chsh_from_amplitudes_gate_executable`

### 110.5. Boundary of the result

Closed in finite executable form:

1. wavefunction-as-amplitude-packet readout;
2. unitary context map;
3. Born table from actualization measure;
4. Bell/CHSH probabilities from amplitudes rather than copied probabilities.

Still open:

1. derive \(U_K\) from physical apparatus dynamics;
2. derive Bell setting amplitudes from local setting contexts;
3. derive propagation phases from update geometry;
4. derive \(\hbar_I\) as action-phase conversion.

This is a real bridge, but it is still finite and contextual.

Status:

`measurement_context_bridge_closed_finite`
