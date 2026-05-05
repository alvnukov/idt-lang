## 86. Schur Actualization Verifier

This section registers executable gates for the accepted actualization core.

Status:

`schur_actualization_verifier_initialized`

### 86.1. Schur inheritance gate

The verifier can now check:

$$
\Gamma\succeq0,
\qquad
K_\eta\succeq0,
$$

and:

$$
\Gamma_\eta
=
\Gamma\circ K_\eta
\succeq0.
$$

This is the finite Schur product gate for inherited positivity.

Status:

`finite_schur_inheritance_gate_executable`

### 86.2. Actualization \(I_3=0\) gate

The verifier can now compute:

$$
\mathcal A(A,B)
=
\sum_{h\in A,h'\in B}
W(h)\overline{W(h')}\Gamma(h,h')
$$

and:

$$
\mu(A)=\mathcal A(A,A).
$$

For pairwise disjoint \(A,B,C\), it checks:

$$
I_3(A,B,C)=0.
$$

This is the executable finite gate for second-order-only interference in the bilinear sector.

Status:

`finite_actualization_i3_gate_executable`

### 86.3. Current manifest gates

The current manifest:

`theory_verifier_manifest.json`

contains executable examples for:

1. Schur positivity preservation;
2. \(I_3=0\) in the bilinear actualization sector;
3. negative tests for non-PSD Schur inputs and invalid non-disjoint \(I_3\) events.

Status:

`schur_actualization_manifest_registered`

### 86.4. What is closed

Closed:

1. finite Schur product positivity verification;
2. finite actualization \(I_3=0\) verification;
3. negative tests for malformed finite actualization contexts.

Open:

1. finite Born-like representation check;
2. probability-admissible context checker;
3. automatic manifest extraction from theory sections;
4. source-linked experimental gate calculators under the same verifier.

Next target:

add probability-admissible readout context checks:

$$
|\mathcal A(A_i,A_j)|
\le
\delta_K\sqrt{\mu(A_i)\mu(A_j)}.
$$

Probability context verifier:

`sections/87-probability-context-verifier.md`

Status:

`schur_actualization_verifier_closed`
