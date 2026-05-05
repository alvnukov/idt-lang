## 87. Probability Context Verifier

This section registers the executable gate for probability-admissible readout contexts.

Status:

`probability_context_verifier_initialized`

### 87.1. Context admissibility gate

For a finite context:

$$
K=\{A_i\}_{i=1}^N,
$$

the verifier checks:

$$
|\mathcal A(A_i,A_j)|
\le
\delta_K
\sqrt{\mu(A_i)\mu(A_j)}
\qquad
(i\ne j).
$$

It also checks:

$$
\mu(A_i)>0,
\qquad
\sum_i\mu(A_i)>0.
$$

Status:

`finite_probability_context_gate_executable`

### 87.2. Why this matters

The theory must not treat:

$$
\mu(A)
$$

as a global probability measure.

Probability readout is allowed only after the context passes the decoherence/facticity gate.

The verifier now catches contexts where off-diagonal actualization remains too large.

Status:

`probability_readout_guard_initialized`

### 87.3. Current manifest gate

The current manifest:

`theory_verifier_manifest.json`

contains:

1. an admissible finite probability context;
2. a negative test where a large off-diagonal term prevents probability normalization.

Status:

`probability_context_manifest_registered`

### 87.4. What is closed

Closed:

1. finite probability-admissible context checking;
2. positive-measure checking;
3. negative test for excessive off-diagonal actualization.

Open:

1. context probability table emission;
2. facticity ratio report;
3. automatic link from manifest gates to section IDs;
4. Bell/CHSH context manifest checks.

Next target:

add probability table output and Bell/CHSH finite readout gates:

$$
P_K(A_i)
=
\frac{\mu(A_i)}{\sum_j\mu(A_j)}.
$$

Status:

`probability_context_verifier_closed`
