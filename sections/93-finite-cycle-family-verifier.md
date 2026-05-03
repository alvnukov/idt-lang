## 93. Finite Cycle Family Verifier

This section registers the first executable gate for:

$$
\lambda_{\theta C}^{(\gamma)}
=
\Theta_\gamma/\bar C_\gamma^K.
$$

Status:

`finite_cycle_family_verifier_initialized`

### 93.1. Executable family gate

The verifier now accepts a finite cycle family with:

1. cycle word;
2. role: calibration / validation / excluded;
3. cycle class;
4. branch source;
5. lifted phase \(\Theta_\gamma\);
6. kernel-strain cost \(\bar C_\gamma^K\);
7. admissibility flag.

It computes:

$$
\lambda_{\theta C}^{(\gamma)}
=
\frac{\Theta_\gamma}{\bar C_\gamma^K}.
$$

Status:

`finite_phase_cost_family_gate_executable`

### 93.2. Calibration / validation rule

Calibration cycles estimate:

$$
\lambda_{\theta C,I}.
$$

Validation cycles must pass:

$$
\left|
\frac{
\lambda_{\theta C}^{(\gamma_{\mathrm{val}})}
}{
\lambda_{\theta C,I}^{(\mathrm{cal})}
}
-1
\right|
\le
\epsilon_{\theta C}.
$$

The current executable manifest contains one calibration cycle and one validation cycle with the same dimensionless slope.

Status:

`finite_phase_cost_validation_gate_defined`

### 93.3. Guardrails

The verifier rejects:

1. missing calibration cycles;
2. missing validation cycles;
3. duplicate active cycle words;
4. non-closed active cycle words;
5. zero lifted phase;
6. non-positive cost;
7. validation residual above tolerance.

Excluded cycles are allowed only with an explicit reason.

Status:

`finite_cycle_family_guardrails_executable`

### 93.4. Current manifest

The current manifest:

`theory_verifier_manifest_v6_0.json`

contains:

1. a calibration cycle;
2. a validation cycle;
3. an excluded cycle with missing derived kernel-strain cost.

The manifest passes.

This is not a physical prediction yet.

It proves that the finite verifier can now enforce the closure protocol on toy cycle families.

Status:

`first_finite_cycle_family_manifest_registered`

### 93.5. What is closed

Closed:

1. finite cycle-family manifest schema;
2. executable relative phase-cost validation gate;
3. duplicate-cycle guard;
4. excluded-cycle reason requirement.

Open:

1. real cycle family from primitive grammar;
2. computed \(\bar c_K\) from \(G_0,G_1,\mathsf P_\eta\);
3. branch-additivity verifier;
4. physical validation against known phase gates after \(A_{0,I}\).

Next target:

add finite kernel-strain cost computation:

$$
(G_0,G_1,\mathsf P_\eta)
\Rightarrow
\bar c_K(\eta).
$$

Finite kernel-strain cost verifier:

`sections/94-finite-kernel-strain-cost-verifier.md`

Status:

`finite_cycle_family_verifier_closed`
