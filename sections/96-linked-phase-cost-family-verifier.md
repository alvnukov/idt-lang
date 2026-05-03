## 96. Linked Phase-Cost Family Verifier

This section closes the duplicate-number gap between the finite cycle-cost ledger
and the relative phase-cost family gate.

Status:

`linked_phase_cost_family_verifier_initialized`

### 96.1. Linked input rule

The previous gate accepted:

$$
(\Theta_\gamma,\bar C_\gamma^K)
$$

as two declared fields inside the same cycle entry.

That was useful for a first toy check, but it allowed a hidden fit:

$$
\bar C_\gamma^K
\quad\text{could be copied by hand rather than derived from edge costs.}
$$

The linked gate removes that freedom.

It accepts:

1. a fixed edge-cost ledger
   \((i\to j)\mapsto\bar c_K(i\to j)\);
2. a pre-registered cycle word
   \(\gamma=i_0i_1\cdots i_N,\ i_N=i_0\);
3. a lifted phase \(\Theta_\gamma\).

Then it computes:

$$
\bar C_\gamma^K
=
\sum_{r=0}^{N-1}
\bar c_K(i_r\to i_{r+1})
$$

before testing:

$$
\lambda_{\theta C}^{(\gamma)}
=
\frac{\Theta_\gamma}{\bar C_\gamma^K}.
$$

Status:

`phase_cost_uses_computed_cycle_cost`

### 96.2. Rejection rules

The verifier rejects:

1. missing edge costs for an active cycle;
2. non-closed active cycle words;
3. duplicate active cycle words;
4. zero lifted phase;
5. nonpositive computed cycle cost;
6. calibration slope inconsistency;
7. validation slope failure.

Excluded cycles remain allowed, but they must provide a reason and are not used
in the calibration or validation statistics.

Status:

`linked_phase_cost_rejection_rules_executable`

### 96.3. Current manifest

The current manifest:

`theory_verifier_manifest_v6_0.json`

contains the linked toy check:

$$
\bar C_{aba}^K=1.0+1.0=2.0,
\qquad
\Theta_{aba}=0.4,
$$

and:

$$
\bar C_{aca}^K=1.5+1.5=3.0,
\qquad
\Theta_{aca}=0.6.
$$

Therefore:

$$
\lambda_{\theta C}^{(aba)}
=
\lambda_{\theta C}^{(aca)}
=
0.2.
$$

These are toy values only.

They test whether the closure machinery rejects hidden manual duplication; they
do not constitute a physical value for \(\hbar\).

Status:

`toy_linked_phase_cost_manifest_registered`

### 96.4. What is closed

Closed:

1. \(\bar C_\gamma^K\) can be computed from an edge-cost ledger before
   phase-cost closure testing;
2. \(\lambda_{\theta C}\) validation no longer needs a manually copied cost
   field;
3. missing active edge costs are executable failures.

Open:

1. full non-diagonal Bures cost;
2. primitive grammar generation of admissible cycle families;
3. physical action standard \(A_{0,I}\), without which \(\hbar_I\) remains
   blocked.

Closed by Section 97:

feed computed kernel-strain transition costs into the edge-cost ledger:

$$
\rho_{0\to1}^{(\eta)},\rho_1
\Rightarrow
\bar c_K(\eta)
\Rightarrow
\bar C_\gamma^K
\Rightarrow
\lambda_{\theta C}^{(\gamma)}.
$$

Status:

`linked_phase_cost_family_verifier_closed`
