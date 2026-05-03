## 95. Finite Cycle Cost Composition Verifier

This section registers the executable gate:

$$
\bar C_\gamma^K
=
\sum_{\eta\in\gamma}
\bar c_K(\eta).
$$

Status:

`finite_cycle_cost_composition_verifier_initialized`

### 95.1. Edge-cost ledger

The verifier now accepts a finite edge-cost ledger:

$$
(i\to j)
\mapsto
\bar c_K(i\to j).
$$

Costs must be nonnegative and fixed before cycle closure testing.

Status:

`finite_edge_cost_ledger_defined`

### 95.2. Cycle sum gate

For a closed word:

$$
\gamma=i_0i_1\cdots i_N,
\qquad
i_N=i_0,
$$

the verifier computes:

$$
\bar C_\gamma^K
=
\sum_{r=0}^{N-1}
\bar c_K(i_r\to i_{r+1}).
$$

It rejects:

1. non-closed cycle words;
2. missing edge costs;
3. mismatch between declared and computed cycle cost.

Status:

`finite_cycle_cost_sum_gate_executable`

### 95.3. Current manifest

The current manifest:

`theory_verifier_manifest_v6_0.json`

contains:

$$
\bar C_{aba}^K=2.0,
\qquad
\bar C_{aca}^K=3.0.
$$

These are toy values.

They exist only to verify the closure machinery.

Status:

`toy_cycle_cost_sum_manifest_registered`

### 95.4. What is closed

Closed:

1. finite edge-cost ledger;
2. finite cycle cost summation;
3. mismatch detection.

Open:

1. automatic use of diagonal Bures edge costs in the cycle ledger;
2. full non-diagonal \(\bar c_K\);
3. real primitive cycle grammar;
4. automatic transfer of computed edge costs into phase-cost validation.

Closed by Section 96:

computed edge costs are now connected to phase-cost family entries without
duplicating the cycle-cost field:

$$
\bar c_K(\eta)
\Rightarrow
\bar C_\gamma^K
\Rightarrow
\lambda_{\theta C}^{(\gamma)}.
$$

Status:

`finite_cycle_cost_composition_verifier_closed`
