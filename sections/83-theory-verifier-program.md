## 83. Theory Verifier Program

This section defines the first machine-verifiable layer for the protolanguage.

The program is not a simulator of nature.

It is a logic verifier for the theory state.

Status:

`theory_verifier_program_initialized`

### 83.1. Scope

The verifier checks:

1. symbol existence;
2. dimensional consistency;
3. dependency cycles;
4. forbidden input paths;
5. attempts to mark underived claims as derived.

It does not prove the theory.

It prevents several classes of false progress.

Status:

`verifier_scope_defined`

### 83.2. Current manifest

The current machine manifest is:

`theory_verifier_manifest_v6_0.json`

It encodes the active blocked front:

$$
\hbar_I
\Leftarrow
A_{0,I},\bar C_\gamma,\theta_\gamma
$$

and the declared no-fit rules:

$$
\hbar_I
\nLeftarrow
G_N,\hbar_{\mathrm{obs}},\text{Planck units}.
$$

Status:

`current_verifier_manifest_registered`

### 83.3. First executable gate

Run:

```bash
python3 -m theory_verifier --json
```

Expected result for the current manifest:

```json
{
  "ok": true,
  "issues": []
}
```

This means the manifest is internally consistent.

It does not mean the blocked quantities are computed.

Status:

`first_executable_gate_defined`

### 83.4. What failure means

If the verifier reports:

`dimension_mismatch`

then a formula has inconsistent units.

If it reports:

`forbidden_input_path`

then a target depends on an experimental value that is forbidden as an input.

If it reports:

`underived_dependency`

then a claim marked as `derived` depends on an open, blocked, bridge, target, or experimental-gate symbol.

If it reports:

`dependency_cycle`

then the derivation graph is circular.

Status:

`verifier_failure_meanings_defined`

### 83.5. Current limitation

The first verifier does not yet parse Markdown formulas.

The manifest is explicit JSON.

This is intentional for the first version:

1. the verifier should be deterministic;
2. the theory text remains human-readable;
3. the manifest records only the claims selected for machine checking.

Status:

`markdown_parsing_not_yet_required`

### 83.6. What is closed

Closed:

1. executable logic-verifier scaffold;
2. current no-fit dependency manifest;
3. dimensional checks for active \(\hbar_I,\kappa_{\chi,I},G_I\) formulas;
4. unit tests for mismatch, circularity, forbidden input, and underived dependency detection.

Open:

1. Markdown-to-manifest extraction;
2. PSD/kernel numeric gates in the new verifier package;
3. phase holonomy finite-model checks;
4. experiment-ledger calculators under the same manifest discipline.

Next target:

add finite kernel and holonomy checks:

$$
\Gamma\succeq0,
\quad
\mathbb G_\eta\succeq0,
\quad
U_\gamma\ \text{gauge invariant}.
$$

Finite kernel holonomy verifier:

`sections/84-finite-kernel-holonomy-verifier.md`

Status:

`theory_verifier_program_scaffold_closed`
