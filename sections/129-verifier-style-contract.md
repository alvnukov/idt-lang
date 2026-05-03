## 129. Verifier Style Contract

Status:

`infrastructure_quality_gate`

The verifier is now part of the theory, not only a helper script. Its job is to
make claims hard to smuggle in. Therefore verifier changes must obey a stable
style.

### 129.1. Gate registration rule

Finite gate dispatch is registry-based:

$$
\texttt{gate.type}
\mapsto
\texttt{check\_...()}
$$

New finite gates must be added to `FINITE_GATE_CHECKS`, not appended as another
branch in a long manual `if` chain.

This gives one visible place where the executable vocabulary is listed.

### 129.2. Checker rule

Each checker must:

1. parse all numeric inputs with typed parsers;
2. reject non-finite or malformed values;
3. recompute the claimed value from inputs;
4. return a precise issue code on mismatch;
5. avoid changing tests to make a formula pass.

### 129.3. Theory-status rule

A gate may verify a formula without upgrading the theory status.

Examples:

`clock_strain_source_law_I = derived_conditional`

does not imply:

`G_I = derived`

and:

`weak_field_clock_calculator_I = derived_conditional`

does not imply:

`\gamma_I^{\mathrm{PPN}} = derived`

### 129.4. Refactor accepted

This version replaces the long finite-gate dispatch chain with:

`FINITE_GATE_CHECKS`

The behavior is intended to be identical. The acceptance condition is that the
same manifest, verifier run, type check, lint check, and full test module pass
after the refactor.

### 129.5. Future style

Next verifier cleanup should target closure checks:

$$
\texttt{target symbol}
\mapsto
\texttt{required symbols, required gates, status rule}.
$$

That should be done only after another large theory cluster needs it. Refactor
must support theory development, not become a separate treadmill.
