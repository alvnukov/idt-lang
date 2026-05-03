## 118. Hbar No-Air Provenance Gate

Status: `anti_fit_guard`.

This module fixes a reliability rule for the \(\hbar_I\) route:

do not promote \(\hbar_I\) even to `derived_conditional` unless the action
standard \(A_{0,I}\) has non-circular provenance.

### 118.1. What is forbidden

The following are not derivations of \(A_{0,I}\) or \(\hbar_I\):

1. choosing \(A_{0,I}=1\) by normalization and then claiming a physical action;
2. using \(\hbar_{\mathrm{obs}}\);
3. using Planck units;
4. using \(G_N\);
5. using \(E=\hbar\omega\);
6. using \(p=\hbar k\);
7. using \(\Delta\phi=S/\hbar\).

These are either unit conventions or known-gate formulas. They can validate an
already derived scale, but cannot supply the scale.

### 118.2. Provenance condition

An action standard has acceptable provenance only if:

$$
A_{0,I}
\Leftarrow
\mathcal P_A
$$

where \(\mathcal P_A\) is a primitive action-producing structure that does not
contain \(\hbar_I\), \(\hbar_{\mathrm{obs}}\), \(G_N\), Planck units, or any
formula algebraically equivalent to an \(\hbar\)-definition.

Until that holds:

$$
\hbar_I
=
\frac{A_{0,I}\bar C_\gamma}{\theta_\gamma}
$$

is a route schema, not a derived physical value.

### 118.3. Machine rule

The manifest now requires:

`action_standard_provenance_demo`

The gate records:

1. candidate sources;
2. forbidden sources;
3. action-standard status;
4. whether the scale is normalization-only;
5. whether the route claims physical \(\hbar_I\).

The verifier rejects:

1. overlap between candidate and forbidden sources;
2. physical \(\hbar_I\) claims from normalization-only \(A_{0,I}\);
3. physical \(\hbar_I\) claims when \(A_{0,I}\) is only a candidate;
4. `hbar_I = derived_conditional` while \(A_{0,I}\), \(\bar C_\gamma\), or
   \(\theta_\gamma\) remains unclosed.

### 118.4. Current accepted status

Accepted:

`hbar_route_schema_guarded`

`hbar_no_air_provenance_gate_added`

Not accepted:

`hbar_I = derived_conditional`

`hbar_I = derived`

The next honest target is therefore narrower:

derive \(A_{0,I}\) from a primitive action-producing mechanism, not from
normalization, known constants, or already-known quantum formulas.

The selected ladder is:

`sections/119-action-standard-work-time-ladder.md`
