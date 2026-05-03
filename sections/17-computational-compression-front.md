## 17. Computational Compression Front

Primitive calculations are not automatically simpler.

But the protolanguage may generate compressed variables that are simpler than standard tools in mixed or boundary regimes.

The target is not:

$$
\text{always compute every history directly}.
$$

The target is:

$$
\text{primitive layer}
\Rightarrow
\text{compressed readout variables}
\Rightarrow
\text{faster / cleaner / more accurate computation}.
$$

Status:

`computational_compression_front_initialized`

### 17.1. Direct primitive cost

Direct primitive computation involves:

$$
h,\quad W(h),\quad \Gamma_I(h,h'),\quad
\mathfrak s_I,\quad \mathfrak q_I,\quad r_C,\quad \rho_I.
$$

A full history sum scales badly:

$$
\mathcal A(A,B)
=
\sum_{h\in A,h'\in B}
W(h)\overline{W(h')}
\Gamma_I(h,h').
$$

This is usually harder than standard effective equations.

Therefore direct primitive summation is not the default computational strategy.

Status:

`direct_primitive_sum_not_default`

### 17.2. Compression principle

A derived variable is accepted as computationally useful if it:

1. is obtained from primitive/readout structure;
2. reduces the number of active degrees of freedom;
3. preserves the relevant experiment gates;
4. exposes residuals instead of hiding them;
5. gives equal or better predictive accuracy with fewer fitted parameters.

Call such a variable a compressed readout variable:

$$
C_I
=
\mathcal C(\text{primitive data}).
$$

Computational value requires:

$$
\mathrm{Cost}(C_I)
<
\mathrm{Cost}(\text{standard tool})
$$

or:

$$
\mathrm{Error}(C_I)
<
\mathrm{Error}(\text{standard approximation})
$$

on a declared domain.

Status:

`compressed_readout_variable_acceptance_rule`

### 17.3. Existing compression candidates

The theory already contains candidate compressed variables.

| Compressed variable | Primitive source | Standard role |
|---|---|---|
| \(\psi(x)\) | projected actualization amplitude | wavefunction |
| \(\kappa_{ab}=|\Gamma_{ab}|\) | coherence kernel | visibility / decoherence |
| \(f(a,b)=1-|\Gamma_{ab}|\) | coherence loss | facticity / classicality |
| \(\chi(E)=r_C(E)/r_\infty\) | clock-rate ratio | gravitational time factor |
| \(\Phi_I=c_I^2\log\chi\) | clock-rate field | Newtonian potential |
| \(\oint A_I\) | phase connection | AB holonomy |
| \(Z_{0,I}/R_{K,I}\) | vacuum/charge-action bridge | \(\alpha_{\mathrm{em}}\) gate |
| \(\mathcal R_I\) | mismatch after closure | residual predictor |

These are not ad hoc helpers.

They are derived interfaces between primitive inheritance and known experimental readouts.

Status:

`candidate_compressed_variables_listed`

### 17.4. Where compression may beat standard tools

The likely advantage is not ordinary textbook limits.

In ordinary domains:

$$
\text{proto}
\to
\text{QM/GR effective equations}
$$

should be used.

Potential advantage appears where standard descriptions are stitched manually:

1. measurement / decoherence / recoverability;
2. quantum eraser and partial facticity;
3. clock comparison with quantum phase;
4. AB / gauge phase with apparatus-dependent coherence;
5. weak gravity plus interferometry;
6. dark-sector residual comparisons;
7. transitions between coherent, factual, and classical readouts.

Status:

`compression_advantage_domains_declared`

### 17.5. Example: facticity variable

For two alternatives:

$$
\kappa_{ab}
=
|\Gamma_{ab}|,
\qquad
f_{ab}
=
1-\kappa_{ab}.
$$

Instead of modelling every environmental degree of freedom, compute the operational visibility:

$$
V
=
\frac{2\sqrt{p_ap_b}}{p_a+p_b}
\kappa_{ab}.
$$

This can be simpler than full unitary system-environment modelling when only visibility and recoverability are measured.

But it is valid only if:

1. \(\kappa_{ab}\) is derived or calibrated once from a declared marking channel;
2. quantum eraser recoverability is predicted without re-fitting;
3. triple-slit gate remains \(I_3\approx0\).

Status:

`facticity_as_compressed_decoherence_variable`

### 17.6. Example: clock potential variable

Instead of starting from a metric:

$$
g_{\mu\nu},
$$

use clock-rate compression:

$$
\chi(E)
=
\frac{r_C(E)}{r_\infty},
\qquad
\Phi_I
=
c_I^2\log\chi.
$$

Then weak-field predictions follow:

$$
\frac{\Delta\nu}{\nu}
\approx
\frac{\Delta\Phi_I}{c_I^2},
$$

and:

$$
\ddot x
=
-\nabla\Phi_I.
$$

This may be computationally simpler for precision clock networks because clocks directly measure \(\chi\), not \(g_{\mu\nu}\).

Residuals:

$$
\alpha_C,\quad\beta_C,\quad\xi_C
$$

remain visible instead of being absorbed into a metric fit.

Status:

`clock_potential_as_compressed_gravity_variable`

### 17.7. Example: holonomy variable

For gauge phase phenomena, the relevant compressed variable is:

$$
\Theta_{q,I}
=
\frac{q_I}{\hbar_I}
\oint A_I.
$$

This can be simpler than local force modelling because AB phase is holonomy-sensitive even when:

$$
F_I=0
$$

along the path.

Known gate:

$$
\Delta\phi_{AB}
=
\frac{q\Phi_B}{\hbar}.
$$

Status:

`holonomy_as_compressed_gauge_phase_variable`

### 17.8. Accuracy rule

A compressed tool is accepted only on a declared domain:

$$
\mathcal D_C.
$$

It must provide:

$$
O^{\mathrm{compressed}}_j
=
O^{\mathrm{obs}}_j
+
\mathcal R_j
$$

with residuals bounded by known gates.

If a residual is unexplained, the compressed tool is downgraded:

$$
\text{predictive}
\to
\text{phenomenological}.
$$

Status:

`compressed_tool_accuracy_gate`

### 17.9. What v5.18 changes

This section corrects the computational goal.

The theory should not claim:

$$
\text{primitive computation is always simpler}.
$$

It should aim for:

$$
\text{new derived variables that compress mixed regimes}.
$$

The next concrete computational target is:

$$
(\kappa_{ab},f_{ab},\Theta_{q,I})
\Rightarrow
\text{two-path + eraser + AB predictions}
$$

with fewer assumptions than full system-environment modelling.

Status:

`computational_simplification_reframed_as_compression`

First compressed calculator:

`sections/18-compressed-two-path-calculator.md`

Clock-network calculator:

`sections/20-clock-network-calculator.md`
