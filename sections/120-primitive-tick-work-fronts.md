## 120. Primitive Tick / Work Fronts

Status: `closure_front`, not physical derivation.

The action standard ladder now splits into two independent closure fronts:

$$
\tau_{0,I}
\Rightarrow
\texttt{primitive\_tick\_closure\_I},
\qquad
W_{0,I}
\Rightarrow
\texttt{primitive\_work\_unit\_closure\_I}.
$$

Only after both fronts close may the theory reconsider:

$$
A_{0,I}=W_{0,I}\tau_{0,I}.
$$

This section does not claim a numerical value for \(A_{0,I}\) or
\(\hbar_I\).

### 120.1. Primitive tick object

The tick cannot be the ordering parameter \(\lambda\). The ordering parameter
is bookkeeping. A physical tick candidate is a stable count-ratio readout:

$$
\tau_{0,I}
=
\frac{\Delta\tau_C}{N_{\mathrm{step}}},
$$

where \(C\) is an admissible stable clock chain and \(N_{\mathrm{step}}\) is a
pre-registered update-step count.

The same candidate must agree with radar sampling:

$$
\tau_{0,I}
=
\frac{\tau_{1/2}}{N_r},
\qquad
\tau_{1/2}=\frac{\ell_0}{c_I}.
$$

This makes the tick front independent from \(\hbar\), \(G_N\), Planck time, and
known quantum transition frequencies. It is still not closed, because the
theory must still prove:

1. clock-chain universality;
2. \(\lambda\)-reparametrization invariance;
3. closure of the radar length scale \(\ell_0\);
4. stability under admissible coarse-graining;
5. radar consistency outside a toy finite gate.

Machine symbols:

1. `primitive_tick_I`;
2. `ell0`;
3. `ell0_closure_I`;
4. `c_I`;
5. `primitive_tick_closure_I`.

Required finite gates:

1. `primitive_tick_clock_count_demo`;
2. `primitive_tick_radar_consistency_demo`;
3. `primitive_tick_reparam_invariance_demo`;
4. `primitive_tick_clock_universality_demo`.

### 120.2. Primitive work object

The primitive work unit cannot be imported from:

$$
E=\hbar\omega,
\qquad
\Delta E_{\mathrm{spectroscopy}},
\qquad
\text{Planck-unit formulas}.
$$

The admissible candidate is a closed update-balance unit:

$$
W_{0,I}
=
\sum_a W_a^{\mathrm{in}}
-
\sum_b W_b^{\mathrm{out}},
$$

where each \(W\)-packet is a pre-registered kernel-strain work packet, not a
known quantum energy gap. In the current finite verifier this is only a toy
balance check. It establishes arithmetic closure and source cleanliness, not a
physical energy scale.

There is now an explicit dimensional obstruction: dimensionless kernel costs
plus \(c_I,\ell_0,\tau_{0,I}\) cannot generate the mass exponent in
\(ML^2T^{-2}\). A primitive mass/energy anchor must be closed separately.

Machine symbols:

1. `primitive_work_unit_I`;
2. `primitive_mass_anchor_I`;
3. `primitive_mass_anchor_closure_I`;
4. `primitive_work_unit_closure_I`.

Required finite gates:

1. `primitive_work_balance_demo`;
2. `primitive_work_no_quantum_energy_demo`;
3. `primitive_work_coarse_grain_balance_demo`;
4. `primitive_work_sector_universality_demo`;
5. `primitive_work_dimensional_obstruction_demo`.

### 120.3. Guardrail for \(A_{0,I}\)

The action standard closure now depends on both closure fronts:

$$
\texttt{primitive\_work\_unit\_closure\_I}
\wedge
\texttt{primitive\_tick\_closure\_I}
\Rightarrow
\texttt{action\_standard\_work\_time\_closure\_I}.
$$

Therefore:

$$
A_{0,I}=\texttt{blocked}
$$

while either primitive work or primitive tick remains unclosed.

Consequently:

$$
\hbar_I=\texttt{blocked}.
$$

### 120.4. Honest status

Closed in this pass:

1. separate closure targets for primitive tick and primitive work;
2. no-fit source guards for both objects;
3. finite arithmetic gates for tick-count, radar-tick, work-balance,
   reparametrization, clock-universality, coarse-graining, and sector
   consistency;
4. verifier rejection of premature closure claims.

Still open:

1. a non-toy derivation of \(\tau_{0,I}\);
2. a non-toy derivation of \(W_{0,I}\);
3. closure of `ell0`;
4. closure of `primitive_mass_anchor_I`;
5. universality of both scales across admissible sectors;
6. experimental comparison after the scales are derived, not fitted.

Accepted:

`primitive_tick_work_fronts_defined`

Not accepted:

`primitive_tick_I = derived`

`primitive_work_unit_I = derived`

`A0_I = derived_conditional`

`hbar_I = derived_conditional`
