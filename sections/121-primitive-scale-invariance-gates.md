## 121. Primitive Scale Invariance Gates

Status: `finite_guard`, not scale derivation.

The primitive tick and primitive work fronts now require invariance checks
before either object can be promoted.

### 121.1. Tick reparametrization gate

The update ordering parameter \(\lambda\) is not a physical clock. Under:

$$
\lambda' = f(\lambda),
\qquad
f'(\lambda)>0,
$$

raw rates transform as:

$$
r_C'(E)=\frac{r_C(E)}{f'(\lambda)}.
$$

But tick ratios must remain invariant:

$$
\frac{r_C(A)}{r_C(B)}
=
\frac{r_C'(A)}{r_C'(B)}.
$$

The finite gate `primitive_tick_reparam_invariance_demo` checks both the raw
rate transformation and invariant ratios. This protects the theory from
turning \(\lambda\) into hidden absolute time.

### 121.2. Tick universality gate

Different admissible clock chains must reconstruct the same tick scale within
a registered tolerance:

$$
\max_i
\left|
\frac{\tau_{0,I}^{(i)}}{\langle\tau_{0,I}\rangle}
-1
\right|
\le \epsilon_\tau.
$$

The finite gate `primitive_tick_clock_universality_demo` is only a toy
universality check. It does not prove equivalence-principle-level universality.

### 121.3. Work coarse-graining gate

Primitive work cannot depend on how a closed transfer is partitioned. The
finite gate checks:

$$
\sum_a W_a^{\mathrm{fine,in}}
-
\sum_b W_b^{\mathrm{fine,out}}
=
\sum_c W_c^{\mathrm{coarse,in}}
-
\sum_d W_d^{\mathrm{coarse,out}}.
$$

This is a coarse-graining consistency check, not a physical work derivation.

### 121.4. Work universality gate

Independent admissible sectors must reconstruct the same work unit within a
registered tolerance:

$$
\max_i
\left|
\frac{W_{0,I}^{(i)}}{\langle W_{0,I}\rangle}
-1
\right|
\le \epsilon_W.
$$

The finite gate `primitive_work_sector_universality_demo` rejects sector drift
but does not yet identify the absolute physical energy scale.

### 121.5. Updated status

Required tick gates:

1. `primitive_tick_clock_count_demo`;
2. `primitive_tick_radar_consistency_demo`;
3. `primitive_tick_reparam_invariance_demo`;
4. `primitive_tick_clock_universality_demo`.

Required work gates:

1. `primitive_work_balance_demo`;
2. `primitive_work_no_quantum_energy_demo`;
3. `primitive_work_coarse_grain_balance_demo`;
4. `primitive_work_sector_universality_demo`;
5. `primitive_work_dimensional_obstruction_demo`.

Accepted:

`primitive_scale_invariance_gates_defined`

Not accepted:

`primitive_tick_closure_I = derived`

`primitive_work_unit_closure_I = derived`
