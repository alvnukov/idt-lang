## 122. Scale Obstruction Theorem

Status: `guard_theorem`.

The current action-standard route has two different gaps.

### 122.1. Tick needs the length scale

The tick route can be made relational and reparametrization-safe, but an
absolute physical tick still depends on the radar length scale:

$$
\tau_{0,I}
\sim
\frac{\ell_0}{c_I N_r}.
$$

Therefore `primitive_tick_closure_I` now explicitly depends on:

1. `primitive_tick_I`;
2. `ell0`;
3. `c_I`.

Since `ell0` is still open, the tick is not derived as a physical scale.

### 122.2. Work needs a mass anchor

From dimensionless kernel costs, a velocity scale \(c_I\), a length scale
\(\ell_0\), and a tick scale \(\tau_{0,I}\), one can generate only \(L\) and
\(T\) dimensions. One cannot generate a nonzero \(M\) exponent.

The work unit has dimension:

$$
[W_{0,I}]=ML^2T^{-2}.
$$

So a physical work scale requires an independent mass/energy anchor:

$$
\texttt{primitive\_mass\_anchor\_I}.
$$

This is not a fitted numerical mass. It is a named unresolved object. The
theory is not allowed to silently smuggle it in through \(E=\hbar\omega\),
spectroscopy, \(G_N\), or Planck units.

### 122.3. Machine guard

The finite gate `primitive_work_dimensional_obstruction_demo` checks that:

$$
ML^2T^{-2}
\notin
\mathrm{span}_{\mathbb Q}
\{1,\ L/T,\ L,\ T\}.
$$

This proves a negative result: the present primitive set cannot derive an
absolute work unit without an additional mass/energy scale.

### 122.4. Consequence

The route is now:

$$
(\ell_0,c_I,\text{clock universality})
\Rightarrow
\tau_{0,I},
$$

$$
\texttt{primitive\_mass\_anchor\_I}
\Rightarrow
W_{0,I},
$$

$$
W_{0,I}\tau_{0,I}
\Rightarrow
A_{0,I}
\Rightarrow
\hbar_I.
$$

Current honest status:

1. `primitive_tick_closure_I = target`;
2. `primitive_work_unit_closure_I = target`;
3. `ell0_closure_I = target`;
4. `primitive_mass_anchor_I = open`;
5. `primitive_mass_anchor_closure_I = target`;
6. `A0_I = blocked`;
7. `hbar_I = blocked`.

Accepted:

`scale_obstruction_theorem_defined`

Not accepted:

`work_from_dimensionless_kernel_cost_alone`
