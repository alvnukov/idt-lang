## 64. Primitive Cycle Grammar

This section defines the grammar needed to fix spectral phases without using gravity.

It is not yet a numerical derivation of:

$$
\omega_{\ell,I}.
$$

Status:

`primitive_cycle_grammar_initialized`

### 64.1. Update alphabet

For a local clock-vacuum link \(\langle EF\rangle\), define an update alphabet:

$$
\mathcal A_{EF}
=
\{a_1,\ldots,a_N\}.
$$

Each symbol denotes one admissible elementary update class:

$$
a_i
\leftrightarrow
\eta_i\in\mathcal U_{EF}.
$$

The alphabet must be fixed by primitive inheritance:

$$
\mathcal I,\Gamma_I,K_\eta
\Rightarrow
\mathcal A_{EF}.
$$

Status:

`update_alphabet_defined`

### 64.2. Grammar rules

A primitive cycle grammar is:

$$
\mathcal G_{EF}
=
(\mathcal A_{EF},\mathcal P_{EF},\mathcal R_{EF}),
$$

where:

1. \(\mathcal P_{EF}\) is the set of allowed adjacent update pairs;
2. \(\mathcal R_{EF}\) is the reversal/involution rule induced by \(E\leftrightarrow F\).

Allowed words:

$$
w=a_{i_1}a_{i_2}\cdots a_{i_m}
$$

must satisfy:

$$
(a_{i_r},a_{i_{r+1}})\in\mathcal P_{EF}.
$$

Status:

`primitive_cycle_grammar_rules`

### 64.3. Closed primitive cycles

A word \(w\) is a closed primitive cycle if:

$$
w\sim\varnothing
$$

under the inherited update equivalence relation and no proper subword is closed.

Define:

$$
N_{\mathrm{cyc}}
=
\min
\{
|w|: w\text{ is a nontrivial closed primitive cycle}
\}.
$$

This fixes the phase-lock denominator if the transfer mode follows the primitive cycle.

Status:

`closed_primitive_cycle_length_defined`

### 64.4. Phase-lock from cycle closure

If one traversal of a closed primitive cycle is identity in readout:

$$
\mathsf T^{N_{\mathrm{cyc}}}=I,
$$

then allowed phases satisfy:

$$
\theta_m
=
\frac{2\pi m}{N_{\mathrm{cyc}}},
\qquad
m=0,\ldots,N_{\mathrm{cyc}}-1.
$$

The first nonzero phase is:

$$
\theta_1
=
\frac{2\pi}{N_{\mathrm{cyc}}}.
$$

Thus:

$$
\omega_{\ell,I}
=
\frac{2\pi}
{N_{\mathrm{cyc}}\Delta\tau_{\mathrm{step}}}
$$

if this first mode couples to clock strain.

Status:

`cycle_closure_phase_lock`

### 64.5. Strain coupling gate

The first phase-locked mode counts only if:

$$
g_1\neq0.
$$

If:

$$
g_1=0,
$$

then:

$$
\omega_{\ell,I}
=
\frac{2\pi m_*}
{N_{\mathrm{cyc}}\Delta\tau_{\mathrm{step}}},
$$

where:

$$
m_*=\min\{m:g_m\neq0\}.
$$

The coupling rule must be derived from how the cycle changes:

$$
s_{EF}.
$$

Status:

`cycle_strain_coupling_gate`

### 64.6. What the grammar fixes and does not fix

The grammar can fix:

$$
N_{\mathrm{cyc}},
\qquad
m_*,
\qquad
\theta_*=\frac{2\pi m_*}{N_{\mathrm{cyc}}}.
$$

It does not by itself fix:

$$
\Delta\tau_{\mathrm{step}}.
$$

Therefore a full derivation still needs:

$$
\Delta\tau_{\mathrm{step}}
\Leftarrow
\text{clock-readout rule}.
$$

Status:

`cycle_grammar_fixes_phase_not_time`

### 64.7. No-fit rule

Forbidden:

1. choose \(N_{\mathrm{cyc}}\) from \(\omega_{\ell,G}\);
2. choose \(m_*\) from \(G_N\);
3. change grammar after non-gravity bounds;
4. identify \(\Delta\tau_{\mathrm{step}}\) with a convenient clock time without a readout rule.

Allowed:

1. derive \(\mathcal G_{EF}\) from \(\mathcal I,\Gamma_I,K_\eta\);
2. compute \(N_{\mathrm{cyc}}\);
3. compute \(g_m\);
4. separately derive \(\Delta\tau_{\mathrm{step}}\) from clock readout.

Status:

`cycle_grammar_no_fit_rule`

### 64.8. What is closed

Closed:

$$
\mathcal G_{EF}
\Rightarrow
N_{\mathrm{cyc}},m_*
\Rightarrow
\theta_*.
$$

Open:

1. actual primitive grammar \(\mathcal G_{EF}\);
2. strain coupling coefficients \(g_m\);
3. step clock time;
4. numerical \(\omega_{\ell,I}\).

Next target:

derive the step clock-readout rule. Without it, cycle grammar fixes only a phase, not a frequency.

Step clock readout rule:

`sections/65-step-clock-readout-rule.md`

Fixed-point rotation grammar:

`sections/66-fixed-point-rotation-grammar.md`

Perron-Frobenius grammar weights:

`sections/69-perron-frobenius-grammar-weights.md`

Status:

`cycle_grammar_phase_route_defined`
