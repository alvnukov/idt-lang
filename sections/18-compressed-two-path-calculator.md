## 18. Compressed Two-Path Calculator

This section turns the first compressed variables into a calculational protocol.

It is not a new postulate.

It is the two-path sector of bilinear actualization written in the smallest operational variables.

Status:

`compressed_two_path_calculator_initialized`

### 18.1. Minimal input packet

For each detector/readout cell \(x\), use:

$$
\mathcal D_x
=
\left(
p_a(x),
p_b(x),
\kappa_{ab}(x),
\theta_{ab}(x),
\Delta S_I(a,b;x),
\Theta_{q,I}
\right).
$$

where:

$$
\Theta_{q,I}
=
\frac{q_I}{\hbar_I}
\oint A_I.
$$

This replaces the full unresolved history-pair sum:

$$
\sum_{h\in a,h'\in b}
W(h)\overline{W(h')}
\Gamma_I(h,h')
$$

by a compressed interference packet.

Status:

`two_path_input_packet_defined`

### 18.2. Probability density readout

Define total phase:

$$
\Theta_I(x)
=
\frac{\Delta S_I(a,b;x)}{\hbar_I}
+
\Theta_{q,I}
+
\theta_{ab}(x).
$$

Then:

$$
\mu_x
=
p_a(x)+p_b(x)
+
2\sqrt{p_a(x)p_b(x)}
\kappa_{ab}(x)
\cos\Theta_I(x).
$$

Normalized probability:

$$
P(x)
=
\frac{\mu_x}{\int \mu_x\,dx}
$$

or for discrete detectors:

$$
P_i
=
\frac{\mu_i}{\sum_j\mu_j}.
$$

The normalization is a readout-context operation, not a global probability measure over all events.

Status:

`compressed_two_path_probability_readout`

### 18.3. Fringe observables

For fixed \(x\), phase sweep gives:

$$
\mu_{\max}
=
p_a+p_b
+
2\sqrt{p_ap_b}\kappa_{ab},
$$

and:

$$
\mu_{\min}
=
p_a+p_b
-
2\sqrt{p_ap_b}\kappa_{ab}.
$$

Visibility:

$$
V
=
\frac{\mu_{\max}-\mu_{\min}}
{\mu_{\max}+\mu_{\min}}
=
\frac{2\sqrt{p_ap_b}}{p_a+p_b}
\kappa_{ab}.
$$

Balanced case:

$$
p_a=p_b
\Rightarrow
V=\kappa_{ab}.
$$

Path bias:

$$
D
=
\frac{|p_a-p_b|}{p_a+p_b}.
$$

Then:

$$
V^2
\le
1-D^2
$$

when \(\kappa_{ab}\le1\).

Known gate:

wave-particle complementarity must be respected without adding collapse.

Status:

`visibility_distinguishability_gate`

### 18.4. Marking and eraser compression

Let marker/environment states be compressed into:

$$
\gamma_{ab}
=
\langle M_b|M_a\rangle.
$$

Then:

$$
\Gamma_{ab}
\mapsto
\Gamma_{ab}\gamma_{ab}.
$$

Thus:

$$
\kappa_{ab}^{\mathrm{marked}}
=
\kappa_{ab}^{0}
|\gamma_{ab}|.
$$

Full which-way marking:

$$
\langle M_b|M_a\rangle=0
\Rightarrow
V=0
$$

in the unconditioned readout.

Eraser conditioning uses a readout channel \(E\):

$$
\gamma_{ab}
\mapsto
\gamma_{ab|E}.
$$

Recovered visibility:

$$
V_E
=
\frac{2\sqrt{p_ap_b}}{p_a+p_b}
\kappa_{ab}^{0}
|\gamma_{ab|E}|.
$$

Known gate:

loss of unconditioned visibility does not imply irreversible factization if conditional channels recover coherence.

Status:

`compressed_quantum_eraser_calculator`

### 18.5. Irreversible factization test

Define recoverable coherence:

$$
\kappa_{\mathrm{rec}}
=
\max_E
\kappa_{ab}^{0}
|\gamma_{ab|E}|.
$$

Operational irreversibility:

$$
\Lambda_{\mathrm{irrev}}
=
-
\log
\frac{\kappa_{\mathrm{rec}}}{\kappa_{ab}^{0}}.
$$

If:

$$
\Lambda_{\mathrm{irrev}}=0,
$$

then the visibility loss was reversible marking.

If:

$$
\Lambda_{\mathrm{irrev}}>0,
$$

then uncontrolled inheritance channels have removed recoverable coherence.

Status:

`irreversibility_as_recoverability_loss`

### 18.6. AB phase calculator

Magnetic flux changes:

$$
\Theta_{q,I}
\mapsto
\Theta_{q,I}
+
\frac{q_I\delta\Phi_B}{\hbar_I}.
$$

Fringe shift:

$$
\delta N
=
\frac{1}{2\pi}
\frac{q_I\delta\Phi_B}{\hbar_I}
=
\frac{q_I\delta\Phi_B}{h_I}.
$$

One period:

$$
|\delta N|=1
\Rightarrow
\delta\Phi_B
=
\frac{h_I}{|q_I|}.
$$

Known gate:

AB phase and flux period must match the same \(h_I,q_I\) used in other phase/charge gates.

Status:

`compressed_ab_phase_calculator`

### 18.7. Residual packet

A compressed calculation must output residuals:

$$
\mathcal R_x
=
P_{\mathrm{obs}}(x)
-
P_{\mathrm{calc}}(x).
$$

Decompose:

$$
\mathcal R_x
=
\mathcal R_{\kappa,x}
+
\mathcal R_{\theta,x}
+
\mathcal R_{\mathrm{norm},x}
+
\mathcal R_{\mathrm{nonbilinear},x}.
$$

Interpretation:

1. \(\mathcal R_{\kappa}\): missing marking/coherence channel;
2. \(\mathcal R_{\theta}\): missing phase/action/connection term;
3. \(\mathcal R_{\mathrm{norm}}\): wrong readout context or detector model;
4. \(\mathcal R_{\mathrm{nonbilinear}}\): possible \(I_3\neq0\) sector.

Status:

`compressed_two_path_residual_packet`

### 18.8. Computational advantage criterion

The compressed calculator beats full modelling only if:

$$
\mathrm{dim}(\mathcal D_x)
\ll
\mathrm{dim}(\text{environment Hilbert model})
$$

and if it predicts:

1. unmarked visibility;
2. marked visibility;
3. eraser-conditioned visibility;
4. AB phase shift;
5. residual pattern;

with one shared packet update rule.

If \(\kappa\), \(\theta\), or \(\Theta_q\) are independently fitted per condition, the calculator loses predictive status.

Status:

`compressed_calculator_predictive_criterion`

### 18.9. What v5.19 closes

This section provides the first actual computational tool from the protolanguage:

$$
\mathcal D_x
\Rightarrow
P(x),V,\Lambda_{\mathrm{irrev}},\delta N,\mathcal R_x.
$$

It remains conditional because:

1. \(\kappa_{ab}\) must be derived or calibrated from marking dynamics;
2. \(\Delta S_I\) must be derived from \(\mathfrak s_I\);
3. \(\Theta_q\) must use the same charge/action bridge as AB and electrical gates.

Next target:

derive a packet update rule:

$$
\text{apparatus / marker channel}
\Rightarrow
\gamma_{ab}
\Rightarrow
\kappa_{ab}^{\mathrm{marked}}
$$

without full environment modelling.

Status:

`first_compressed_calculator_defined`

Marker-channel packet update:

`sections/19-marker-channel-update.md`

Matter-wave link phase residual:

`sections/55-matter-wave-link-phase-residual.md`
