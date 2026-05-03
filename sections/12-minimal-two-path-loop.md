## 12. Minimal Two-Path Predictive Loop

This is the smallest sector where the theory can become predictive.

It must reproduce ordinary two-path interference and Aharonov-Bohm phase with one shared action-phase scale.

Status:

`minimal_two_path_loop_initialized`

### 12.1. Two inherited alternatives

Let two alternative histories:

$$
h_a,\quad h_b
$$

end in the same readout cell \(x\).

Define local route weights:

$$
W_a(x)
=
\sqrt{p_a(x)}
\exp\left[
i\frac{S_a(x)}{\hbar_I}
\right]
$$

and:

$$
W_b(x)
=
\sqrt{p_b(x)}
\exp\left[
i\frac{S_b(x)}{\hbar_I}
\right].
$$

The inherited coherence kernel between the alternatives is:

$$
\Gamma_{ab}(x)
=
\kappa_{ab}(x)e^{i\theta_{ab}(x)},
\qquad
0\le\kappa_{ab}\le1.
$$

Actualization gives:

$$
\mu_x(a\cup b)
=
p_a(x)+p_b(x)
+2\sqrt{p_a(x)p_b(x)}\,
\kappa_{ab}(x)
\cos\left[
\frac{S_a(x)-S_b(x)}{\hbar_I}
+\theta_{ab}(x)
\right].
$$

This is not an added quantum postulate.

It follows from the bilinear actualization calculus once the action-phase bridge is admitted.

Balanced case:

$$
p_a=p_b
\quad\Rightarrow\quad
V(x)=\kappa_{ab}(x).
$$

Known gate:

ordinary two-path fringe visibility is controlled by coherence, not by a collapse primitive.

Status:

`two_path_interference_formula_conditional_on_action_bridge`

### 12.2. Primitive action difference

The inherited action difference is:

$$
\Delta S_I(a,b)
=
S_a-S_b.
$$

The primitive target is:

$$
\Delta S_I(a,b)
=
\sum_{\eta\in h_a}\mathfrak s_I(\eta)
-
\sum_{\eta\in h_b}\mathfrak s_I(\eta).
$$

Continuum readout:

$$
\Delta S_I(a,b)
=
\int_{h_a}L_I\,d\tau_I
-
\int_{h_b}L_I\,d\tau_I.
$$

The phase difference is:

$$
\Delta\phi_I(a,b)
=
\frac{\Delta S_I(a,b)}{\hbar_I}.
$$

Therefore a neutral two-path experiment tests:

$$
\Delta\phi_I
\mod 2\pi
$$

and not an absolute action value.

The next derivation must fix \(\mathfrak s_I\) enough to compute \(\Delta S_I\), not merely fit a phase.

Status:

`primitive_action_difference_target`

### 12.3. Charged phase connection

Electromagnetic readout enters as a phase connection.

For a charged history \(h\):

$$
\phi_{q,I}(h)
=
\frac{q_I}{\hbar_I}
\int_h A_{I,\mu}\,dx^\mu.
$$

For the closed two-path loop:

$$
\Delta\phi_{q,I}(a,b)
=
\frac{q_I}{\hbar_I}
\oint A_{I,\mu}\,dx^\mu.
$$

Define the connection-loop readout:

$$
\mathcal F_{A,I}
=
\oint A_{I,\mu}\,dx^\mu.
$$

In the static magnetic Aharonov-Bohm gate:

$$
\mathcal F_{A,I}
=
\oint \mathbf A_I\cdot d\mathbf x
=
\int \mathbf B_I\cdot d\mathbf S
\equiv
\Phi_{B,I}.
$$

Then:

$$
\Delta\phi_{AB,I}
=
\frac{q_I\Phi_{B,I}}{\hbar_I}.
$$

Known Aharonov-Bohm gate:

$$
\Delta\phi_{AB}
=
\frac{q\Phi_B}{\hbar}.
$$

This gate is strong because the phase can shift even where the local force on the path is zero.

The theory must therefore reconstruct connection-phase readout, not only force readout.

Status:

`charged_phase_connection_gate`

### 12.4. Combined fringe formula

For a charged two-path experiment:

$$
\mu_x(\Phi_B)
=
p_a(x)+p_b(x)
+2\sqrt{p_a(x)p_b(x)}\,
\kappa_{ab}(x)
\cos\left[
\frac{\Delta S_I(a,b)}{\hbar_I}
+\frac{q_I\Phi_{B,I}}{\hbar_I}
+\theta_{ab}(x)
\right].
$$

Flux changes the fringe phase by:

$$
\delta\phi
=
\frac{q_I\,\delta\Phi_{B,I}}{\hbar_I}.
$$

One full fringe period satisfies:

$$
\delta\phi=2\pi.
$$

Therefore the flux period is:

$$
\Phi_{0,I}
=
\frac{h_I}{|q_I|}.
$$

For electron charge magnitude:

$$
\Phi_{0,I}^{(e)}
=
\frac{h_I}{e_I}.
$$

This is an immediate no-refit bridge between:

1. neutral action-phase interference;
2. charged connection phase;
3. charge scale.

Status:

`two_path_ab_flux_period_gate`

### 12.5. No-refit closure equations

One allowed calibration:

$$
h_I
\leftarrow
\text{neutral interference}
$$

or:

$$
h_I
\leftarrow
\text{spectroscopy}.
$$

Then the Aharonov-Bohm flux period must obey:

$$
h_I
=
|q_I|\Phi_{0,I}^{AB}
$$

without changing \(h_I\).

Equivalently:

$$
\frac{|q_I|\Phi_{0,I}^{AB}}{h_I}
\to
1.
$$

The first closure observable is:

$$
\mathcal C_{AB}
=
\left\{
\frac{h_I^{\mathrm{neutral}}}{|q_I|\Phi_{0,I}^{AB}},
\frac{h_I^{\mathrm{spectroscopy}}}{|q_I|\Phi_{0,I}^{AB}}
\right\}
\to
\{1,1\}.
$$

If this fails, the action-phase bridge and charge-phase bridge are not the same primitive phase readout.

Status:

`ab_neutral_phase_no_refit_closure`

### 12.6. Relation to fine-structure constant

The Aharonov-Bohm gate fixes the ratio:

$$
\frac{q_I}{\hbar_I}
$$

through phase response.

The fine-structure gate requires the dimensionless coupling:

$$
\alpha_{\mathrm{em},I}
=
\frac{e_I^2}{4\pi\epsilon_{0,I}\hbar_I c_I}.
$$

In natural bridge units:

$$
\hbar_I=c_I=1,
$$

this becomes:

$$
\alpha_{\mathrm{em},I}
=
\frac{g_I^2}{4\pi}.
$$

Therefore the next non-fitted target is:

$$
\mathfrak q_I(\eta)
\Rightarrow
g_I
\Rightarrow
\alpha_{\mathrm{em},I}.
$$

The AB sector alone does not derive \(\alpha_{\mathrm{em}}\).

It only locks charge phase to the same \(\hbar_I\).

Predictive value appears when the same \(g_I\) also passes spectroscopy, scattering, Josephson, and Hall gates.

Status:

`ab_phase_to_alpha_bridge_not_yet_alpha_derivation`

### 12.7. Residual channels

The minimal two-path loop has only a few allowed residuals.

Visibility residual:

$$
V_{\mathrm{obs}}
-
\kappa_{ab}
=
\mathcal R_V.
$$

Phase residual:

$$
\Delta\phi_{\mathrm{obs}}
-
\left(
\frac{\Delta S_I}{\hbar_I}
+
\frac{q_I\Phi_{B,I}}{\hbar_I}
\right)
=
\mathcal R_{\phi}.
$$

Non-bilinear residual:

$$
I_3
=
\mathcal R_{I_3}.
$$

Allowed interpretation:

1. \(\mathcal R_V\) may come from uncontrolled marking / environment;
2. \(\mathcal R_{\phi}\) may indicate missing connection or clock-action mismatch;
3. \(\mathcal R_{I_3}\) would challenge the bilinear actualization sector.

Forbidden move:

absorb these residuals by changing \(\hbar_I\) separately in each experiment.

Status:

`minimal_loop_residual_channels_declared`

### 12.8. What v5.13 actually proves

This section proves conditionally:

$$
\text{bilinear actualization}
+
\text{action-phase bridge}
+
\text{charge-phase connection}
\Rightarrow
\text{two-path + AB phase formulas}.
$$

It does not yet prove:

1. numerical \(\hbar\);
2. numerical \(\alpha_{\mathrm{em}}\);
3. primitive origin of \(g_I\);
4. unique form of \(\mathfrak s_I\);
5. unique form of \(\mathfrak q_I\).

It does define the first concrete computation target:

$$
\left(
\mathfrak s_I,\mathfrak q_I
\right)
\Rightarrow
\left(
\Delta S_I,
\Phi_{0,I}^{AB},
\alpha_{\mathrm{em},I}
\right)
$$

with one shared \(\hbar_I\).

Status:

`first_formula_level_predictive_loop`

Primitive support conditions for the phase structures used here:

`sections/13-primitive-phase-bridges.md`
