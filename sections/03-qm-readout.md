## 3. QM Without QM Primitives

The following must not be taken as primitives:

$$
\psi,\quad \hat H,\quad \text{Born rule as postulate},\quad \text{collapse}
$$

They must arise as readouts.

### 3.1. Born-like readout

If:

$$
\Gamma_I(h,h')=\langle e_h,e_{h'}\rangle
$$

then:

$$
\mu(A)=
\left\|
\sum_{h\in A}W(h)e_h
\right\|^2
$$

The Born rule is not a postulate here; it is the diagonal readout of a positive inherited kernel.

### 3.2. Interference

For two alternatives \(a,b\):

$$
\mu(a\cup b)
=
|W_a|^2+|W_b|^2
+2\operatorname{Re}(W_a\overline{W_b}\Gamma_{ab})
$$

Visibility:

$$
V
=
\frac{2\sqrt{p_ap_b}}{p_a+p_b}
|\Gamma_{ab}|
$$

Balanced case:

$$
V=|\Gamma_{ab}|
$$

Which-way facticity:

$$
f(a,b)=1-|\Gamma_{ab}|
$$

### 3.2A. Planck constant as action-phase scale

The protolanguage does not fit \(\hbar_I\) separately per phenomenon.

It defines \(\hbar_I\) as the universal conversion between inherited action and actualization phase:

$$
\Delta\phi_I
=
\frac{\Delta S_I}{\hbar_I}
$$

Therefore:

$$
\hbar_I
=
\frac{\Delta S_I}{\Delta\phi_I}
$$

This becomes predictive only when \(\Delta S_I\) is computed from primitive inheritance.

Until then, \(\hbar_I\) is a universal calibration constant, not a derived number.

No-fit rule:

1. use one calibration route to set units;
2. compute all other phase/action phenomena with the same \(\hbar_I\);
3. any mismatch is a residual, not a re-fit.

Allowed calibration routes:

| Route | Formula |
|---|---|
| spectroscopy / clocks | \(\Delta E_I=h_I f\) |
| matter-wave interference | \(p\lambda=h_I\) |
| phase accumulation | \(\Delta\phi=\Delta S_I/\hbar_I\) |
| canonical sector | \([x,p]=i\hbar_I\) |

Independent verification requires:

$$
h_I^{(1)}
=
h_I^{(2)}
=
\cdots
=
h_{\mathrm{known}}
$$

inside experimental uncertainty.

Computational target:

$$
\chi^2(\hbar_I)
=
\sum_j
\frac{
\left[
O_j^{\mathrm{proto}}(\hbar_I)
-
O_j^{\mathrm{obs}}
\right]^2
}{
\sigma_j^2
}
$$

This fit is allowed only as a universality test after a single unit-setting calibration.

It is not accepted as a derivation of \(\hbar\).

Non-fitted derivation target:

$$
\mathfrak s_I(\eta)
\Rightarrow
S_I(h)
\Rightarrow
\hbar_I
$$

where \(\hbar_I\) is fixed by phase periodicity of the actualization kernel:

$$
\Gamma_I(h,h')
\text{ is invariant under }
S_I(h)-S_I(h')
\mapsto
S_I(h)-S_I(h')+2\pi\hbar_I
$$

Known gates:

$$
E=hf
$$

$$
p=\hbar k
$$

$$
\lambda=\frac{h}{p}
$$

$$
\Delta\phi=\frac{1}{\hbar}\int L\,dt
$$

Status:

`planck_constant_as_universal_action_phase_scale`

Not yet derived:

`numerical_hbar_from_primitive_update_action`

### 3.3. Sorkin gate

For pairwise disjoint \(A,B,C\):

$$
I_3(A,B,C)
=
\mu(A\cup B\cup C)
-\mu(A\cup B)
-\mu(A\cup C)
-\mu(B\cup C)
+\mu(A)+\mu(B)+\mu(C)
$$

In the bilinear sector:

$$
I_3=0
$$

Known gate:

> triple-slit experiments must remain compatible with \(I_3\approx0\).

### 3.4. Bell / CHSH

For binary readouts:

$$
E(x,y)=\sum_{a,b=\pm1}ab\,P(a,b|x,y)
$$

$$
S=E_{00}+E_{01}+E_{10}-E_{11}
$$

If a global factual context exists:

$$
|S|\le2
$$

Gram / Tsirelson sector:

$$
E(x,y)=-u_x\cdot v_y
$$

$$
|S|\le2\sqrt2
$$

No-signalling gate:

$$
\sum_aP(a,b|x,y)=\sum_aP(a,b|x',y)
$$

and:

$$
\sum_bP(a,b|x,y)=\sum_bP(a,b|x,y')
$$

Interpretation:

> entanglement lives in joint actualization; signal requires marginal change.

### 3.5. Quantum eraser

Marking:

$$
|\Gamma_{\mathrm{marked}}(a,b)|
<
|\Gamma_{\mathrm{unmarked}}(a,b)|
$$

Eraser recovery:

$$
|\Gamma_{\mathrm{cond},E}(a,b)|
\approx
|\Gamma_{\mathrm{unmarked}}(a,b)|
$$

Irreversible residual:

$$
\Lambda_{\mathrm{irrev}}
=
-\log
\frac{V_{\mathrm{rec,obs}}}{V_{\mathrm{rec,env}}}
$$

Known gate:

> reversible marking must allow conditional recovery; loss of visibility alone is not irreversible factization.

---
