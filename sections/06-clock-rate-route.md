## 6. Clock-Rate Field Derivation

Status:

`clock_protocol_layer_extended`

Goal of this section:

> begin deriving the GR sector through a clock-rate field, rather than only describing the route.

We do not derive the full Einstein equations.

We strengthen the first testable bridge:

$$
r_C(E)
\Rightarrow
\Phi_I(E)
\Rightarrow
\text{redshift}
\Rightarrow
\text{Newtonian source law}
$$

### 6.1. Clock-rate field

Let \(C\) be a calibrated clock subsystem.

The number of ticks in a neighborhood of event \(E\):

$$
N_C(E;\Delta\lambda)
$$

where \(\lambda\) is an internal ordering parameter for inherited updates.

Clock-rate field:

$$
r_C(E)
=
\lim_{\Delta\lambda\to0}
\frac{N_C(E;\Delta\lambda)}
{\Delta\lambda}
$$

\(\lambda\) is not an observable clock.

It is a gauge bookkeeping parameter.

Under:

$$
\lambda\mapsto\lambda'=f(\lambda)
$$

raw rates transform as:

$$
r_C(E)\mapsto\frac{r_C(E)}{f'(\lambda_E)}
$$

Therefore raw \(r_C(E)\) is not a physical readout.

Only protocol ratios are admissible.

For a co-sampled reference chain \(R\):

$$
\widehat r_C(E;R)
=
\frac{r_C(E)}{r_R(E)}
$$

is invariant under \(\lambda\)-reparametrization.

Reference rate in a remote / flat calibration domain:

$$
\widehat r_{C,\infty}
$$

Clock-specific dimensionless factor:

$$
\chi_C(E)
=
\frac{\widehat r_C(E;R)}
{\widehat r_{C,\infty}}
$$

Known flat gate:

$$
\rho_I\to0
\Rightarrow
\chi_C(E)\to1
$$

Clock universality is not automatic.

The GR route may use a single field \(\chi(E)\) only if admissible clocks agree:

$$
\left|
\frac{
\chi_C(E)/\chi_C(F)
}{
\chi_{C'}(E)/\chi_{C'}(F)
}
-1
\right|
\le
\epsilon_{\mathrm{EP}}
$$

for all calibrated clocks \(C,C'\) in the same readout domain.

If this gate fails, the model describes clock-dependent coupling, not GR.

When the gate passes:

$$
\chi_C(E)\approx\chi(E)
$$

### 6.1A. Admissible-clock universality

Clock universality is derived only for admissible calibrated clocks.

A calibrated clock \(C\) is admissible in a weak static domain if its internal transition generator has the form:

$$
K_C(E)
=
\chi(E)K_C^{\infty}
+
\Delta K_C(E)
$$

where \(K_C^{\infty}\) is the flat-domain clock generator and \(\Delta K_C\) is the non-universal residual.

For a transition \(n\to m\):

$$
f_{C,nm}(E)
=
\chi(E)f_{C,nm}^{\infty}
\left[
1+\delta_{C,nm}(E)
\right]
$$

with:

$$
\delta_{C,nm}(E)
=
\frac{
\langle n|\Delta K_C(E)|n\rangle
-
\langle m|\Delta K_C(E)|m\rangle
}{
\chi(E)
\left(
\langle n|K_C^\infty|n\rangle
-
\langle m|K_C^\infty|m\rangle
\right)
}
$$

If:

$$
|\delta_{C,nm}(E)-\delta_{C,nm}(F)|
\le
\epsilon_{\mathrm{LPI}}
$$

for the tested domain, then:

$$
\frac{f_{C,nm}(E)}{f_{C,nm}(F)}
=
\frac{\chi(E)}{\chi(F)}
\left[
1+O(\epsilon_{\mathrm{LPI}})
\right]
$$

Thus:

$$
\chi_C(E)
=
\chi(E)
\left[
1+O(\epsilon_{\mathrm{LPI}})
\right]
$$

Admissible-clock theorem:

> If inheritance deformation rescales the local update generator universally and all clock-dependent residuals are below LPI bounds, then all admissible calibrated clocks measure the same \(\chi(E)\) within experimental tolerance.

The standard redshift test form is:

$$
\left(
\frac{f_A-f_B}{f_B}
\right)_C
=
(1+\alpha_C)
\frac{\Phi_I(A)-\Phi_I(B)}{c_I^2}
+O(\Phi_I^2/c_I^4)
$$

Clock universality requires:

$$
|\alpha_C-\alpha_{C'}|
\le
\epsilon_{\mathrm{LPI}}
$$

for all admissible clocks \(C,C'\).

The differential clock-ratio gate is:

$$
\left|
\frac{
\left[f_C(A)/f_C(B)\right]
}{
\left[f_{C'}(A)/f_{C'}(B)\right]
}
-1
\right|
\le
\epsilon_{\mathrm{LPI}}
$$

The WEP/Eötvös consistency gate is:

$$
\eta_{AB}
=
\frac{2|a_A-a_B|}{|a_A+a_B|}
\le
\epsilon_{\mathrm{WEP}}
$$

because the same composition-dependent coupling sector must also satisfy free-fall universality.

Known-experiment interpretation:

1. gravitational redshift fixes the universal coefficient \(1/c_I^2\);
2. clock-comparison redshift tests bound \(\alpha_C-\alpha_{C'}\);
3. WEP/Eötvös tests bound composition-dependent coupling of internal energy;
4. any nonzero \(\delta_C\) is not hidden: it is an experimental residual.

Step clock readout rule:

`sections/65-step-clock-readout-rule.md`

Status:

`clock_universality_derived_for_admissible_clocks`

Not yet derived:

`all_real_clocks_are_admissible`

### 6.1B. Clock protocols and residual decomposition

A clock readout is not a raw device reading.

It is a protocol:

$$
\mathscr P_C
=
(C,R,W,T,\mathcal K)
$$

where:

1. \(C\) is the clock subsystem;
2. \(R\) is the co-sampled reference chain;
3. \(W\) is the local comparison window;
4. \(T\) is the chosen transition or tick rule;
5. \(\mathcal K\) is the calibration map to the flat-domain rate.

Protocol output:

$$
\chi_{\mathscr P_C}(E)
=
\frac{
\widehat r_C(E;R,W,T)
}{
\widehat r_{C,\infty}(T,\mathcal K)
}
$$

Admissibility requires protocol invariance:

$$
\chi_{\mathscr P_C}(E)
=
\chi(E)
\left[
1+\delta_{\mathscr P_C}(E)
\right]
$$

with:

$$
|\delta_{\mathscr P_C}(E)|
\le
\epsilon_{\mathrm{clock}}
$$

inside the tested domain.

Residual decomposition:

$$
\delta_{\mathscr P_C}
=
\delta_C^{\mathrm{drift}}
+
\delta_C^{\mathrm{env}}
+
\alpha_C\frac{\Phi_I}{c_I^2}
+
\beta_C\frac{v^2}{c_I^2}
+
\xi_C^i\frac{\partial_i\Phi_I L_C}{c_I^2}
+
O(c_I^{-4})
$$

where:

1. \(\delta_C^{\mathrm{drift}}\) is local device drift;
2. \(\delta_C^{\mathrm{env}}\) is environmental perturbation;
3. \(\alpha_C\) is LPI/redshift violation;
4. \(\beta_C\) is kinematic time-dilation violation;
5. \(\xi_C^i\) is finite-size/tidal clock sensitivity.

Calibration may subtract local drift and environmental systematics.

It may not hide:

$$
\alpha_C,\quad\beta_C,\quad\xi_C^i
$$

because these are physical residuals.

Combined clock readout:

$$
\frac{d\tau_C}{dt}
=
\chi(E)
\sqrt{1-\frac{v^2}{c_I^2}}
\left[
1+\delta_{\mathscr P_C}
\right]
$$

Weak field:

$$
\frac{d\tau_C}{dt}
\approx
1+\frac{\Phi_I}{c_I^2}
-\frac{v^2}{2c_I^2}
+\delta_{\mathscr P_C}
$$

Frequency comparison between two clock protocols:

$$
\frac{f_{\mathscr P_C,A}}{f_{\mathscr P_{C'},B}}
=
\frac{\chi(A)}{\chi(B)}
\frac{
\sqrt{1-v_A^2/c_I^2}
}{
\sqrt{1-v_B^2/c_I^2}
}
\left[
1+\delta_{\mathscr P_C}(A)-\delta_{\mathscr P_{C'}}(B)
\right]
$$

Weak comparison formula:

$$
\frac{\Delta f}{f}
\approx
\frac{\Delta\Phi_I}{c_I^2}
-
\frac{\Delta v^2}{2c_I^2}
+
\Delta\delta_{\mathscr P}
$$

This is the operational clock formula that must reproduce gravitational redshift, special-relativistic time dilation, and satellite-clock corrections in the tested domain.

Static closed-loop consistency:

$$
\prod_{k=1}^{N}
\frac{f_{C_k}(E_k)}
{f_{C_{k+1}}(E_{k+1})}
=
1+O(\epsilon_{\mathrm{loop}})
$$

for a closed static comparison loop with:

$$
C_{N+1}=C_1,\qquad E_{N+1}=E_1
$$

A nonzero loop residual is not absorbed into \(\Phi_I\).

It is a physical signal:

$$
\mathcal R_{\mathrm{clock-loop}}
\neq0
$$

Stability gate:

$$
\sigma_y^{(C)}(T_{\mathrm{avg}})
\le
\epsilon_{\mathrm{stab}}(T_{\mathrm{avg}})
$$

where \(\sigma_y\) is fractional frequency instability over averaging time \(T_{\mathrm{avg}}\).

Known-experiment gates for clock protocols:

| Gate | Required formula |
|---|---|
| gravitational redshift | \(\Delta f/f=\Delta\Phi/c^2\) |
| special-relativistic dilation | \(d\tau/dt=\sqrt{1-v^2/c^2}\) |
| weak combined clock formula | \(d\tau/dt\approx1+\Phi/c^2-v^2/(2c^2)\) |
| LPI comparison | \(|\alpha_C-\alpha_{C'}|\le\epsilon_{\mathrm{LPI}}\) |
| kinematic universality | \(|\beta_C-\beta_{C'}|\le\epsilon_{\mathrm{boost}}\) |
| clock-loop closure | loop residual \(\le\epsilon_{\mathrm{loop}}\) |

Status:

`clock_protocol_residual_calculus`

### 6.2. Potential from clock-rate

For the universal sector define inheritance gravitational potential:

$$
\Phi_I(E)
=
c_I^2\log\chi(E)
$$

Equivalently:

$$
\chi(E)=e^{\Phi_I(E)/c_I^2}
$$

Weak-field expansion:

$$
|\Phi_I|\ll c_I^2
\Rightarrow
\chi(E)\approx1+\frac{\Phi_I(E)}{c_I^2}
$$

This definition is chosen because clock ratios multiply, while potentials add:

$$
\frac{\chi(A)}{\chi(B)}
=
e^{[\Phi_I(A)-\Phi_I(B)]/c_I^2}
$$

Sign convention:

$$
\Phi_I(\infty)=0
$$

Attractive positive sources have:

$$
\Phi_I<0
$$

near the source.

Higher-potential clocks tick faster:

$$
\Phi_I(A)>\Phi_I(B)
\Rightarrow
f_A>f_B
$$

### 6.3. Redshift derivation

Clock frequency readout:

$$
f_C(E)\propto\widehat r_C(E;R)
$$

Therefore:

$$
\frac{f_A}{f_B}
=
\frac{\chi(A)}{\chi(B)}
=
e^{[\Phi_I(A)-\Phi_I(B)]/c_I^2}
$$

Weak field:

$$
\frac{f_A-f_B}{f_B}
\approx
\frac{\Phi_I(A)-\Phi_I(B)}{c_I^2}
$$

Known gate:

$$
\left|
\left(\frac{\Delta\nu}{\nu}\right)_{\mathrm{proto}}
-
\left(\frac{\Delta\nu}{\nu}\right)_{\mathrm{obs}}
\right|
\le n\sigma
$$

Status:

`derived_from_clock_rate_definition`

not:

`full_GR_derived`

### 6.4. Source readout without volume circularity

Inheritance activity in a region:

$$
\mathcal N_I(U)
=
\sum_{\eta:\mathrm{supp}(\eta)\subset U}\omega_\eta
$$

This is an uncalibrated activity count/weight, not yet a geometric source.

Pre-geometric counting/activity measure:

$$
\nu_{\mathrm{count}}(U)
$$

Pre-geometric activity density:

$$
\widetilde\rho_I(E)
=
\lim_{U\to E}
\frac{\mathcal N_I(U)}
{\nu_{\mathrm{count}}(U)}
$$

After a spatial readout \(S\) is reconstructed, it has geometric volume:

$$
d\nu_{G,S}
$$

Source-weighted inherited activity:

$$
M_I(U)
=
\sum_{\eta:\mathrm{supp}(\eta)\subset U}m_I(\eta)
$$

The geometric source density is:

$$
\rho_I^G
=
\frac{dM_I}{d\nu_{G,S}}
$$

Section 25 reduces \(m_I(\eta)\) to the clock-strain response charge \(q_{\Phi,I}(\eta)\).

This separation prevents the circular move:

$$
\rho_I
\Rightarrow
\text{geometry}
\Rightarrow
\text{volume}
\Rightarrow
\rho_I
$$

Matter-energy density readout:

$$
\rho_m c_I^2
=
\zeta_I\rho_I^G
$$

where \(\zeta_I\) converts inheritance activity density into energy-density units.

This matter bridge remains a calibration bridge.

Status:

`volume_circularity_removed`

### 6.5. Source law from minimal clock-rate distortion

Define:

$$
\varphi
=
\log\chi
=
\frac{\Phi_I}{c_I^2}
$$

The functional below is not arbitrary.

It is the lowest-order coarse-grained form forced by the following weak-field inheritance conditions.

Coarse-grained source-law conditions:

1. locality: only neighbouring readout cells contribute at leading order;
2. additivity: disjoint inheritance regions add their activity costs;
3. flat stability: \(\varphi=0\) is the no-source minimum;
4. orientation symmetry: reversing a neighbour link does not change the cost;
5. isotropy: no preferred spatial direction remains after coarse-graining;
6. long-range Newtonian gate: no local field-mass term \(\mu_{\varphi,I}^2\varphi^2\) at leading order.

Effective source-law theorem:

> Under these six conditions, the unique lowest-derivative scalar functional for a weak static clock-rate field is a quadratic strain term plus a local linear source coupling, up to boundary terms and higher-order residuals.

The coefficients must satisfy:

$$
\alpha_I>0,
\qquad
\beta_I>0
$$

where \(\alpha_I>0\) gives flat stability and \(\beta_I>0\) fixes the attractive-source sign.

Section 26 reduces \(\alpha_I\) to coarse-grained clock-link stiffness.

For neighbouring readout cells \(E,F\), define clock-rate strain:

$$
s_{EF}
=
\varphi(F)-\varphi(E)
$$

Flat stability and orientation symmetry remove the linear term:

$$
C_{EF}(s)
=
\frac12a_{EF}s_{EF}^2
+O(s_{EF}^4)
$$

The leading source coupling is local and additive:

$$
C_{\mathrm{src}}
=
\sum_\eta
q_{\Phi,I}(\eta)
\varphi(E_\eta)
+O(q_{\Phi,I}\varphi^2)
$$

Thus the microscopic weak-field cost is:

$$
\mathcal F_{\mathrm{micro}}
=
\sum_{\langle EF\rangle}
\frac12a_{EF}
[\varphi(F)-\varphi(E)]^2
+
\sum_\eta
q_{\Phi,I}(\eta)\varphi(E_\eta)
+
O(s^4,q_{\Phi,I}\varphi^2)
$$

Coarse-graining over a reconstructed spatial readout \(S\) gives:

$$
\sum_{\langle EF\rangle}
\frac12a_{EF}
[\varphi(F)-\varphi(E)]^2
\to
\int_S
\frac{\alpha_I}{2}
q_I^{ij}\partial_i\varphi\partial_j\varphi
d\nu_{G,S}
$$

and:

$$
\sum_\eta
q_{\Phi,I}(\eta)\varphi(E_\eta)
\to
\int_S
\beta_I\rho_I^G\varphi\,d\nu_{G,S}
$$

Therefore, in weak, static, approximately isotropic readout, the lowest-order local distortion functional is:

$$
\mathcal F[\varphi]
=
\int_S
\left[
\frac{\alpha_I}{2}
q_I^{ij}\partial_i\varphi\partial_j\varphi
+
\beta_I\rho_I^G\varphi
\right]
d\nu_{G,S}
$$

Boundary condition:

$$
\varphi(\infty)=0
$$

with fixed boundary variation.

Variation:

$$
\delta\mathcal F
=
\int_S
\left[
-\alpha_I\Delta_S\varphi
+
\beta_I\rho_I^G
\right]
\delta\varphi\,d\nu_{G,S}
$$

Stationarity for arbitrary \(\delta\varphi\) gives:

$$
\Delta_S\varphi
=
\frac{\beta_I}{\alpha_I}\rho_I^G
$$

Therefore:

$$
\Delta_S\Phi_I
=
\frac{c_I^2\beta_I}{\alpha_I}\rho_I^G
$$

Using:

$$
\rho_m c_I^2=\zeta_I\rho_I^G
$$

the Newtonian Poisson form is recovered conditionally:

$$
\Delta_S\Phi_I
=
4\pi G_I\rho_m
$$

if:

$$
4\pi G_I
=
\frac{c_I^4\beta_I}{\alpha_I\zeta_I}
$$

Equivalently, by Gauss:

$$
\oint_{\partial U}
\nabla_S\Phi_I\cdot d\mathbf S
=
4\pi G_I
\int_U\rho_m\,d\nu_{G,S}
$$

This means:

> net outward clock-rate strain through a boundary equals calibrated inherited activity enclosed.

Status:

`conditional_coarse_grained_source_law_candidate`

Not yet derived:

`uniqueness_of_primitive_support_conditions`

### 6.5A. Primitive support for coarse-graining conditions

The six coarse-graining conditions are not taken as free assumptions.

They follow as the accepted weak-field sector if the primitive inheritance layer satisfies the following support conditions.

Primitive support conditions:

1. bounded inheritance neighbourhood:

$$
a_{EF}=0
\quad
\text{outside the stable readout neighbourhood}
\quad
\mathcal N_S(E)
$$

up to higher-gradient residuals;

2. disjoint support factorization:

$$
\mathcal C(U\cup V)
=
\mathcal C(U)+\mathcal C(V)
$$

when \(U,V\) have no shared boundary inheritance links;

3. static reciprocity:

$$
J_I=0
\Rightarrow
a_{EF}=a_{FE}
$$

for the weak static sector;

4. flat vacuum stationarity:

$$
\rho_I^G=0
\Rightarrow
\varphi=\mathrm{const}
$$

and the calibration \(\chi_\infty=1\) fixes:

$$
\varphi=0
$$

5. isotropic fixed point:

$$
\sum_{F\in\mathcal N_S(E)}
a_{EF}\ell_{EF}^i\ell_{EF}^j
=
\alpha_I q_I^{ij}
+O(\epsilon_{\mathrm{aniso}})
$$

where \(\ell_{EF}^i\) is the readout displacement from \(E\) to \(F\);

6. long-range masslessness gate:

$$
\mu_{\varphi,I}^2\varphi^2
$$

is excluded at leading order because it would replace the Newtonian Green kernel by a Yukawa kernel.

The accepted weak-field sector therefore requires:

$$
\mu_{\varphi,I}^2L_{\mathrm{test}}^2
\ll
\epsilon_{\mathrm{Newton}}
$$

on tested gravitational length scales.

Primitive-to-coarse-graining theorem:

> If the primitive inheritance layer satisfies bounded neighbourhood, disjoint support factorization, static reciprocity, flat vacuum stationarity, isotropic fixed point, and the long-range masslessness gate, then the six source-law coarse-graining conditions in 6.5 follow in the weak static sector.

Derivation map:

| Coarse-graining condition | Primitive support |
|---|---|
| locality | bounded inheritance neighbourhood |
| additivity | disjoint support factorization |
| flat stability | flat vacuum stationarity |
| orientation symmetry | static reciprocity |
| isotropy | isotropic fixed point |
| no local mass term | long-range masslessness gate |

Residual terms:

$$
\mathcal F
=
\mathcal F_0
+O(s^4,q_{\Phi,I}\varphi^2,\epsilon_{\mathrm{aniso}},\mu_{\varphi,I}^2\varphi^2)
$$

Known-experiment interpretation:

1. \(\mu_{\varphi,I}^2\neq0\) creates finite-range deviations from Newtonian gravity;
2. \(\epsilon_{\mathrm{aniso}}\neq0\) creates direction-dependent free-fall/redshift residuals;
3. non-additive boundary terms create source-superposition residuals.

Status:

`primitive_support_reduction_complete`

Not yet derived:

`uniqueness_of_primitive_support_conditions`

### 6.6. Weak-field interval, spatial curvature, and free fall

Use weak-field metric readout:

$$
ds_I^2
=
c_I^2e^{2\Phi_I/c_I^2}dt^2
-
e^{-2\gamma_I\Phi_I/c_I^2}d\ell^2
$$

with:

$$
d\ell^2=q_{ij}dx^idx^j
$$

Weak form:

$$
ds_I^2
\approx
c_I^2
\left(1+\frac{2\Phi_I}{c_I^2}\right)dt^2
-
\left(1-\frac{2\gamma_I\Phi_I}{c_I^2}\right)d\ell^2
$$

For slow motion, the leading proper-time expansion is:

$$
d\tau_I
=
dt
\sqrt{
1+\frac{2\Phi_I}{c_I^2}
-
\frac{v^2}{c_I^2}
}
$$

Weak expansion:

$$
d\tau_I
\approx
dt
\left[
1+\frac{\Phi_I}{c_I^2}
-\frac{v^2}{2c_I^2}
\right]
$$

up to \(O(\Phi_Iv^2/c_I^4,\Phi_I^2/c_I^4)\).

Free motion extremizes:

$$
\tau_I=\int d\tau_I
$$

Equivalently, minimize the sign-flipped functional:

$$
L_{\mathrm{eff}}
=
\frac12v^2-\Phi_I
$$

Euler-Lagrange:

$$
\frac{d^2x^i}{dt^2}
=
-\partial_i\Phi_I
$$

Thus Newtonian free fall follows conditionally from:

1. clock-rate potential;
2. weak-field interval readout;
3. extremal proper-time chain.

The parameter \(\gamma_I\) does not affect leading slow-body free fall, but it affects null propagation.

Light bending target:

$$
\Delta\theta
=
2(1+\gamma_I)\frac{G_IM}{c_I^2b}
$$

GR fixed-point target:

$$
\gamma_I\to1
$$

Status:

`derived_conditional_on_weak_field_interval_ansatz`

### 6.7. PPN weak-field gate

The clock-rate route must not collapse redshift, Newtonian limit, and full weak-field GR into one test.

For PPN notation define positive Newtonian potential:

$$
U_I=-\Phi_I\ge0
$$

Use PPN readout:

$$
g_{00}
=
1-\frac{2U_I}{c_I^2}
+2\beta_I^{\mathrm{PPN}}
\frac{U_I^2}{c_I^4}
+O(c_I^{-6})
$$

$$
g_{ij}
=
-
\left(
1+2\gamma_I^{\mathrm{PPN}}
\frac{U_I}{c_I^2}
\right)\delta_{ij}
+O(c_I^{-4})
$$

$$
g_{0i}=O(c_I^{-3})
$$

GR target:

$$
\beta_I^{\mathrm{PPN}}\to1,
\qquad
\gamma_I^{\mathrm{PPN}}\to1
$$

Gate separation:

| Gate | Mainly fixes |
|---|---|
| redshift | \(g_{00}\) at \(O(c_I^{-2})\) |
| Newtonian free fall | \(\nabla\Phi_I\) and \(g_{00}\) |
| light bending | \(\gamma_I^{\mathrm{PPN}}\) |
| Shapiro delay | \(\gamma_I^{\mathrm{PPN}}\) |
| perihelion | \(\beta_I^{\mathrm{PPN}}\), \(\gamma_I^{\mathrm{PPN}}\), higher \(g_{00}\) |

### 6.8. What is actually derived here

Derived:

1. gauge-safe clock readout:

$$
\widehat r_C(E;R)=r_C(E)/r_R(E)
$$

2. admissible-clock universality:

$$
K_C(E)=\chi(E)K_C^\infty+\Delta K_C(E)
\Rightarrow
\chi_C(E)=\chi(E)[1+O(\epsilon_{\mathrm{LPI}})]
$$

3. protocol-level clock residual calculus:

$$
\mathscr P_C=(C,R,W,T,\mathcal K)
\Rightarrow
\delta_{\mathscr P_C}
=
\delta_C^{\mathrm{drift}}
+
\delta_C^{\mathrm{env}}
+
\alpha_C\frac{\Phi_I}{c_I^2}
+
\beta_C\frac{v^2}{c_I^2}
+
\xi_C^i\frac{\partial_i\Phi_I L_C}{c_I^2}
+
O(c_I^{-4})
$$

4. combined redshift/time-dilation clock readout:

$$
\frac{d\tau_C}{dt}
\approx
1+\frac{\Phi_I}{c_I^2}
-\frac{v^2}{2c_I^2}
+\delta_{\mathscr P_C}
$$

5. potential from universal clock-rate:

$$
\Phi_I=c_I^2\log\chi
$$

6. gravitational redshift from clock-rate ratios:

$$
f_A/f_B=e^{[\Phi_I(A)-\Phi_I(B)]/c_I^2}
$$

7. weak-field redshift:

$$
\Delta\nu/\nu\approx\Delta\Phi_I/c_I^2
$$

8. primitive support reduction for the source-law coarse-graining conditions:

$$
\mathcal H,I,\eta
\Rightarrow
\{\mathrm{locality,additivity,isotropy,flat\ stability}\}
$$

under the weak static support conditions in 6.5A.

9. lowest-order coarse-grained origin of the clock-rate distortion functional:

$$
\mathcal F_{\mathrm{micro}}
\to
\mathcal F[\varphi]
$$

10. conditional Poisson candidate law from that functional:

$$
\Delta_S\Phi_I
=
\frac{c_I^2\beta_I}{\alpha_I}\rho_I^G
$$

11. Newtonian acceleration from extremal \(\tau_I\):

$$
\ddot x^i=-\partial_i\Phi_I
$$

Not derived yet:

1. uniqueness of the primitive support conditions;
2. proof that all real clocks are admissible;
3. complete stochastic clock-noise model;
4. value of \(G_I\);
5. why \(\gamma_I^{\mathrm{PPN}}=1\);
6. full Einstein equations.
7. matter calibration \(\rho_I^G\to\rho_m\);
8. microscopic link stiffness \(a_{EF}\);
9. event-density calibration \(\lambda_I\).

### 6.9. Known-experiment gate for this route

| Gate | Formula | Status |
|---|---|---|
| clock universality | \(|\alpha_C-\alpha_{C'}|\le\epsilon_{\mathrm{LPI}}\) | derived for admissible clocks |
| \(\lambda\)-gauge | raw \(r_C\) unobservable; ratios invariant | protected |
| gravitational redshift | \(\Delta\nu/\nu\approx\Delta\Phi_I/c_I^2\) | derived weak-field |
| special-relativistic dilation | \(d\tau/dt=\sqrt{1-v^2/c_I^2}\) | required fixed point |
| combined clock formula | \(d\tau/dt\approx1+\Phi_I/c_I^2-v^2/(2c_I^2)\) | protocol readout |
| LPI clock comparison | clock-ratio residual \(\le\epsilon_{\mathrm{LPI}}\) | residual gate |
| boost universality | \(|\beta_C-\beta_{C'}|\le\epsilon_{\mathrm{boost}}\) | residual gate |
| loop closure | \(\mathcal R_{\mathrm{clock-loop}}\le\epsilon_{\mathrm{loop}}\) | static consistency |
| WEP/Eötvös | \(\eta_{AB}\le\epsilon_{\mathrm{WEP}}\) | consistency gate |
| Newtonian free fall | \(\ddot x=-\nabla\Phi_I\) | conditional derivation |
| Poisson gravity | \(\Delta_S\Phi_I=(c_I^2\beta_I/\alpha_I)\rho_I^G\) | conditional candidate derivation |
| source residuals | \(O(s^4,q_{\Phi,I}\varphi^2,\epsilon_{\mathrm{aniso}},\mu_{\varphi,I}^2\varphi^2)\) | bounded by Newtonian/isotropy gates |
| equivalence principle | clock universality + extremal \(\tau_I\) | partial |
| light bending | \(\Delta\theta=2(1+\gamma_I)G_IM/(c_I^2b)\) | requires \(\gamma_I\to1\) |
| Shapiro delay | PPN \(\gamma_I\) | target |
| perihelion | PPN \(\beta_I,\gamma_I\) | target |

Acceptance status:

`clock_rate_route_with_protocol_clock_layer`

---
