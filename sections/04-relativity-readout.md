## 4. Relativity Without Primitive Geometry

The following must not be taken as primitives:

$$
g_{\mu\nu},\quad M,\quad \text{light cone},\quad \text{coordinates}
$$

Geometry front chain:

$$
I_\eta
\Rightarrow
\preceq_I
\Rightarrow
(\bar E,\le_I)
\Rightarrow
(\tau_I,d_S)
\Rightarrow
D_G
\Rightarrow
g_{\mu\nu}^{\mathrm{readout}}
$$

### 4.1. Factual event set

Factual events:

$$
E_\epsilon
$$

are obtained from high-facticity readout tokens.

Coarse events:

$$
\bar E=E_\epsilon/\sim_{\mathrm{fact}}
$$

### 4.2. Causal order

Inherited influence:

$$
A\prec_I B
$$

if an admissible act in \(A\) changes the readout data of \(B\).

Reachability:

$$
A\preceq_I B
$$

if there is a chain of inherited influences.

Causal quotient:

$$
A\sim_c B
\Longleftrightarrow
A\preceq_I B
\ \mathrm{and}\
B\preceq_I A
$$

On the quotient:

$$
(\bar E,\le_I)
$$

there must be a partial order.

### 4.3. No signal before light cone

If:

$$
R\not\le_I S
$$

then admissible interventions in \(R\) preserve the \(S\)-marginal:

$$
\mathcal A_S^u(B,B')
=
\mathcal A_S^{u'}(B,B')
$$

This is a proto-form of no superluminal signalling.

### 4.4. Clocks

A clock is a stable fact-producing cycle:

$$
C_0\prec_I C_1\prec_I\cdots\prec_I C_N
$$

Tick event:

$$
\Theta_C(k)=C_k
$$

Tick count in a chain segment:

$$
N_C(A,B)
=
\#\{k:\ A\preceq_I C_k\preceq_I B\}
$$

Clock phase:

$$
\theta_C(k+1)-\theta_C(k)=2\pi
$$

Stable clock condition:

$$
\left|
\frac{N_C(A,B)}{N_C(B,D)}
-
\frac{\tau_I(A,B)}{\tau_I(B,D)}
\right|
\le
\epsilon_{\mathrm{stab}}
$$

for repeated local calibration chains.

Proper time along chain:

$$
\tau_I(\gamma)
=
\sum_k\delta\tau_I(A_k,A_{k+1})
$$

Clock readout of proper time:

$$
\tau_C(A,B)
=
\frac{N_C(A,B)}
{f_{C,\infty}}
$$

after flat-domain calibration.

Admissible clock equivalence:

$$
\frac{\tau_C(A,B)}
{\tau_{C'}(A,B)}
=
1+O(\epsilon_{\mathrm{clock}})
$$

for co-located calibrated clocks.

Free clock:

$$
\tau_I(A,B)
=
\sup_{\gamma:A\to B}\tau_I(\gamma)
$$

Known time-dilation gate:

$$
\frac{d\tau}{dt}
=
\sqrt{1-\frac{v^2}{c^2}}
$$

for inertial flat readout.

Weak gravitational + kinematic gate:

$$
\frac{d\tau}{dt}
\approx
1+\frac{\Phi}{c^2}
-\frac{v^2}{2c^2}
$$

Any clock readout must reduce to these formulas in the tested domain.

### 4.5. Slices

A slice \(S\subset\bar E\) is an antichain:

$$
A,B\in S,\ A\neq B
\Rightarrow
A\not\le_I B,\ B\not\le_I A
$$

Simultaneity is slice-dependent.

### 4.6. Spatial distance

On a slice \(S\):

$$
G_S=(S,\sim_S)
$$

Spatial distance:

$$
d_S(A,B)
=
\ell_0
\inf_{\pi:A\to B}
\sum_{(X,Y)\in\pi}w_S(X,Y)
$$

The scale \(\ell_0\) is not primitive.

It is fixed by clock/order distance calibration.

Distance-scale closure:

`sections/40-clock-order-distance-scale.md`

### 4.7. Geometry interval

Use \(D_G\), not old \(D_I\).

Timelike:

$$
D_G(A,B)=c_I^2\tau_I(A,B)^2
$$

Spacelike:

$$
D_G(A,B)=-d_S(A,B)^2
$$

Null:

$$
D_G(A,B)=0
$$

Lorentzian target:

$$
D_G(A,B)
\to
c^2\Delta t^2-\Delta x^2
$$

---
