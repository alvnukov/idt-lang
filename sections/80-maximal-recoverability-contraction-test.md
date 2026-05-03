## 80. Maximal Recoverability Contraction Test

This section tests whether maximal recoverable inheritance can select:

$$
\mathsf C_\eta.
$$

Result:

maximal recoverability constrains loss, but does not by itself select phase.

Status:

`maximal_recoverability_contraction_test_initialized`

### 80.1. Recoverability score

Let:

$$
\mathsf C_\eta
$$

be the contraction from the cross-kernel factorization:

$$
X_\eta
=
G_1^{1/2}\mathsf C_\eta G_0^{1/2}.
$$

For an active source subspace \(P_{\mathrm{act}}\), define preserved recoverable weight:

$$
\mathcal Q_\eta(\mathsf C)
=
\operatorname{Tr}
\left(
\rho_{\mathrm{act}}
\mathsf C^\dagger\mathsf C
\right),
$$

where \(\rho_{\mathrm{act}}\) is a normalized active readout state on the source support.

Because:

$$
\|\mathsf C\|\le1,
$$

we have:

$$
0\le\mathcal Q_\eta(\mathsf C)\le1.
$$

Status:

`recoverability_score_defined`

### 80.2. Maximization result

The maximum:

$$
\mathcal Q_\eta=1
$$

is reached whenever:

$$
\mathsf C^\dagger\mathsf C
=
I
$$

on the active support.

Thus every active-support isometry is maximally recoverable.

Therefore:

$$
\max\mathcal Q_\eta
\nRightarrow
\mathsf C_\eta
$$

as a unique contraction.

Status:

`maximal_recoverability_does_not_select_phase`

### 80.3. Support-restricted case

Let \(R_\eta\) restrict which source-target cells can connect.

If \(R_\eta\) permits many support-respecting isometries, maximal recoverability still does not select one.

If \(R_\eta\) permits a unique support-respecting partial isometry:

$$
\mathsf P_\eta,
$$

then maximal recoverability can select the support map:

$$
\mathsf C_\eta
=
\mathsf P_\eta D_\eta,
$$

where:

$$
D_\eta
$$

is diagonal phase freedom on the transported active modes.

The phases remain open unless additional holonomy/curvature data are derived.

Status:

`support_can_select_matching_not_phase`

### 80.4. Phase flatness and exact cocycles

The simplest no-extra-phase choice is:

$$
D_\eta=I.
$$

More generally, a pure endpoint relabeling:

$$
D_{ij}
=
e^{i(\alpha_j-\alpha_i)}
$$

is an exact cocycle.

It gives:

$$
U_\gamma=1
$$

for every closed cycle.

Therefore a nontrivial fixed-point rotation cannot come from maximal recoverability plus exact phase choice.

It requires:

$$
\operatorname{Arg}U_\gamma\ne0
\mod2\pi
$$

from non-exact topology, curvature, or a derived action-cost obstruction.

Status:

`nontrivial_phase_requires_more_than_recoverability`

### 80.5. Known experimental gates

This negative result is consistent with known phase physics.

Interference and Aharonov-Bohm experiments do not show that phase is fixed by probability preservation alone.

They show that closed holonomy is physical:

$$
\Delta\phi_{AB}
=
\frac{q}{\hbar}\oint A_\mu dx^\mu.
$$

Thus a phase theory must derive the holonomy source, not merely preserve norm.

Status:

`known_phase_gates_require_holonomy_not_only_recoverability`

### 80.6. No-fit rule

Forbidden:

1. choose the maximally recoverable isometry whose phase gives the desired \(G_I\);
2. treat norm preservation as phase derivation;
3. insert non-exact holonomy only after the fixed-point route fails;
4. use observed AB or interference phases to set primitive gravity-cycle phases.

Allowed:

1. use maximal recoverability to reject lossy contractions when the update is declared reversible;
2. use support uniqueness to derive a permutation/partial isometry;
3. keep phase open when only recoverability is known;
4. require topology, curvature, or action-cost data for non-exact cycle phase.

Status:

`maximal_recoverability_no_fit_rule`

### 80.7. What is closed

Closed:

1. maximal recoverability alone does not select \(\mathsf C_\eta\);
2. support restrictions may select matching but not phase;
3. exact phase choices cannot produce nontrivial cycle holonomy;
4. nontrivial rotation needs a derived holonomy source.

Open:

1. primitive topology/curvature source for non-exact phase;
2. independent action-cost obstruction;
3. unique support relation \(R_\eta\);
4. numerical \(\hbar_I,\omega_{\ell,I},G_I\).

Next target:

derive a non-exact holonomy source:

$$
\text{topology / curvature / action-cost obstruction}
\Rightarrow
U_\gamma\ne1.
$$

Non-exact holonomy source gate:

`sections/81-non-exact-holonomy-source-gate.md`

Status:

`maximal_recoverability_test_closed_negative`
