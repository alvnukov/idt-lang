## 74. Transition Action Gate

This section defines what would count as a derivation of transition actions:

$$
\mathfrak s_{ij}.
$$

It also records a negative result: positivity alone cannot derive them.

Status:

`transition_action_gate_initialized`

### 74.1. Complex transfer element

For an allowed transition:

$$
(a_i,a_j)\in\mathcal P_{EF},
$$

write the transfer element as:

$$
\mathcal T_{ij}
=
|\mathcal T_{ij}|
\exp
\left(
\frac{i\mathfrak s_{ij}}{\hbar_I}
\right).
$$

Then:

$$
\mathfrak s_{ij}
=
\hbar_I\arg\mathcal T_{ij}
\mod2\pi\hbar_I.
$$

Status:

`transition_action_from_transfer_phase`

### 74.2. Positivity-only negative result

Schur positivity of the induced kernel requires:

$$
K_{\eta,EF}\succeq0.
$$

For the two-event normalized kernel:

$$
K(q)\succeq0
\Longleftrightarrow
|q|\le1.
$$

This constrains magnitudes.

It does not determine:

$$
\arg q
$$

or:

$$
\arg\mathcal T_{ij}.
$$

Therefore:

$$
\text{positivity alone}
\nRightarrow
\mathfrak s_{ij}.
$$

Status:

`positivity_does_not_fix_transition_action`

### 74.3. Reciprocity constraint

Link reversal requires:

$$
\mathfrak s_{\bar j\bar i}
=
-
\mathfrak s_{ij}
\mod2\pi\hbar_I.
$$

This is a constraint, not a value.

It removes inconsistent actions but does not select the cocycle.

Status:

`transition_action_reciprocity_constraint`

### 74.4. Additivity constraint

For a word:

$$
w=i_0i_1\cdots i_L,
$$

the action is:

$$
S_I(w)
=
\sum_{r=0}^{L-1}
\mathfrak s_{i_ri_{r+1}}.
$$

Blocking consistency requires:

$$
S_I(w\circ v)
=
S_I(w)+S_I(v)
\mod2\pi\hbar_I.
$$

Again, this is a consistency condition, not a numerical selection rule.

Status:

`transition_action_additivity_constraint`

### 74.5. What can derive \(\mathfrak s_{ij}\)

Allowed derivation sources:

1. primitive update phase readout \(U_I(\eta_j\leftarrow\eta_i)\);
2. update action cost functional \(\mathfrak s_I(\eta_j\leftarrow\eta_i)\);
3. non-exact cycle action fixed by primitive topology;
4. independent phase gates already tied to \(\hbar_I\).

Forbidden derivation sources:

1. \(G_N\);
2. \(\omega_{\ell,G}\);
3. photon or matter-wave residuals used after the fact;
4. a chosen fixed point \(\Theta_*\).

Status:

`allowed_transition_action_sources`

### 74.6. Closure criterion

Transition actions are closed only if:

$$
\mathcal I,\Gamma_I,K_\eta
\Rightarrow
U_I(\eta_j\leftarrow\eta_i)
\Rightarrow
\mathfrak s_{ij}
$$

for all allowed grammar edges.

If only constraints are known:

$$
\mathfrak s_{\bar j\bar i}=-\mathfrak s_{ij},
\qquad
S(w\circ v)=S(w)+S(v),
$$

then status remains:

`action_constrained_not_derived`.

Status:

`transition_action_closure_criterion`

### 74.7. No-fit rule

Forbidden:

1. choose \(\arg\mathcal T_{ij}\) to fit gravity;
2. infer \(\mathfrak s_{ij}\) from Planck units;
3. treat positivity constraints as phase derivations;
4. change cocycle after fixed-point comparison.

Allowed:

1. carry `action_constrained_not_derived`;
2. derive actions from primitive phase readout;
3. reject the fixed-point route if transition actions remain free.

Status:

`transition_action_no_fit_rule`

### 74.8. What is closed

Closed:

$$
\mathfrak s_{ij}
=
\hbar_I\arg\mathcal T_{ij}
\mod2\pi\hbar_I.
$$

Closed:

positivity, reciprocity, and additivity constrain transition actions but do not determine them.

Open:

1. primitive phase readout for update transitions;
2. non-exact action cocycle;
3. numerical \(F_G\);
4. numerical \(\omega_{\ell,I}\).

Next target:

classify the fixed-point map route with the current component status and decide whether to pause it until primitive phase readout is specified.

Fixed-point route decision:

`sections/75-fixed-point-route-decision.md`

Primitive transition phase readout:

`sections/76-primitive-transition-phase-readout.md`

Status:

`transition_action_constrained_not_derived`
