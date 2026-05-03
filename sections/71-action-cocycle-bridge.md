## 71. Action Cocycle Bridge

This section connects grammar phase cocycles to inherited action.

It does not derive numerical action increments.

Status:

`action_cocycle_bridge_initialized`

### 71.1. Transition action increment

For each allowed grammar transition:

$$
(a_i,a_j)\in\mathcal P_{EF},
$$

define an inherited action increment:

$$
\mathfrak s_{ij}
\in
\mathbb R/2\pi\hbar_I\mathbb Z.
$$

The grammar edge phase is:

$$
\vartheta_{ij}
=
\frac{\mathfrak s_{ij}}{\hbar_I}
\mod2\pi.
$$

Status:

`edge_phase_from_action_increment`

### 71.2. Word action

For a word:

$$
w=a_{i_0}a_{i_1}\cdots a_{i_L},
$$

define:

$$
S_I(w)
=
\sum_{r=0}^{L-1}
\mathfrak s_{i_ri_{r+1}}.
$$

Then:

$$
\Theta(w)
=
\frac{S_I(w)}{\hbar_I}
\mod2\pi.
$$

This is exactly the update-chain action-phase bridge restricted to the local grammar.

Status:

`word_phase_from_inherited_action`

### 71.3. Gauge-invariant cycle action

For a closed grammar cycle \(\gamma\):

$$
S_I(\gamma)
=
\sum_{(i,j)\in\gamma}
\mathfrak s_{ij}.
$$

The physical cycle phase is:

$$
\Phi_\gamma
=
\frac{S_I(\gamma)}{\hbar_I}
\mod2\pi.
$$

Only:

$$
\Phi_\gamma
$$

can enter the fixed-point map.

Status:

`cycle_action_phase_invariant`

### 71.4. Exact cocycle case

If:

$$
\mathfrak s_{ij}
=
\sigma_j-\sigma_i,
$$

then:

$$
S_I(\gamma)=0
$$

for every closed cycle.

Therefore:

$$
\Phi_\gamma=0.
$$

This gives no nontrivial rotation source.

A nonzero fixed-point rotation requires a non-exact action cocycle.

Status:

`nontrivial_rotation_requires_nonexact_action_cocycle`

### 71.5. No-fit rule

Forbidden:

1. choose \(S_I(\gamma)\) from \(\omega_{\ell,G}\);
2. choose \(\mathfrak s_{ij}\) after photon or matter-wave comparison;
3. treat gauge-dependent \(\mathfrak s_{ij}\) as physical;
4. add a non-exact cocycle only to rescue gravity.

Allowed:

1. derive \(\mathfrak s_{ij}\) from primitive update costs;
2. use only cycle actions \(S_I(\gamma)\);
3. accept zero rotation if the action cocycle is exact;
4. classify the fixed-point route as underderived if cycle actions are not fixed.

Status:

`action_cocycle_no_fit_rule`

### 71.6. What is closed

Closed:

$$
\vartheta_{ij}
=
\mathfrak s_{ij}/\hbar_I
\mod2\pi.
$$

Closed:

$$
\Phi_\gamma
=
S_I(\gamma)/\hbar_I
\mod2\pi.
$$

Open:

1. primitive transition actions \(\mathfrak s_{ij}\);
2. non-exact cycle actions \(S_I(\gamma)\);
3. coherence magnitudes \(r_j\);
4. fixed point \(\Theta_*\);
5. \(\omega_{\ell,I}\).

Next target:

derive transition actions \(\mathfrak s_{ij}\) from primitive update costs, or classify the rotation map as action-underdetermined.

Transition action gate:

`sections/74-transition-action-gate.md`

Primitive transition phase readout:

`sections/76-primitive-transition-phase-readout.md`

Status:

`action_cocycle_bridge_defined`
