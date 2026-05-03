## 85. Contraction Holonomy Classifier

This section registers the next finite verifier gates.

Status:

`contraction_holonomy_classifier_initialized`

### 85.1. Contraction gate

The verifier can now check:

$$
\|\mathsf C_\eta\|\le1.
$$

It does this through the equivalent finite positivity condition:

$$
I-\mathsf C_\eta^\dagger\mathsf C_\eta\succeq0.
$$

Failure means the proposed cross-update contraction cannot be used in:

$$
X_\eta=G_1^{1/2}\mathsf C_\eta G_0^{1/2}.
$$

Status:

`finite_contraction_gate_executable`

### 85.2. Exact / non-exact holonomy classifier

The verifier can now classify a declared cycle as:

`exact`

or:

`non_exact`.

For a cycle:

$$
\gamma,
$$

it computes:

$$
\theta_\gamma
=
\sum_{(i\to j)\in\gamma}\mathcal A_{ij}
\mod2\pi.
$$

Then:

$$
\theta_\gamma=0
\Rightarrow
\text{exact},
$$

and:

$$
\theta_\gamma\ne0
\Rightarrow
\text{non-exact}.
$$

Status:

`finite_holonomy_class_gate_executable`

### 85.3. Why this matters

The fixed-point route requires:

$$
U_\gamma\ne1
$$

for at least one admissible cycle.

The verifier can now reject a manifest that declares a cycle non-exact while its phase sum is actually exact.

This directly protects the route from false nontrivial rotation.

Status:

`false_nontrivial_rotation_guard_initialized`

### 85.4. Current manifest gates

The current manifest:

`theory_verifier_manifest_v6_0.json`

contains executable examples for:

1. a valid contraction;
2. a non-exact cycle holonomy;
3. negative tests for non-contraction and incorrectly declared non-exact cycles.

Status:

`contraction_and_holonomy_class_manifest_registered`

### 85.5. What is closed

Closed:

1. finite contraction norm gate;
2. finite exact/non-exact holonomy classification;
3. negative tests for both new gates.

Open:

1. finite Schur-product inheritance gate in the new verifier;
2. extraction of cycle data from actual grammar files;
3. finite model for \(\bar C_\gamma\);
4. linking manifest gates to specific section/formula IDs.

Next target:

add Schur-product inheritance and actualization gates:

$$
\Gamma\succeq0,\quad K_\eta\succeq0
\Rightarrow
\Gamma\circ K_\eta\succeq0,
$$

and:

$$
I_3=0.
$$

Schur actualization verifier:

`sections/86-schur-actualization-verifier.md`

Status:

`contraction_holonomy_classifier_closed`
