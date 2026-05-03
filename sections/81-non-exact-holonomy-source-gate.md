## 81. Non-Exact Holonomy Source Gate

This section defines what can source a physical non-exact phase:

$$
U_\gamma\ne1
$$

on a closed cycle.

Status:

`non_exact_holonomy_source_gate_initialized`

### 81.1. Edge connection form

Write transition phase as a discrete connection:

$$
U_{ij}
=
e^{i\mathcal A_{ij}}.
$$

For a closed cycle:

$$
\gamma=i_0i_1\cdots i_Li_0,
$$

the holonomy is:

$$
U_\gamma
=
\prod_{r=0}^{L}
U_{i_ri_{r+1}}
=
\exp
\left(
i\sum_{r=0}^{L}\mathcal A_{i_ri_{r+1}}
\right),
$$

with \(i_{L+1}=i_0\).

Status:

`discrete_phase_connection_defined`

### 81.2. Exact phases are gauge

If:

$$
\mathcal A_{ij}
=
\alpha_j-\alpha_i,
$$

then:

$$
U_\gamma=1
$$

for every closed cycle.

This is a pure endpoint relabeling.

It cannot source a physical fixed-point rotation.

Status:

`exact_phase_is_gauge_only`

### 81.3. Allowed non-exact sources

A non-exact holonomy can be accepted only from one of these sources:

1. discrete curvature on the grammar graph;
2. nontrivial topology with flat but globally non-exact connection;
3. derived action-cost obstruction;
4. source-coupled phase response already fixed before comparison.

In continuum notation:

$$
\oint_\gamma \mathcal A
=
\int_\Sigma \mathcal F
$$

when the loop bounds a surface \(\Sigma\).

If \(\mathcal F=0\) but topology is nontrivial, a flat holonomy may still be physical.

Status:

`allowed_non_exact_holonomy_sources_defined`

### 81.4. Action-cost holonomy

If the phase is sourced by action cost:

$$
U_\gamma
=
e^{iC_\gamma/\hbar_I},
$$

then:

$$
\operatorname{Arg}U_\gamma
=
\frac{C_\gamma}{\hbar_I}
\mod2\pi.
$$

This is not a derivation of \(\hbar_I\) unless \(C_\gamma\) is independently derived without \(\hbar_I\).

If two independent cycles give:

$$
\frac{C_\gamma}{\operatorname{Arg}U_\gamma}
=
\frac{C_{\gamma'}}{\operatorname{Arg}U_{\gamma'}}
$$

on fixed branches, then they support a universal phase-action scale.

Status:

`action_cost_holonomy_requires_independent_cost`

### 81.5. Known phase gates

Electromagnetic Aharonov-Bohm gate:

$$
\Delta\phi_{AB}
=
\frac{q}{\hbar}
\oint A_\mu dx^\mu.
$$

Action phase gate:

$$
\Delta\phi
=
\frac{\Delta S}{\hbar}.
$$

Weak gravitational matter-wave gate:

$$
\Delta\phi_{\mathrm{grav}}
\approx
\frac{m g A}{\hbar v}
$$

for the standard nonrelativistic interferometer geometry.

Equivalently:

$$
\Delta\phi_{\mathrm{grav}}
=
\frac{1}{\hbar}
\int
m\Delta\Phi\,dt
$$

in the weak-potential limit.

These are gates for the holonomy sector.

They are not sources for choosing primitive holonomy after the fact.

Status:

`known_holonomy_gates_registered_without_fit`

### 81.6. Gravity route implication

The fixed-point gravity route needs a non-exact cycle phase:

$$
\operatorname{Arg}U_\gamma\ne0.
$$

If the primitive inheritance graph has no curvature, no topology, and no action-cost obstruction, then:

$$
U_\gamma=1
$$

and the fixed-point route produces no nontrivial rotation from this sector.

Therefore the route must either:

1. derive a non-exact holonomy source;
2. accept the exact-cocycle outcome and pause the route;
3. find a different mechanism for \(\Theta_*\).

Status:

`gravity_fixed_point_requires_derived_non_exact_holonomy`

### 81.7. No-fit rule

Forbidden:

1. insert a curvature term only to match \(G_N\);
2. select topology after observing the desired fixed point;
3. use measured AB, COW, or atom-interferometer phase as primitive input;
4. hide \(\hbar_I\) inside \(C_\gamma\).

Allowed:

1. derive graph curvature from update consistency;
2. derive topology from the inheritance grammar;
3. derive action cost independently and test universal \(\hbar_I\);
4. reject the route if no non-exact source exists.

Status:

`non_exact_holonomy_no_fit_rule`

### 81.8. What is closed

Closed:

1. exact phases are gauge and physically non-rotating;
2. non-exact holonomy needs curvature, topology, or independent action cost;
3. known phase experiments are gates, not fitting inputs;
4. gravity fixed-point rotation requires a derived non-exact source.

Open:

1. primitive graph curvature;
2. primitive graph topology;
3. independent cycle action cost \(C_\gamma\);
4. universal \(\hbar_I\) from multiple cycles;
5. numerical \(\omega_{\ell,I}\) and \(G_I\).

Next target:

attempt the action-cost route:

$$
\text{update work / clock cost}
\Rightarrow
C_\gamma
\Rightarrow
\hbar_I
\quad\text{or}\quad
\operatorname{Arg}U_\gamma.
$$

Action-cost hbar route:

`sections/82-action-cost-hbar-route.md`

Status:

`non_exact_holonomy_source_gate_closed`
