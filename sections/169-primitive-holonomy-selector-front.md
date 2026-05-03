## 169. Primitive Holonomy Selector Front

Status:

`primitive_holonomy_selector_front_initialized`

This section formalizes the next possible unlock primitive discussed after
Section 168.

It does not add a numerical calibration.

It introduces a structural selector target:

`primitive_holonomy_source_selector_I`.

The selector must choose a source class before comparison with \(G_N\),
\(\hbar_{\mathrm{obs}}\), Planck units, spectroscopy, or any gravity residual.

### 169.1. What the selector is

A primitive selector is a rule:

$$
\mathcal S_{\mathrm{hol}}
:
\Gamma_I
\Rightarrow
\{\text{source class},\text{admissible cycle family},\text{branch policy}\}.
$$

It is not:

$$
\mathcal S_{\mathrm{hol}}
:
G_N
\Rightarrow
w_\gamma.
$$

The second form is a hidden calibration.

Status:

`selector_is_structural_not_numeric`

### 169.2. Allowed source classes

The current selector registry contains four admissible source classes:

1. discrete curvature;
2. topological winding;
3. action-cost obstruction;
4. source-coupled phase response.

The registry is not a claim that any class has been derived.

It only prevents an implicit fifth class from being inserted later after a
failed comparison.

Status:

`holonomy_source_class_registry_fixed`

### 169.3. Topological winding subselector

The nearest concrete subselector is:

`primitive_topology_winding_selector_I`.

It must derive:

1. cycle words;
2. homotopy classes;
3. orientation reversal;
4. winding additivity.

For any accepted winding map:

$$
w_{\gamma^{-1}}=-w_\gamma,
\qquad
w_{\gamma_1\gamma_2}=w_{\gamma_1}+w_{\gamma_2}.
$$

Cycles in the same homotopy class must receive the same winding.

Status:

`primitive_winding_selector_coherence_required`

### 169.4. Machine targets

The target:

`primitive_holonomy_source_selector_I`

now requires:

1. `primitive_source_class_registry_I`;
2. `pre_observation_selection_rule_I`;
3. `selector_holdout_policy_I`.

The target:

`primitive_topology_winding_selector_I`

now requires:

1. `cycle_word_grammar_I`;
2. `cycle_homotopy_class_I`;
3. `orientation_reversal_rule_I`;
4. `winding_additivity_rule_I`.

The non-exact holonomy target now depends on the general selector target.

Status:

`primitive_selector_targets_guarded`

### 169.5. Research verdict

This cluster does not unlock the \(G\)-route.

It sharpens the condition for a future unlock:

$$
\text{non-exact holonomy source}
\Leftarrow
\text{pre-observation structural selector}
$$

not:

$$
\text{non-exact holonomy source}
\Leftarrow
\text{post-fit branch choice}.
$$

If no primitive selector can be derived, the theory must either add a new
structural primitive or keep the holonomy route underdetermined.

Status:

`primitive_holonomy_selector_front_complete`
