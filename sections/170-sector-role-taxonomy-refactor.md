## 170. Sector Role Taxonomy Refactor

Status:

`sector_role_taxonomy_refactor_initialized`

This section records the paradigm refactor.

The active object is no longer a linear derivation ladder from primitives to
all physical constants.

The active object is a typed reconstruction framework. Every physical bridge
must first declare which role it plays.

### 170.1. Role taxonomy

The canonical roles are:

1. `structural_selector`;
2. `dimensional_anchor`;
3. `dimensionless_coupling`;
4. `bridge_assumption`;
5. `derived_readout`;
6. `experimental_gate`;
7. `blocked_claim`.

A symbol may not occupy multiple roles in the same claim context.

In particular:

1. a calibrated anchor is not a derived readout;
2. a structural selector is not a numerical coupling;
3. an experimental gate is not a primitive source;
4. a blocked claim cannot be relabeled as a target output by changing notation.

Status:

`sector_roles_partitioned`

### 170.2. Anchors versus selectors

A dimensional anchor fixes a unit-bearing scale.

Examples:

1. `calibrated_hbar_I`;
2. `calibrated_G_anchor_I`;
3. future primitive mass / impulse / work anchors.

A structural selector fixes an admissible sector or branch before comparison
with observations.

Examples:

1. `primitive_holonomy_source_selector_I`;
2. `primitive_topology_winding_selector_I`;
3. future gauge-sector selectors.

The two roles are not interchangeable.

Adding a structural selector cannot set a dimensionful constant.

Adding a dimensionful anchor cannot select a gauge group, winding class, or
source class.

Status:

`anchors_and_selectors_separated`

### 170.3. Coupling policy

Dimensionless couplings occupy a third role.

Examples:

1. \(\alpha_{\mathrm{em},I}\);
2. weak-sector mixing parameters;
3. strong-sector scale ratios or running-coupling targets.

A dimensionless coupling can be:

1. derived from an independently fixed structural selector;
2. calibrated once and then tested by running / holdout gates;
3. left as target.

It cannot be silently derived from gauge covariance alone.

Status:

`dimensionless_couplings_require_selector_or_calibration`

### 170.4. Machine target

The target:

`sector_role_taxonomy_I`

requires:

1. `structural_selector_registry_I`;
2. `dimensional_anchor_registry_I`;
3. `dimensionless_coupling_registry_I`;
4. `bridge_assumption_registry_I`;
5. `derived_readout_registry_I`;
6. `cross_sector_holdout_policy_I`.

The verifier now checks:

1. role registry completeness;
2. no overlapping role assignments;
3. no dimensionful first-principles claim without an independent anchor;
4. no derived dimensionless-coupling claim without a derived selector;
5. no bridge assumption relabeled as derived.

Status:

`sector_role_taxonomy_machine_guarded`

### 170.5. Development consequence

Future EM, weak, strong, and gravity work must begin by classifying each object:

1. sector selector;
2. dimensional anchor;
3. dimensionless coupling;
4. bridge assumption;
5. derived readout;
6. experimental gate;
7. blocked claim.

Only after that classification may the route ask whether the object is derived,
calibrated, or held out.

This prevents the old failure mode:

$$
\text{missing selector}
\Rightarrow
\text{hidden numerical calibration}
\Rightarrow
\text{overclaimed derivation}.
$$

Status:

`taxonomy_first_development_rule`
