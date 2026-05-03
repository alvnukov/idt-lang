## 173. IDT MetaLang Research Graph

Status:

`idt_metalang_research_graph_initialized`

This section answers the current research-language review.

The next useful strengthening is not a stronger physics claim. The next useful
strengthening is a smaller machine-readable research graph that makes physical
claims hard to counterfeit structurally.

The current repository already has several pieces:

1. symbol and derivation statuses;
2. `depends_on` edges for derivations;
3. cycle checks and forbidden input paths;
4. sector role taxonomy gates;
5. QM experiment and proof-obligation ledgers;
6. prediction-like SPARC gates;
7. useful exclusion and rejection gates.

Those pieces are real, but they are distributed. The missing layer is a compact
IDT-Core/MetaLang contract that says what a research claim must contain before
it is allowed to become a physics claim.

### 173.1. Contract Surface

The first executable contract is:

`idt_metalang_research_graph_contract_demo`

It tracks seven surfaces:

| Surface | Current status | Reason |
|---|---|---|
| `claim_role_type_system` | `implemented` | sector role registry, role partition, anchor/coupling/bridge gates |
| `dependency_dag` | `implemented` | derivation `depends_on`, cycle checks, forbidden input paths |
| `proof_status_axis` | `partial` | proof statuses exist, but are not yet separated from role/status vocabulary |
| `prediction_protocol` | `partial` | sector gates carry prediction fields, but no first-class prediction object exists |
| `failure_ledger` | `partial` | useful exclusions exist as gates/prose, but not as a top-level ledger |
| `minimal_core_kernel` | `partial` | the core is spread across sections 170-172 |
| `theorem_cards` | `partial` | full-QM closure theorem cards exist, but bridge and gate cards are not uniform |

The contract status is therefore:

`partial`

It must not be marked:

`complete`

until the partial surfaces become first-class manifest objects or verifier
semantics.

The evidence references inside the contract are also grounded. A reference must
point to one of:

1. an existing manifest object;
2. an accepted manifest schema surface;
3. an accepted verifier check label;
4. an existing Markdown section.

Status:

`idt_metalang_evidence_refs_grounded`

The first first-class theorem-card pass covers the full-QM closure frontier:

1. `universal_carrier_selection_theorem`;
2. `hilbert_carrier_derivation`;
3. `universal_born_rule_theorem`;
4. `wigner_reversible_inheritance_theorem`;
5. `apparatus_facticity_theorem`;
6. `monoidal_tensor_composition_theorem`;
7. `first_principles_hbar_lock`;
8. `field_mode_continuum_limit`.

These cards do not close QM. They make each remaining blocker explicit,
typed, grounded, and separately inspectable.

Status:

`full_qm_frontier_theorem_cards_grounded`

### 173.2. Required IDT-Core Kernel

The compact kernel should be:

1. primitive grammar;
2. claim role type system;
3. dependency graph;
4. proof-status semantics;
5. gate protocol;
6. prediction protocol;
7. failure ledger;
8. theorem-card protocol.

This is a language target, not a physics target.

It does not claim `full_QM_I = derived`, `G_I = derived`, `hbar_I = derived`,
or `alpha_em_I = derived`.

It gives future physics work a stricter compiler.

### 173.3. Prediction Object Target

A future first-class prediction object should minimally contain:

```yaml
prediction:
  id:
  observable:
  input_data:
  frozen_parameters:
  allowed_tolerance:
  fail_condition:
  holdout_dataset:
  claim_boundary:
```

This turns the current claim-control strength into a predeclared prediction
workflow.

The key rule is:

`prediction` is not a successful prediction until the frozen parameters,
tolerance, fail condition, and holdout dataset were declared before evaluation.

### 173.4. Failure Ledger Target

A future first-class failure record should minimally contain:

```yaml
failure:
  id:
  failed_object:
  failure_mode:
  frozen_inputs:
  observed_mismatch:
  rejected_repair:
  retained_value:
```

The retained value is important. A failed bridge can still narrow the theory if
the failure was predeclared and not repaired after seeing the result.

### 173.5. Theorem Card Target

A future first-class theorem card should minimally contain:

```yaml
theorem_card:
  id:
  statement:
  role:
  assumptions:
  dependencies:
  proof_status:
  verifier:
  known_failures:
  physical_scope:
  forbidden_claims:
```

This makes the next stage explicit:

`IDT-MetaLang before IDT-Physics escalation`.

### 173.6. Current Decision

We should strengthen the research language now.

We should not pause QM/physics work for a full rewrite. The right next step is
incremental:

1. keep the existing manifest and verifier;
2. add compact first-class objects only where they remove ambiguity;
3. use the research graph contract to reject premature `complete` status;
4. promote prediction, failure, and theorem-card objects in small executable
   passes.

Status:

`idt_metalang_strengthening_needed_without_physics_overclaim`
