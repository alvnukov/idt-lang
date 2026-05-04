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

The full-QM frontier also reads these cards as the status authority:
`formal_proof` is required before a theorem card can support a frontier
component. Finite verifier passes, numerical evidence, or calibrated matches
remain useful evidence, but they do not by themselves close a full-QM theorem
blocker.

Status:

`full_qm_frontier_theorem_cards_grounded`

The first theorem proof route is now manifest-backed:

`carrier_selection_proof_route_demo`

This adds the missing layer between a theorem card and finite evidence. A proof
route is not a theorem proof. It is a typed list of lemma obligations with
finite witnesses, open gaps, and a computed proof status.

Status:

`theorem_proof_route_language_initialized`

The first lemma route is now manifest-backed:

`context_product_carrier_lemma_route_demo`

This is the first narrower proof-unit below a theorem proof route. It records
the finite witnesses, excluded counterexamples, expected exclusion count, and
remaining generalization gaps for one carrier-selection lemma.

The first conditional separator theorem is now manifest-backed:

`context_product_exhaustion_implies_local_tomography`

Its executable verifier is:

`context_product_local_tomography_theorem_demo`

It promotes the context-product route from finite witness to
`conditional_proof`: under finite context-product exhaustion assumptions,
product readouts separate stable composite facts, so local tomography follows.
The paired rejected-candidate card
`real_hilbert_composite_hidden_joint_invariant` and fixture
`real_hilbert_composite_hidden_joint_invariant_demo` record the rebit
\(Y\otimes Y\) hidden-joint invariant separator.

The second lemma route is now manifest-backed:

`purification_filtering_carrier_lemma_route_demo`

The second conditional separator theorem is now manifest-backed:

`purification_filtering_implies_recoverable_support_update`

Its executable verifier is:

`purification_filtering_recoverable_support_theorem_demo`

It promotes the purification/filtering route from finite witness to
`conditional_proof`: under recoverable-extension and support-renormalization
assumptions, admissible filtering is a support-restricted recoverable update,
and insufficient-extension plus zero-support-filter cases are rejected.

The third lemma route is now manifest-backed:

`bounded_correlation_carrier_lemma_route_demo`

The third conditional separator theorem is now manifest-backed:

`bounded_correlation_screen_rejects_superquantum_boxes`

Its executable verifier is:

`bounded_correlation_screen_theorem_demo`

It promotes the bounded-correlation route from finite witness to
`conditional_proof`: under stable-correlation and declared GPT-principle
assumptions, classical and Tsirelson-edge samples survive, while PR-box-like
and boxworld-like cases are rejected.

The fourth lemma route is now manifest-backed:

`noncomplex_jordan_classification_lemma_route_demo`

The fourth conditional separator theorem is now manifest-backed:

`noncomplex_jordan_separator_rejects_noncomplex_samples`

Its executable verifier is:

`noncomplex_jordan_separator_theorem_demo`

It promotes the non-complex Jordan route from finite witness to
`conditional_proof`: under the finite candidate family and declared
composition/filtering/correlation route assumptions, real-Hilbert-like,
quaternionic-Hilbert-like, and exceptional-Jordan-like samples are rejected
while the generic GPT cone remains underdetermined.

The fifth lemma route is now manifest-backed:

`generic_gpt_classification_lemma_route_demo`

The fifth conditional separator theorem is now manifest-backed:

`generic_gpt_closure_rejects_unconstrained_cone`

Its executable verifier is:

`generic_gpt_closure_theorem_demo`

It promotes the generic-GPT route from finite witness to `conditional_proof`:
the unconstrained generic GPT cone is rejected, while the route-closed GPT
subtheory and the broader generic GPT cone remain explicit underdetermined
blockers. This is the current frontier for universal carrier selection.

The verifier now also checks carrier-selection theorem grounding directly:
`universal_carrier_selection_theorem` must match
`carrier_selection_proof_route_demo`, and every theorem-route lemma must cite
its executable lemma route.

Status:

`lemma_route_language_initialized`

### 173.2. Query And Edit Layer

The first file-based graph query tool is:

`scripts/graph_query.py`

It is intentionally not a database. The JSON manifest remains the source of
truth, but common graph operations no longer require manual `zq` probing:

```bash
python3 scripts/graph_query.py summary
python3 scripts/graph_query.py show universal_carrier_selection_theorem
python3 scripts/graph_query.py refs hbar_I
```

The tool also supports cautious single-field edits:

```bash
python3 scripts/graph_query.py set-field \
  --collection theorem_cards \
  --id universal_carrier_selection_theorem \
  --field proof_status \
  --value open \
  --expect-sha <sha-from-summary>
```

Edits are deliberately narrow:

1. only allowlisted string fields can be changed;
2. the caller must provide the current manifest SHA;
3. writes hold an exclusive lock;
4. writes use atomic replace;
5. the tool changes only the target line, not the whole JSON file.

Status:

`file_based_graph_query_layer_added`

### 173.3. Required IDT-Core Kernel

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

### 173.4. Prediction Object Target

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

### 173.5. Failure Ledger Target

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

### 173.6. Theorem Card Target

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

### 173.7. Current Decision

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

### 173.8. QM Proof Anti-Hallucination Audit

The next verifier layer is:

`qm_proof_anti_hallucination_audit_demo`

It treats a successful finite-QM verifier pass as evidence, not as a proof of
full QM. The audit checks the live graph boundaries:

1. `full_QM_I` remains `target`;
2. `hbar_I` remains `blocked`;
3. `universal_carrier_selection_theorem` remains `open`;
4. `limit_preserves_facticized_readout_separation` remains `open` inside
   `nonfinite_gpt_residual_compactness_frontier_demo`;
5. every conditional theorem card retains a `does_not_prove_full_QM_I`
   forbidden claim;
6. negative controls are declared for premature full-QM, carrier-selection,
   nonfinite-limit, and conditional-theorem upgrades.

The audit status is:

`passes_with_open_gaps`

This is intentionally not `formal_proof`. It is an anti-self-deception check:
if a future edit silently turns an open QM blocker into a derived result, the
manifest should fail before the prose can overclaim.

Status:

`qm_proof_anti_hallucination_audit_added`

### 173.9. Structural Compression Map

Viewed as one structure, the current theory has a smaller repeated shape:

```text
typed claim
  -> dependencies
  -> finite witness or bridge
  -> verifier gate
  -> theorem/frontier card
  -> forbidden upgrades
```

This suggests several candidate abstractions:

1. `research_graph_kernel`;
2. `finite_witness_gate_schema`;
3. `conditional_separator_schema`;
4. `frontier_obstruction_schema`;
5. `calibrated_anchor_boundary_schema`;
6. `failure_as_information_schema`.

The executable audit is:

`idt_structural_compression_audit_demo`

Its rule is:

`abstractions_may_not_change_claim_status_or_close_open_gap`

That rule is the important part. Mathematical compression is allowed only when
it preserves truth conditions. A shorter language that relabels a bridge as a
derivation, hides an open frontier, or reduces verifier coverage is not a
simplification; it is a false proof.

The immediate compression opportunity is to factor the repeated
conditional-separator pattern. Many current carrier-selection routes have the
same logical form:

```text
assumptions
  + finite witnesses
  + rejected counterexamples
  + retained forbidden upgrades
  -> conditional separator
```

The full-QM and nonfinite residual frontiers have the dual form:

```text
required theorem set
  + component statuses
  + obstruction ledger
  + forbidden upgrades
  -> frontier status
```

These are good candidates for future reusable verifier schemas. They are not
yet implemented as a generic kernel, so the current status is only:

`candidate_map`

Status:

`idt_structural_compression_candidate_map_added`

### 173.10. Foundation Import Boundary

The base layer must distinguish genuine IDT primitives from useful QM imports.
The carrier-neutral primitive core is restricted here to history space, event
algebra, readout-context family, and inheritance-act family. The current
finite-QM programme still imports several structures:

1. complex coherent amplitudes;
2. a positive distinguishability kernel;
3. a quadratic actualization measure;
4. Schur-style inheritance update;
5. tensor/product composition;
6. unitary context maps;
7. an action-phase bridge through `calibrated_hbar_I` while `hbar_I` remains
   blocked.

The executable audit is:

`foundation_import_boundary_audit_demo`

Its rule is:

`no_qm_import_may_be_counted_as_idt_primitive_or_derived_claim`

This does not invalidate the existing QM gates. It classifies their carrier and
readout assumptions honestly: finite gates remain evidence for compatibility,
not derivations of the Hilbert carrier, the universal Born rule, monoidal
tensor composition, Wigner/unitary dynamics, or first-principles `hbar_I`.

Each import records a target refactor:

```text
complex amplitude carrier -> carrier_neutral_K_I
PSD kernel -> positivity_obligation
quadratic measure -> born_rule_obligation
Schur update -> inheritance_update_obligation
tensor composition -> monoidal_composition_obligation
unitary map -> reversible_inheritance_obligation
hbar bridge -> first_principles_action_scale_obligation
```

The verifier also grounds the audit against live statuses: `full_QM_I` must
remain `target`; `hbar_I` must remain `blocked`; carrier, Hilbert, Born,
Wigner/unitary, tensor, and first-principles-hbar theorem cards must remain open
or blocked as declared.

Status:

`foundation_import_boundary_audit_added`
