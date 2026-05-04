## 172. Finite QM Core Proof Program

Status:

`finite_qm_core_proof_program_opened`

The previous QM milestone gives executable finite coverage:

1. `35` registered QM experiment rows;
2. `35` executable finite-gate references;
3. `6` universal pattern families;
4. one bench compiler summary.

That is a useful intermediate result. It is not a proof of all QM.

The next task is to separate three different claims:

| Claim | Current status |
|---|---|
| finite readout regression suite | executable |
| finite QM core derivation | target |
| full QM including continuum and first-principles action scale | blocked |

Status:

`qm_claim_levels_separated`

### 172.1. Proof Obligations

The manifest now records `qm_core_proof_obligations`. The verifier checks that
the proof program contains the required obligation set:

| Obligation | Current status | Main blocker |
|---|---|---|
| `finite_operational_core` | `regression_supported` | minimal independent axiom set not proven |
| `probability_measure_layer` | `regression_supported` | uniqueness of the readout probability measure not proven |
| `distinguishability_geometry` | `target` | carrier geometry not selected from IDT alone |
| `hilbert_carrier_derivation` | `blocked` | complex Hilbert structure is still imported as carrier |
| `born_rule_derivation` | `blocked` | square-modulus rule is verified but not derived |
| `reversible_inheritance_symmetry` | `regression_supported` | unitary/antiunitary form not forced by theorem |
| `measurement_facticity_mechanism` | `regression_supported` | projection, POVM-like partial readout, and recoverability are not one theorem |
| `tensor_composition_law` | `target` | composition law and entanglement structure not derived |
| `recompile_35_from_core` | `target` | bench compiles patterns, not every gate from one proven core |
| `continuum_action_scale_extension` | `blocked` | continuum limit and first-principles `hbar_I` remain open |

The verifier also guards the public boundary:

`full_QM_I`

cannot be promoted to:

`derived`

while any obligation remains below `derived`.

Status:

`qm_core_proof_obligation_guard_registered`

### 172.2. Correct Order

The correct route is:

$$
\text{IDT finite operations}
\Rightarrow
\text{probability layer}
\Rightarrow
\text{distinguishability geometry}
\Rightarrow
\text{carrier}
\Rightarrow
\text{Born/readout}
\Rightarrow
\text{reversible inheritance}
\Rightarrow
\text{measurement/facticity}
\Rightarrow
\text{composition}
\Rightarrow
\text{35-gate recompilation}.
$$

This order matters.

It would be weaker to assume Hilbert space first and then prove only internal
Hilbert-space facts. The stronger target is to show why the IDT
distinguishability/facticity structure forces a Hilbert-like carrier, or to
record exactly where it fails.

The highest-risk step is:

`tensor_composition_law`.

Without it, IDT may still reconstruct a finite single-system QM-like theory,
but it cannot claim the composite layer needed for Bell, GHZ, swapping,
teleportation, and no-cloning.

The finite Born/readout route is now executable as:

`born_quadratic_readout_route_demo`.

It checks normalized amplitude packets under phase-invariant, orthogonal-event
additive, facticized context readout. The quadratic modulus readout survives;
linear-modulus alternatives are rejected on the registered two- and
three-branch packets.

This is a finite route toward Born readout, not the full Born theorem. The
universal theorem still depends on closing the carrier and measurement/facticity
obligations.

The finite tensor-composition route is now executable as:

`tensor_composition_route_demo`.

It checks product-context basis size, local dimension multiplication, and
Schmidt-rank factorization witnesses. Product states remain factorizable;
Bell-style states have Schmidt rank two and are not reducible to product
states.

This is a finite route toward the composition layer, not the full monoidal
composition theorem.

The finite measurement/facticity route is now executable as:

`measurement_facticity_route_demo`.

It connects recoverable markers, partial pointer readouts, and stable
projective records through readout gain, disturbance bounds, and recoverability
loss thresholds. This joins the existing projective, partial, decoherence, and
recoverability gates into one finite mechanism route.

The 35-gate finite-core recompile route is now executable as:

`qm_core_recompile_route_demo`.

It records the shared six-operation core, the required finite route gates, the
six universal kernels, the 35 covered experiments, and the 35 finite gate
references. This turns the old bench summary into an explicit manifest contract.

The continuum/action-scale frontier is now executable as:

`continuum_action_frontier_demo`.

It confirms that finite generator reconstruction, translation relation, Weyl
relation, strong-continuity modulus, generator-difference convergence, and the
calibrated action holdout are supported. It keeps the full extension blocked
because first-principles `hbar_I` remains blocked and field-mode limits remain
open.

The full-QM closure frontier is now executable as:

`full_qm_closure_frontier_demo`.

It records the theorem-level blockers that still prevent closure: universal
carrier selection, Hilbert carrier derivation, universal Born derivation,
reversible-symmetry inheritance, apparatus/facticity, monoidal tensor
composition, first-principles `hbar_I`, and field-mode continuum limits. The
gate rejects any premature `derived` status while any listed obligation remains
blocked or open.

The full-QM frontier blockers are now also represented as first-class theorem
cards in the manifest. The verifier requires each frontier requirement to have
a grounded card before the frontier can be treated as an auditable research
graph.

The frontier component status is now locked to the corresponding theorem-card
proof status:

1. `blocked` proof status keeps the frontier component `blocked`;
2. `formal_proof` is required before a component can become `supported`;
3. every other proof status keeps the component `open`.

Status:

`finite_qm_core_route_order_declared`

### 172.3. Next Executable Target

The next executable target is not another experiment gate.

It is:

`distinguishability_geometry_probe`.

This gate should compare the candidate finite carrier geometries:

1. classical simplex;
2. real Hilbert-like carrier;
3. complex Hilbert-like carrier;
4. broader GPT-style cone.

The gate should ask which carriers can support the already registered pattern
requirements:

1. contextual probability readout;
2. interference with \(I_3=0\);
3. reversible inheritance maps;
4. contextual-correlation obstruction;
5. noncopyability;
6. tensor-like composition.

The expected honest outcome may be:

1. a carrier is selected;
2. several carriers survive;
3. the current IDT primitives are insufficient.

All three outcomes are useful. A failed or underdetermined carrier-selection
gate is not a failure of the project; it identifies the next missing primitive
or bridge.

The first probe is now executable as:

`distinguishability_geometry_probe_demo`.

It currently gives this bounded result:

| Candidate carrier | Probe status | Reason |
|---|---|---|
| classical simplex | `rejected` | cannot support interference, contextual obstruction, and noncopyability together |
| real Hilbert-like carrier | `underdetermined` | supports the finite readouts but composition remains unresolved |
| complex Hilbert-like carrier | `survives` | supports all declared finite requirements |
| general GPT-style cone | `underdetermined` | broad enough to fit several requirements, but not uniquely constrained |

The selected carrier remains:

`none`.

This is the right result for now. The probe rejects the purely classical
simplex but does not pretend that IDT has derived complex Hilbert space.

The next separator is now executable as:

`local_tomography_separator_demo`.

It adds the principle that composite states must be determined by joint local
measurement statistics. In finite parameter-count form:

$$
K_{AB}=K_AK_B.
$$

For a complex qubit pair:

$$
K_A=4,\quad K_B=4,\quad K_{AB}=16,
$$

so the separator is satisfied. For a real rebit pair:

$$
K_A=3,\quad K_B=3,\quad K_{AB}=10,
$$

so \(K_{AB}\ne K_AK_B\), and local tomography fails.

The separator therefore rejects the real Hilbert-like carrier if local
tomography is accepted as an IDT composition principle. It still does not
select complex Hilbert uniquely, because a broad GPT cone can remain
underdetermined without additional cone/symmetry restrictions.

The local-tomography route is now refined by:

`idt_local_tomography_derivation_demo`.

This gate does not merely restate the separator. It checks the conditional IDT
route:

1. product readout contexts are closed;
2. joint facticity is exhausted by those product contexts;
3. no stable joint invariant is hidden from every product readout;
4. stable invariants separate across the product readout table.

Under those conditions the finite parameter count is forced:

$$
K_{AB}=K_AK_B.
$$

Any additional joint-only degrees,

$$
K_{AB}>K_AK_B,
$$

are rejected as IDT-inadmissible for this route because they would encode a
stable invariant that cannot be facticized by the declared product contexts.

The context-product route is now executable as:

`context_product_exhaustion_demo`.

It checks the finite witness rule directly. Given local readout contexts
\(A_i\) and \(B_j\), the product-context set must close the full Cartesian
table:

$$
\{A_iB_j\}_{i,j}.
$$

Every stable composite invariant must then have at least one product-context
witness. A candidate with a hidden joint invariant and no witness is rejected as
IDT-inadmissible for this finite route.

This closes one layer of the problem but not the whole theorem. The remaining
gap is now sharper: extend this finite context-product exhaustion rule into a
general carrier-selection theorem, rather than assuming that all admissible
carriers have already been covered.

The first conditional separator theorem is now executable as:

`context_product_local_tomography_theorem_demo`.

It records the conditional theorem card:

`context_product_exhaustion_implies_local_tomography`.

The theorem is deliberately conditional. Under finite context families,
product-context closure, stable-invariant witness completeness,
product-effect separation, and no hidden joint-only facticizable invariant,
product readouts separate stable composite facts. Therefore local tomography
holds for that finite composite route:

$$
K_{AB}=K_AK_B.
$$

The corresponding rebit witness is:

`real_hilbert_composite_hidden_joint_invariant_demo`.

It checks the real-Hilbert composite separator:

$$
K_A=3,\quad K_B=3,\quad K_{AB}=10,\quad K_AK_B=9.
$$

The missing degree is represented by \(Y\otimes Y\). Product readouts over the
local real basis \(\{I,X,Z\}\) cannot distinguish
\(\rho_+=\frac14(I\otimes I+\varepsilon Y\otimes Y)\) from
\(\rho_-=\frac14(I\otimes I-\varepsilon Y\otimes Y)\), while the global
\(Y\otimes Y\) readout distinguishes them. This rejects real-Hilbert-like
finite composite carriers under context-product exhaustion.

Status:

`context_product_local_tomography_conditional_proof`

The purification/filtering route is now executable as:

`idt_purification_filtering_demo`.

It checks two finite consequences of the IDT composition route:

1. a mixed readout can be represented by a recoverable extension whose marginal
   probabilities match the readout packet;
2. a facticized filter restricts support and renormalizes the posterior
   probabilities on the surviving events.

This promotes purification/filtering from a named GPT principle to a finite
IDT route. It still does not prove that every admissible carrier must support
the full categorical or operational purification theorem.

The bounded-correlation route is now executable as:

`idt_bounded_correlation_demo`.

It checks the finite CHSH-style obstruction under the IDT conditions of
single joint-context facticity, normalized context amplitudes, absence of a
global counterfactual fact table, and a stable correlation invariant. Classical
and Tsirelson-edge samples survive the declared bound, while a PR-box-like
sample with \(|S|=4\) is rejected.

This promotes bounded nonclassical correlations from a named separator
principle to a finite IDT route. It still does not prove that the same bound
selects the complete carrier class.

The non-complex Jordan separator is now executable as:

`noncomplex_jordan_separator_demo`.

It checks finite carrier candidates against five IDT route requirements:

1. complex phase orientation;
2. local-tomographic composition;
3. associative tensor composition;
4. purification/filtering route;
5. bounded-correlation route.

Real, quaternionic-like, and exceptional-Jordan-like finite candidates are
rejected by this separator. Complex Hilbert-like structure survives. A generic
GPT cone remains underdetermined.

This is still not the full mathematical classification theorem. It is a finite
IDT exclusion screen for the non-complex Jordan alternatives represented in the
manifest.

The generic-GPT closure separator is now executable as:

`generic_gpt_closure_separator_demo`.

It rejects an unconstrained generic GPT cone because it does not provide finite
route-witness completeness, rules out unwitnessed effect-cone degrees, or
enforce bounded composite correlations. A route-closed GPT subtheory remains
underdetermined, and complex Hilbert-like structure survives.

This narrows the generic-GPT ambiguity without pretending to classify every
possible operational subtheory.

The next GPT separator is now executable as:

`gpt_principle_separator_demo`.

It adds a stricter principle set:

1. local tomography;
2. homogeneous self-dual cone structure;
3. continuous reversible bit symmetry;
4. no third-order interference;
5. purification or filtering;
6. bounded nonclassical correlations.

The current finite result is:

| Candidate carrier | Separator status | Reason |
|---|---|---|
| complex Hilbert-like carrier | `survives` | satisfies all declared separator principles |
| boxworld-like GPT | `rejected` | violates the cone/symmetry, purification/filtering, and bounded-correlation requirements |
| Euclidean Jordan family | `underdetermined` | satisfies part of the cone/symmetry profile, but local tomography and filtering remain unresolved at this level |
| generic GPT cone | `underdetermined` | too broad unless the additional principles are independently established |

The selected carrier remains:

`none`.

This is again intentional. The separator narrows the search space, but it does
not yet prove that IDT alone forces complex Hilbert space.

The current frontier is now executable as:

`carrier_selection_frontier_demo`.

It records the remaining carrier-selection obstructions:

1. extend context-product exhaustion to a carrier-selection theorem;
2. extend purification/filtering to a carrier-selection theorem;
3. extend bounded correlations to a carrier-selection theorem;
4. extend non-complex Jordan exclusion to a classification theorem;
5. extend generic-GPT exclusion to a classification theorem.

The frontier gate checks that those obstructions remain attached to surviving
or underdetermined alternatives. With complex Hilbert-like structure surviving
but Euclidean-Jordan and generic GPT alternatives still underdetermined, the
selected carrier must remain:

`none`.

The frontier status is therefore:

`not_derived`.

The first proof route toward the universal carrier-selection theorem is now
executable as:

`carrier_selection_proof_route_demo`.

It decomposes the theorem into five lemma obligations:

1. context-product exhaustion as a carrier theorem;
2. purification/filtering as a carrier theorem;
3. bounded correlations as a carrier theorem;
4. non-complex Jordan exclusion as a classification theorem;
5. generic GPT exclusion as a classification theorem.

The first lemma is now a `conditional_proof`; the other four currently have
finite witnesses but remain below `formal_proof`. The route therefore still
keeps `universal_carrier_selection_theorem` at `open`.

The first lemma route is now executable as:

`context_product_carrier_lemma_route_demo`.

It connects `context_product_local_tomography_theorem_demo`,
`real_hilbert_composite_hidden_joint_invariant_demo`,
`context_product_exhaustion_demo`, and
`idt_local_tomography_derivation_demo` to the carrier-selection proof route.
The route records three finite exclusions:

1. hidden joint invariant composite;
2. real rebit pair;
3. hidden joint sector.

It is now `conditional_proof`, not `formal_proof`, because the theorem is
conditioned on context-product exhaustion and still does not close generic GPT
or route-closed subtheory underdetermination.

The second lemma route is now executable as:

`purification_filtering_carrier_lemma_route_demo`.

It connects `idt_purification_filtering_demo` to the carrier-selection proof
route. The route records two finite exclusions:

1. insufficient environment extension;
2. zero-support filter.

It is now backed by the conditional theorem card:

`purification_filtering_implies_recoverable_support_update`.

The executable verifier is:

`purification_filtering_recoverable_support_theorem_demo`.

Under finite context families, recoverable extension contexts, marginal readout
consistency, facticized filters, and posterior support renormalization,
admissible filtering is a support-restricted recoverable update. The theorem
records two rejected cases:

1. insufficient environment extension;
2. zero-support filter.

It is now `conditional_proof`, not `formal_proof`, because recoverable
extension contexts and posterior support renormalization are still assumptions
of this route rather than consequences of the IDT primitives alone.

The third lemma route is now executable as:

`bounded_correlation_carrier_lemma_route_demo`.

It connects `idt_bounded_correlation_demo` and `gpt_principle_separator_demo`
to the carrier-selection proof route. The route records two finite exclusions:

1. PR-box-like correlation resource;
2. boxworld-like GPT carrier.

It is now backed by the conditional theorem card:

`bounded_correlation_screen_rejects_superquantum_boxes`.

The executable verifier is:

`bounded_correlation_screen_theorem_demo`.

Under finite context families, single joint-context facticity, normalized
context amplitudes, no global counterfactual table, stable correlation
invariants, and declared GPT separator principles, Tsirelson-bounded samples
survive while superquantum counterexamples are rejected. The theorem records:

1. surviving classical and Tsirelson-edge cases;
2. rejected PR-box-like and boxworld-like cases.

It is now `conditional_proof`, not `formal_proof`, because the GPT separator
principles and full bounded-correlation screen are still assumptions of this
route rather than consequences of the IDT primitives alone.

The fourth lemma route is now executable as:

`noncomplex_jordan_classification_lemma_route_demo`.

It connects `noncomplex_jordan_separator_demo` to the carrier-selection proof
route. The route records three finite exclusions:

1. real Hilbert-like carrier;
2. quaternionic Hilbert-like carrier;
3. exceptional Jordan-like carrier.

It is now backed by the conditional theorem card:

`noncomplex_jordan_separator_rejects_noncomplex_samples`.

The executable verifier is:

`noncomplex_jordan_separator_theorem_demo`.

Under a finite candidate family and the declared route requirements for
complex phase orientation, local-tomographic composition, associative tensor
composition, purification/filtering, and bounded correlations, the theorem
rejects the real-Hilbert-like, quaternionic-Hilbert-like, and
exceptional-Jordan-like samples.

It is now `conditional_proof`, not `formal_proof`, because the generic GPT cone
remains underdetermined and the finite candidate family is still assumed.

The fifth lemma route is now executable as:

`generic_gpt_classification_lemma_route_demo`.

It connects `generic_gpt_closure_separator_demo` and
`carrier_selection_frontier_demo` to the carrier-selection proof route. The
route records one finite exclusion:

1. unconstrained generic GPT cone.

It also records two remaining underdetermined candidates:

1. route-closed GPT subtheory;
2. generic GPT cone.

It still remains `finite_witnessed`, not `formal_proof`, because the generic
GPT closure samples must be promoted to a classification theorem and the
route-closed subtheory must be shown to collapse to the complex Hilbert carrier
under IDT primitives.

Status:

`carrier_selection_proof_route_initialized`

Status:

`context_product_carrier_lemma_route_initialized`

Status:

`purification_filtering_carrier_lemma_route_initialized`

Status:

`bounded_correlation_carrier_lemma_route_initialized`

Status:

`noncomplex_jordan_classification_lemma_route_initialized`

Status:

`generic_gpt_classification_lemma_route_initialized`

The carrier-selection theorem card is now directly locked to
`carrier_selection_proof_route_demo`. The verifier rejects a theorem card that
claims `formal_proof` while the route remains `open`, and it requires each
theorem-route lemma to cite its executable lemma route.

Status:

`carrier_selection_theorem_grounding_locked`

This is the useful proof boundary: IDT has a finite executable screen that
narrows the carrier space, but it does not yet have the missing theorem that
selects complex Hilbert space from the language alone.

Status:

`distinguishability_geometry_probe_selected`

Status:

`distinguishability_geometry_probe_executable`

Status:

`local_tomography_separator_executable`

Status:

`idt_local_tomography_derivation_executable`

Status:

`context_product_exhaustion_executable`

Status:

`idt_purification_filtering_executable`

Status:

`idt_bounded_correlation_executable`

Status:

`noncomplex_jordan_separator_executable`

Status:

`generic_gpt_closure_separator_executable`

Status:

`born_quadratic_readout_route_executable`

Status:

`tensor_composition_route_executable`

Status:

`measurement_facticity_route_executable`

Status:

`qm_core_recompile_route_executable`

Status:

`continuum_action_frontier_executable`

Status:

`full_qm_closure_frontier_executable`

Status:

`full_qm_frontier_theorem_cards_grounded`

Status:

`full_qm_frontier_status_card_locked`

Status:

`gpt_principle_separator_executable`

Status:

`carrier_selection_frontier_executable`
