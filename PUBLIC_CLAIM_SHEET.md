# Public Claim Sheet

This sheet is the public boundary for the current IDT snapshot.

## One-Sentence Thesis

IDT is an executable reconstruction language for separating physical readouts,
calibrations, bridge assumptions, experimental gates, and blocked claims before
turning a candidate theory into public claims.

## Why It Is Needed

Many speculative theory projects fail because derivations, calibrations, fitted
parameters, bridge assumptions, and empirical checks are mixed together in prose.
IDT is useful now because it makes those roles explicit and machine-checkable.

The current value is not a replacement for QM or GR. The value is a disciplined
workflow for:

1. stating what is derived, conditional, calibrated, or blocked;
2. freezing assumptions before touching data;
3. rejecting bridges that only work after post-fit tuning;
4. keeping failed, near-miss, and surviving candidates comparable;
5. giving AI scientific agents a structured claim ledger instead of free-form
   theoretical text;
6. turning the ledger into a compact research graph before escalating physics
   claims.

## Auditable Successes

Current theory version: `v8.0.0`.

The current verifier manifest is executable and checks the public claim ledger:

```bash
python3 -m theory_verifier --json theory_verifier_manifest.json
python3 scripts/check_declarative_rules.py --json
python3 -m unittest discover -s tests
```

The main current successes are bounded and methodological:

1. Finite QM readout compatibility is executable. The verifier covers
   Born/context probability tables, two-path interference, Sorkin `I3 = 0`,
   marker/eraser visibility, unitary context maps, projective readout
   repeatability, Bell/CHSH no-signalling checks, amplitude-derived CHSH tables,
   and the singlet angle model with `|S| = 2*sqrt(2)`.
2. The QM boundary is explicit. These are finite readout gates and known-formula
   compatibility checks, not a claim that full QM is derived.
3. The action-scale route is controlled. `calibrated_hbar_I` can be used as an
   explicit our-universe anchor for operational reconstruction, while
   first-principles `hbar_I` remains a blocked claim. The current verifier also
   checks a no-refit `phase_action_conversion_I` scaffold across
   energy-frequency, momentum-wavenumber, action-phase, spectral, and
   interference fixtures; this is calibrated consistency, not derivation.
4. The gravity route is controlled. `calibrated_G_I` is a calibrated target, and
   first-principles `G_I` remains blocked until the missing source-response and
   vacuum-stiffness inputs are independently supplied.
5. The SPARC weak-gravity front already produces useful exclusions. It anchors
   real DDO154 data, rejects insufficient amplitudes, blocks post-fit residual
   provenance, rejects a proportional radius map, records a baryonic
   acceleration near miss, and rejects a frozen-`q` held-out transfer.
6. The sector role taxonomy is machine-guarded. Symbols must be classified as
   structural selectors, dimensional anchors, dimensionless couplings, bridge
   assumptions, derived readouts, experimental gates, or blocked claims.
7. The IDT-MetaLang research graph contract is executable. It records claim
   role typing and dependency DAG checks as implemented, while proof status,
   prediction protocol, failure ledger, compact core, and theorem cards remain
   partial rather than complete. Its evidence references must resolve to real
   manifest objects, schema surfaces, verifier checks, or Markdown sections.
   Full-QM frontier blockers now have first-class theorem cards.
8. The foundation import boundary is executable. The verifier separates current
   QM imports such as complex amplitudes, PSD kernels, quadratic readout,
   tensor/product composition, unitary maps, and calibrated action phase from a
   carrier-neutral primitive core: history space, event algebra, readout
   contexts, and inheritance acts. The primitive core is now a first-class
   contract: its laws may depend only on the primitive definition section, and
   every excluded import is routed to an explicit theorem or proof obligation.
9. A new facticizable-distinguishability closure frontier is executable as a
   candidate principle. It tests whether stable inherited distinguishability
   must have finite admissible readout witnesses, while retaining negative
   controls and open QM obligations.
10. A QM frontier probe is executable. It audits the route to `full_QM_I` as
   `pass`, `open`, or `frontier` cells. The current diagnosis is no longer an
   opaque blocker: primitive-core and context-product tomography pass, several
   selector/composition/dynamics cells have conditional closure routes, and the
   remaining open frontiers are context-first universal endpoint data,
   carrier-frontier exhaustion, and first-principles action scale.
11. A fundamental-unknownness bridge audit is executable. It records candidate
   principles shared by the QM and gravity fronts: contextual finitization,
   holonomy/branch source selection, source-clock response, residual holdout
   discipline, composition witness exhaustion, and scale-anchor independence.
   The candidate routes to Hilbert carrier, Bell contextual correlations,
   gravity clock/source structure, and shared action scale remain search
   routes, not proof upgrades.
12. The universal Born/Hilbert frontier is now conditionally closed as a single
   contract: context-first universal endpoint data plus carrier-frontier
   exhaustion imply exact universal Born readout and frontier-scoped Hilbert
   representation. This does not derive those assumptions from B0, does not
   prove `full_QM_I`, and does not derive `hbar_I`.
13. A Hilbert/spacetime bridge audit is executable. It records the hypothesis
   that Hilbert carrier structure, Bell contextual correlations, and spacetime
   geometry may be different readout projections of a deeper
   clock-context-source/holonomy layer. It also enforces the boundary that GR is
   treated only as a reflection or limit candidate, not as a primitive source.
14. A Hilbert/Bell/gravity scale probe is executable. It records the broader
   candidate that the same base mechanism may affect more than QM, while
   ordinary finite QM gates only expose the Hilbert/Bell projection because the
   gravity-facing clock/source response is scale-separated. The probe keeps
   this as an open common-source route, not as a derivation of Hilbert, Bell
   correlations, GR, `hbar_I`, or `G_I`.
15. The proof-verification boundary is executable. Current `formal_proof`
   markers cover (a) finite IDT-Core/meta-invariants and (b) five finite
   full-QM-closure sub-obligations proven under the full proof-ledger contract
   (see item 23). All `formal_proof` markers must be covered by proof cards
   with machine-checkable artifacts and commands, and the body of each Lean
   artifact is scanned for forbidden representative symbols
   (`InnerProductSpace`, `PositiveSemidefinite`, `IsUnitary`,
   `TensorProduct`, etc.). The proof pipeline checks that the generated Lean
   finite-core semantic artifact is synchronized with the manifest, then runs
   Lean 4 and the IDT verifier. None of these formal proofs derives universal
   QM, Hilbert space, the Born rule, tensor composition, unitary dynamics, or
   first-principles `hbar_I`.
16. The v7 context-first primitive-base boundary is executable. It records
   admissible contexts, local outcome-event presheaves, inheritance
   transitions, facticization witnesses, and stable distinguishability as the
   active lower-base candidates. The old history/event/readout scaffold is now
   legacy compatibility only, not the current primitive base. The B1 Lean route
   binds admissibility to the successor base and preserves no-target-import
   guards, but remains a conditional route. This does not upgrade QM, Hilbert
   space, Born rule, GR, `hbar_I`, or `G_I`.
17. The QM semantic-kernel route is executable. It groups the current full-QM
   proof surface into six clusters spanning 21 sub-obligations:
   residual/projective, representation, readout, dynamics, composite, and
   physical scale. Of those 21 sub-obligations, 5 now carry real
   machine-checked Lean artifacts under the full proof-ledger contract (see
   item 23) and 16 carry conditional package artifacts awaiting formalization;
   0 are missing. B1 projects to that kernel without losing package fields,
   and each cluster has an explicit B1-projected theorem. The next proof
   target is the semantic content of the open kernel core; this is not a
   proof of `full_QM_I`.
18. The QM semantic-content scaffold bundle is executable. It machine-checks
   finite projective, readout, inheritance-action, product-tomography,
   monoidal, projective-limit, and calibrated-scale fragments as one Lean
   artifact. This removes a proof-engineering gap for those fragments and
   concentrates the remaining full-QM work in structural target theorems, not
   in unchecked scaffold files.
19. The CGSC structural target kernel is executable. It conditionally closes
   the six structural QM target clauses from seven context-generated stable
   closure clauses and preserves no-target-import boundaries. At this layer
   alone the kernel is conditional; the B1 derivation below supplies the clause
   source, while external QM adequacy remains open.
20. The B1 CGSC clause derivation is executable. All seven CGSC clauses are
   now machine-derived from the B1 primitive-base witness interface, and the
   six structural target slots are filled inside the current IDT package
   semantics. A later Lean audit exposes a claim-source aliasing boundary:
   several named target slots share one smaller source proposition, so this is
   a source-witness scaffold, not an independent physical derivation of those
   targets. This does not yet prove external Hilbert/Born/unitary/tensor
   equivalence or a B0-alone derivation.
21. The Born/Hilbert frontier is now narrowed rather than opaque. The finite
   Born-square readout is selected under the checked oriented endpoint
   discipline, and a new Lean bridge proves that the existing context-first
   constructive witness package supplies primitive pairwise endpoint coverage,
   endpoint-stable binary oriented contexts, and ternary-facticization blocking
   once universal endpoint data is provided. The remaining mathematical core is
   deriving that endpoint data from B0 or the accepted successor base; a
   B1-only negative control is checked and does not force that endpoint data.
22. The full v7 recovery layer is now explicit in Lean status ledgers. The
   migrated surface covers B0/projection boundaries, B1/B2 pressure,
   hypothesis batches, NUSD/finite-projection determinacy, zero-base/search
   results, normalized-overlap/compressed finite-QM routes, Born/readout,
   Schrodinger-frequency dynamics, Hilbert carrier pressure, late CGSC routing,
   and the full-QM proof burden. These modules preserve the research map; they
   do not upgrade Born, Hilbert space, Schrodinger dynamics, or full QM to
   proved.
23. Five finite full-QM-closure sub-obligations now carry real
   machine-checked Lean artifacts under the full proof-ledger contract, with
   `claim_count = 38` in the synchronized Lean ledger. They are:
   `context_normalization` (F → μ(A) ≥ 0), `exclusivity_additivity`
   (μ(A∪B) = μ(A) + μ(B) under facticity), `coarse_graining_consistency`
   (3-block iterated additivity), `operational_equivalence_probability`
   (μ(A) = μ(A') under W/Γ-preserving bijection), and `projective_action`
   (monoid-action laws for `projectiveAction` on projective facts). Each Lean
   file compiles under `lake env lean` with no `sorry`/`admit`/`axiom`, and
   the body of each file is scanned for forbidden representative symbols so
   that none of them silently imports Hilbert-space, Born-rule,
   positive-operator, unitary, tensor, or projective-Hilbert machinery. The
   full-QM-closure verdict remains `CONDITIONAL_PACKAGE_ARTIFACTS_REGISTERED`
   with `proved = 5`, `conditional_artifacts = 16`, `missing_artifacts = 0`.
   This is a claim about five finite sub-obligations, not a derivation of
   universal QM, the universal Born rule, Hilbert space, tensor composition,
   unitary dynamics, or first-principles `hbar_I`. One further dynamics
   sub-obligation, `overlap_preservation_dynamics`, was investigated and
   deliberately left conditional: its Lean artifact proves closure properties
   of an IDT-native `PreservesOverlap` predicate but does not derive
   preservation from bijectivity alone, so promoting it would have been an
   overclaim; the wall is recorded in
   `Proofs/MetaLang/V8QmResearchTaskLedger.lean` as
   `overlap_preservation_dynamics_bridge_wall_recorded`.

## What The Verifier Catches

The verifier is designed to reject progress by relabeling. It blocks:

1. a derived claim that depends on an open or blocked object;
2. a calibrated anchor presented as a first-principles derivation;
3. per-experiment action-scale refits presented as one universal anchor;
4. a structural selector used as a dimensional constant;
5. a bridge assumption relabeled as a derived readout;
6. SPARC residual claims that reuse the observed residual as their own source;
7. full-QM claims while the action scale, generator, apparatus, and facticity
   spine remain incomplete;
8. relabeling current QM imports as primitive or first-principles derived
   structures;
9. a `formal_proof` marker without a proof-ledger card and machine-checkable
   proof artifacts.
10. treating the v7 context-first base candidate as a completed proof of
   Hilbert space, Born readout, GR, full QM, `hbar_I`, or `G_I`.

## What Is Explicitly Not Claimed

IDT currently does not claim:

1. a completed derivation of QM;
2. a completed derivation of GR;
3. a numerical first-principles derivation of `hbar_I`, `G_I`, or
   `alpha_em_I`;
4. an explanation of dark matter or dark energy;
5. experimental confirmation as a replacement theory;
6. a successful SPARC galaxy-rotation fit.
7. a derivation of complex Hilbert space, the universal Born rule, tensor
   composition, unitary dynamics, or first-principles `hbar_I` from IDT
   primitives.
8. a completed migration from the legacy executable primitive scaffold to the v7
   context-first lower base.
9. treating six-cluster conditional QM coverage as a completed derivation of
   Hilbert space, Born rule, tensor composition, unitary dynamics, or
   `full_QM_I`.
10. treating machine-checked finite scaffolds as a universal derivation of QM.
11. treating the conditional universal Born/Hilbert frontier closure as a
   B0-alone derivation or as a proof of `full_QM_I`.

## Derived, Conditional, Calibrated, Blocked

Current public classification:

| Category | Examples |
|---|---|
| Machine-checked finite proofs | `context_normalization`, `exclusivity_additivity`, `coarse_graining_consistency`, `operational_equivalence_probability`, `projective_action` (full proof-ledger contract; no QM/Hilbert/Born derivation implied) |
| Derived or finite executable readouts | context Born table, two-path interference, Sorkin `I3 = 0`, finite Bell/CHSH gates |
| Derived conditional | amplitude packet, unitary context evolution, generator-side QM spine, operational QM with declared anchors, six-cluster QM semantic-kernel route, finite semantic-content scaffold bundle, universal Born/Hilbert frontier closure under explicit source/frontier assumptions |
| Diagnosed walls | deriving context-first universal endpoint data from B0 or the accepted successor base; proving carrier-frontier exhaustion over all admissible carriers; `overlap_preservation_dynamics` bridge wall (recorded in Lean ledger) |
| Calibrated anchors | `calibrated_hbar_I`, calibrated gravity anchors and targets |
| Structural selectors | primitive holonomy/source and topology/winding selector targets |
| Experimental gates | SPARC gates, Bell/CHSH gates, residual provenance gates |
| Blocked claims | first-principles `hbar_I`, first-principles `G_I`, first-principles `alpha_em_I`, `full_QM_I = derived` |

## Next Public Milestones

The next public milestone is not a stronger slogan.

The immediate language milestone is to promote prediction and failure records
into first-class manifest objects, and then extend theorem cards beyond the
full-QM frontier.

The next physics milestone remains one pre-registered, non-refitted bridge that
survives an independent holdout gate. The most promising current route is
weak-gravity closure:

```text
source response + vacuum stiffness + calibrated action anchor
=> calibrated_G_I target
=> independent no-refit gate
```

Until that gate survives, the project should be presented as a controlled
research programme with auditable successes and useful exclusions, not as a
completed physical theory.
