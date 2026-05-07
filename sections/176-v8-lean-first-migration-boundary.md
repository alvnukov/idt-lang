## 176. V8 Lean-First Migration Boundary

Status: migration boundary, not a new physical proof.

The v8 direction is Lean-first:

```text
proved claim -> Lean artifact
research route -> IDT declarative language / manifest
numeric gate -> executable trusted checker
legacy Python verifier -> safety net, not proof source of truth
```

The migration freezes new physical research claims until the already recorded
claim discipline has been moved into Lean. The first Lean layer is:

```text
Proofs/MetaLang/V8VerificationLanguage.lean
Proofs/MetaLang/V8ContextFirstPrimitiveBase.lean
Proofs/MetaLang/V8TheoremCardLedger.lean
Proofs/MetaLang/V8CurrentStatusSnapshot.lean
Proofs/MetaLang/V8ExternalCheckerBoundary.lean
Proofs/MetaLang/V8StatusTransitionPolicy.lean
Proofs/MetaLang/V8DependencyGraphPolicy.lean
Proofs/MetaLang/V8ProofArtifactContract.lean
Proofs/MetaLang/V8LeanFirstTrustKernel.lean
Proofs/MetaLang/V8CoreClaimDisciplineRules.lean
Proofs/MetaLang/V8ControlledVocabularyInventory.lean
Proofs/MetaLang/V8StoppedResearchFrontier.lean
```

This layer encodes:

1. controlled vocabulary discipline;
2. `formal_proof` requires a Lean proof artifact;
3. `derived` claims cannot depend on open or blocked dependencies;
4. theorem cards and proof obligations must preserve machine boundaries;
5. the current proof-status snapshot has no false `formal_proof` closure;
6. Python/numeric/data gates may supply finite verifier passes but not
   `formal_proof`;
7. status transitions require explicit evidence and cannot silently upgrade;
8. dependency records require grounded edges, acyclicity, and clean forward
   status dependencies;
9. formal proof upgrades require runnable Lean artifacts with path, theorem
   name, and check command;
10. accepted theorem-card, transition, dependency, artifact, and legacy-checker
    ledgers compose into a single Lean-first trust kernel;
11. the v8 core claim-discipline specification has exactly the accepted six
    rule shapes mirrored from the declarative input;
12. the v8 controlled vocabulary is mirrored into Lean with project-local terms
    kept distinct from standard scientific/formal-methods vocabulary;
13. the context-first primitive base:

```text
B0 = (C, O, I, R, D)
```

where:

- `C` is admissible context cover/category;
- `O` is local outcome-event presheaf;
- `I` is inheritance transition family;
- `R` is facticization/readout witness relation;
- `D` is stable distinguishability relation.

The old `H/E/M/I` scaffold is retained only as compatibility/readout
machinery. It is not the current primitive base.

The stopped QM frontier is also encoded, without upgrading the claim:

```text
B1
+ context-first constructive witness completeness
+ carrier-frontier exhaustion
=> finite standard-QM sector closure
```

Exact fundamental QM still requires:

1. lower-base derivation of B1;
2. lower-base derivation of context-first witness completeness;
3. lower-base derivation of carrier-frontier exhaustion;
4. external Hilbert/Born/unitary/tensor adequacy;
5. exact universal Born readout;
6. first-principles physical phase scale.

Therefore v8 does not claim that QM is proved. It changes the trust model:
anything marked as proved must survive Lean.
