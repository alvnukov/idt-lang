# IDT Lang

![QM Scientific Status](https://img.shields.io/badge/QM-context--first_Born--Hilbert_frontier-yellow)
[![IDT v8 Lean CI](https://github.com/alvnukov/idt-lang/actions/workflows/v8-lean-status.yml/badge.svg?branch=main)](https://github.com/alvnukov/idt-lang/actions/workflows/v8-lean-status.yml)

Inherited Distinguishability Protolanguage (IDT) is a candidate executable
language for interpreting the physical structure of the universe, designed for
both human researchers and AI scientific agents.

Its goal is not to replace physics by assertion. The goal is to provide a
disciplined map from observations to readouts, from hypotheses to bounded
bridges, and from assumptions to explicit anchors and gates. If matured, IDT
could become a shared world-interpretation layer: a way for humans and AI
systems to organize evidence, test explanations, expose gaps, and progressively
deepen structural understanding of the physical world.

The project has a personal origin in a long-running attempt to make physical
systems intelligible, not only calculable. See [Origin and Motivation](ORIGIN.md)
for the human context behind the protolanguage.

## Current Status

This repository is a clean public snapshot of the modular canonical source.

The current object is a reconstruction framework, not a completed replacement
for QM or GR. Its present value is methodological and test-directed:

- explicit claim boundaries;
- no-refit gates;
- calibrated anchor protocols;
- real-data fixtures;
- a finite verifier that turns candidate bridges into auditable checks;
- a role taxonomy for separating structural selectors, dimensional anchors,
  couplings, bridge assumptions, readouts, experimental gates, and blocked
  claims;
- a research-graph contract for tracking which parts of the language are
  implemented, partial, or still missing.

For a compact public boundary, see the [Public Claim Sheet](PUBLIC_CLAIM_SHEET.md).

## AI Agent Quickstart

AI agents should start from [AI Agent Guide](AI_AGENT_GUIDE.md), not from a full
repository scan.

The intended first context object is the compact v8 AI theory graph:

```bash
python scripts/build_ai_theory_graph.py --output dist/idt-v8-ai-theory-graph.json
python scripts/query_ai_theory_graph.py --graph dist/idt-v8-ai-theory-graph.json validate --repo-root . --check-source-hashes
python scripts/query_ai_theory_graph.py --graph dist/idt-v8-ai-theory-graph.json summary
```

The graph is not committed to the repository and is not zipped. On a published
GitHub Release, CI builds, validates, and attaches the raw JSON file
`idt-v8-ai-theory-graph.json` as a release asset.

Use this boundary when answering questions about the theory:

- official project name: **IDT, Inherited Distinguishability Theory**;
- current language/proof architecture: **Lean + IDT v8**;
- proof authority: **Lean artifacts only**;
- graph role: compact context/index for AI agents, not proof authority;
- manifest role: residual research input, not proof truth;
- current scientific status: reconstruction framework with finite gates,
  conditional Lean routes, and explicit open frontiers; not a completed
  derivation of QM or GR.

## What This Snapshot Demonstrates

The current public value is that IDT turns speculative theory work into a
checked claim ledger. It shows which parts are finite executable readouts, which
parts are calibrated, which bridges are still conditional, and which claims are
blocked.

Current auditable results:

- finite QM readout gates: Born/context tables, two-path interference, Sorkin
  `I3 = 0`, marker/eraser visibility, unitary context maps, projective readout
  repeatability, Bell/CHSH no-signalling checks, amplitude-derived CHSH tables,
  and a singlet angle model with `|S| = 2*sqrt(2)`;
- anti-overclaim gates: the verifier rejects premature first-principles claims
  for `hbar_I`, `G_I`, `alpha_em_I`, and `full_QM_I`;
- calibrated-anchor discipline: `calibrated_hbar_I` may be used as an explicit
  our-universe action anchor, while first-principles `hbar_I` remains blocked;
- calibrated action-scale reconstruction: one shared
  `phase_action_conversion_I` anchor is checked across energy-frequency,
  momentum-wavenumber, action-phase, spectral, and interference fixtures, with
  per-experiment refits rejected;
- real-data weak-gravity gates: the SPARC front anchors real DDO154 data,
  rejects post-fit residual provenance, records near misses, and rejects
  held-out transfer for the current frozen candidate;
- sector role taxonomy: selectors, dimensional anchors, couplings, bridge
  assumptions, readouts, experimental gates, and blocked claims are separated
  before public claims are allowed;
- IDT-MetaLang research graph: claim roles and the dependency DAG are
  implemented, while proof-status, prediction, failure-ledger, compact-core,
  and theorem-card surfaces remain explicitly partial; its evidence references
  are grounded against real manifest objects, schema surfaces, verifier checks,
  or Markdown sections, and full-QM frontier blockers now have first-class
  theorem cards.
- v8 Lean-first migration: the language-level proof-status boundary,
  context-first primitive base, and current stopped QM frontier are now encoded
  in Lean under `Proofs/MetaLang/`. The old Python verifier is deprecated
  compatibility infrastructure; the target proof architecture is Lean + IDT v8.
  The first Lean-sourced experiment-protocol probe is available as
  `lake exe idt_v8_protocol_status`; use `--json` for machine-readable status
  `--documents-json` for the accepted IDT v8 document inventory,
  `--residuals-json` for the Lean-sourced QM residual experiment list, and
  `--check-boundary` for the current Lean boundary check. It reports the
  certified-executable-check boundary and does not assign physical/QM
  `formal_proof` status.
- primitive-core contract: the current primitive surface is context-first.
  Admissible context covers, local outcome-event presheaves, inheritance
  transition families, facticization witnesses, and stable distinguishability
  are the active lower-base candidates. The old history/event/readout scaffold
  is now legacy compatibility only, not the current primitive base.
- v7 context-first primitive-base boundary: the B1 Lean route constructor-binds
  admissibility and no-target-import boundaries for the successor-base
  candidate. The latest Born/Hilbert pass narrows the live readout frontier to
  deriving context-first universal endpoint data from B0 or the accepted
  successor base, while carrier-frontier exhaustion remains the Hilbert-side
  universal quantifier.
- v7 recovery layer: the full v7 research map is now preserved as Lean status
  ledgers under `Proofs/QMClosure/V7*.lean`. The migrated surface covers
  B0/projection boundaries, B1/B2 pressure, hypothesis batches, NUSD/FPD,
  zero-base/search results, normalized-overlap/compressed finite-QM routes,
  Born/readout, Schrodinger-frequency dynamics, Hilbert-carrier pressure, late
  CGSC routing, and the full-QM burden ledger. This keeps prior research from
  being collapsed into the v8 residual ledger; every recovered route remains an
  obligation, conditional hit, rejected route, or wall rather than an upgraded
  physical/QM proof.
- QM semantic-kernel route: the current full-QM proof surface is grouped into
  six conditional clusters covering 21 obligations: residual/projective,
  representation, readout, dynamics, composite, and physical scale. B1 now
  projects to this six-cluster kernel without losing package fields, and each
  cluster has an explicit B1-projected theorem. This narrows the next proof
  target to semantic content inside the open kernel core; it is not a proof of
  `full_QM_I`.
- QM semantic-content scaffolds: the finite projective, readout,
  inheritance-action, product-tomography, monoidal associativity,
  projective-limit, and calibrated-scale scaffolds are now compiled as a single
  Lean bundle. This removes a proof-engineering gap for those finite fragments;
  the later B1/CGSC artifacts now close the six structural target clauses
  inside the current package semantics.
- CGSC structural target kernel: the six structural QM blockers are now
  conditionally closed by one Lean artifact from seven context-generated stable
  closure clauses, while preserving the no-target-import boundary. At this
  layer alone the kernel is conditional; the next B1 derivation supplies the
  clause source, while external QM adequacy remains open.
- B1 CGSC clause derivation: all seven CGSC clauses are now machine-derived
  from the B1 primitive-base witness interface in Lean, and the same artifact
  closes the six structural target clauses inside the current IDT package
  semantics.
  The remaining frontier is external adequacy: prove that this B1-derived
  package reconstructs Hilbert/Born/unitary/tensor QM with the intended
  universal physical meaning, not only as an internal obligation bundle. The
  semantic-kernel evaluator now removes the six B1-closed structural blockers
  and two finite-scaffold closures from the live open core; the remaining
  frontier is the all-context readout boundary: context-first universal endpoint
  data. A new Lean bridge proves that the existing context-first constructive
  witness package supplies primitive pairwise endpoint coverage, endpoint-stable
  binary oriented contexts, and ternary-facticization blocking, so it selects
  the Born-square readout without importing Born. The current primitive
  discipline still admits a local ternary witness, and a B1-only endpoint-data
  negative control is now checked, so current B1/scaffold closure does not
  select universal Born by itself. The calibrated phase-scale bridge remains an
  accepted boundary only, not a first-principles derivation of `hbar_I`; the
  new action-scale reconstruction gate only tests one shared calibrated anchor.
- Universal Born/Hilbert frontier: a new Lean contract closes exact universal
  Born readout and frontier-scoped Hilbert representation together under
  context-first universal endpoint data and carrier-frontier exhaustion. This is
  a conditional frontier
  closure, not a B0-alone derivation and not a proof of `full_QM_I`; the live
  lower obligations are deriving that context-first endpoint data from B0 or the
  accepted successor base and proving carrier-frontier exhaustion without
  importing Born or complex Hilbert space.
- facticizable distinguishability closure frontier: the candidate lower-level
  principle says that stable inherited distinguishability must have finite
  admissible readout witnesses; hidden joint invariants, global fact tables,
  unconstrained GPT cones, and nonfinite residuals are tracked as negative
  controls without closing QM.
- QM frontier probe: the verifier audits the route to `full_QM_I` as diagnostic
  cells. Earlier hard blockers have been narrowed into explicit proof
  frontiers: context-first universal endpoint data, carrier-frontier exhaustion,
  and first-principles action scale.
- fundamental-unknownness bridge audit: the current base-theory search compares
  the QM proof frontier with gravity/clock/source routes. It records six
  candidate bridge principles and four route candidates, including possible
  Hilbert and Bell routes, while preserving the status that Hilbert, Bell
  derivation, and shared action scale are not closed.
- Hilbert/spacetime bridge audit: the possible Hilbert/Bell/gravity connection
  is now tracked with an explicit GR-reflection boundary. Metric/GR structure
  may only enter as a readout or limit candidate of deeper clock-source-context
  structure, not as a primitive foundation.
- Hilbert/Bell/gravity scale probe: the broader candidate link is tracked as a
  scale-hidden common-source route. QM-scale gates may expose Hilbert/Bell
  readouts while gravity-facing clock/source response remains suppressed or
  unresolved; this is recorded as an open research route, not a proof.
- proof-verification ledger: current `formal_proof` markers are finite
  IDT-Core/meta-invariants only, and they must be covered by proof cards with
  machine-checkable artifacts and commands. The current proof pipeline first
  synchronizes the generated Lean finite-core semantic artifact against the
  manifest, then runs Lean 4 plus the IDT verifier.

These are successes of reconstruction discipline and executable claim control.
They are not claims that IDT has already derived all of QM, GR, or the constants
of nature.

## Repository Layout

- `AI_AGENT_GUIDE.md` — compact entry point for AI agents: graph workflow,
  primitives, status boundaries, and perspective.
- `ORIGIN.md` — project origin and motivation.
- `PUBLIC_CLAIM_SHEET.md` — public claim boundary and current auditable
  successes.
- `PROTOLANGUAGE.md` — canonical entry point and public positioning.
- `sections/` — modular theory body.
- `scripts/graph_query.py` — file-based research graph query and cautious edit
  helper for the verifier manifest.
- `scripts/build_ai_theory_graph.py` — compact source-grounded theory graph
  packer for AI agents.
- `scripts/query_ai_theory_graph.py` — read-only v8 graph query CLI for
  summaries, local neighborhoods, references, and source pointers.
- `theory_verifier/ai_theory_graph.py` — shared typed graph library used by the
  packer and query CLI.
- `scripts/sync_formal_proof_ledger.py` — generates/checks the Lean finite-core
  semantic proof artifact from the current manifest.
- `scripts/check_proofs.py` — runs proof-card checker commands.
- `scripts/check_declarative_rules.py` — checks v8 declarative rule files.
- `scripts/check_all.py` — one-command local verifier, proof, and test pipeline.
- `Proofs/` — Lean proof artifacts.
- `Experiments/` — Lean-sourced executable protocol probes.
- `rules/v8/` — declarative v8 verification specifications.
- `theory_verifier/` — compatibility Python package; `declarative.py` remains
  the active IDT v8 input checker, while the legacy manifest verifier is not
  proof authority.
- `theory_verifier_manifest.json` — current machine-checkable manifest.
- `tests/` — verifier unit tests.
- `data/` — documented data anchors used by verifier-facing research notes.

## Language Policy

English is the canonical language of the project. The primary README, canonical
source, verifier manifests, code, tests, and release notes should remain in
English.

Translations into other languages are welcome as secondary documentation, but
they must preserve the same claim boundaries as the English source. If a
translation conflicts with the English canonical text, the English text is
authoritative.

## License

This repository is licensed under the Apache License, Version 2.0. See
[`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).

## Verify

Fetch external SPARC data first:

```bash
python3 scripts/fetch_sparc_data.py
```

Then run:

```bash
python3 scripts/check_all.py
```

The proof-only lane is:

```bash
python3 scripts/check_proofs.py
```

The IDT v8 Lean CI lane behind the `IDT v8 Lean CI` badge runs:

```bash
ruff check theory_verifier tests scripts
mypy --strict theory_verifier tests scripts
python3 scripts/check_declarative_rules.py --json
python3 -m unittest tests.test_declarative_verifier
lake build Proofs
lake build idt_v8_protocol_status
lake exe idt_v8_protocol_status -- --check-boundary
lake exe idt_v8_protocol_status -- --json
python scripts/build_ai_theory_graph.py --output dist/idt-v8-ai-theory-graph.json
```

This is the current Lean + IDT v8 migration-stop CI lane. It does not run the
legacy manifest verifier as proof authority and does not claim QM is proved.

## AI Theory Graph

The v8 AI theory graph is a compact index for agents, not proof authority. Lean
remains the proof source of truth, and the manifest is treated as residual
research input.

The graph is not stored in git and is not zipped. On a published GitHub Release,
CI attaches the raw JSON file `idt-v8-ai-theory-graph.json` as a release asset.
To generate the same file locally:

```bash
python scripts/build_ai_theory_graph.py --output dist/idt-v8-ai-theory-graph.json
```

For changes to the accepted theory surface or the IDT research-language/tooling
surface, publish a semantic-versioned GitHub Release after committing. The
release workflow is what produces the raw graph asset for that version. The tag
must follow the versioning rule in [PROTOLANGUAGE.md](PROTOLANGUAGE.md): use
`MAJOR` for incompatible baseline/proof-boundary changes, `MINOR` for compatible
new theory/language/tooling surface, and `PATCH` only for corrections or
hardening that preserve the accepted surface.

Agents should load this compact graph first, inspect node/edge topology, then
fetch exact source files by the recorded source path and hash only when more
context is needed. The graph is context and navigation metadata; it does not
upgrade claims and does not replace Lean artifacts.

For local graph inspection:

```bash
python scripts/query_ai_theory_graph.py summary
python scripts/query_ai_theory_graph.py validate --repo-root . --check-source-hashes
python scripts/query_ai_theory_graph.py show <node-id-or-alias>
python scripts/query_ai_theory_graph.py neighbors <node-id-or-alias> --depth 2
python scripts/query_ai_theory_graph.py sources <node-id-or-alias> --depth 1
```

## Experiment Node Telemetry

The v8 experiment telemetry suite is a Lean-sourced executable research aid.
Lean defines the accepted protocol registry and logical nodes; the Python runner
executes small deterministic fixtures and records which logical nodes were used,
stressed, blocked, or failed.

Run it locally with:

```bash
lake exe idt_v8_experiment_protocols -- --json
python scripts/run_v8_experiment_suite.py \
  --output dist/v8-experiment-node-stats.json \
  --report dist/v8-experiment-report.md
```

The JSON report uses schema `idt-v8-experiment-node-stats/1` and includes
experiment summaries, per-node statistics, telemetry rows, and source hashes.
Use it to see where finite fixtures place pressure on logical nodes such as
shared calibrated action scale, readout normalization, and Bell table
compatibility. This telemetry is certified executable evidence only; it is not
proof authority and cannot upgrade Born, Hilbert, Schrodinger dynamics, `hbar`,
or full QM to proved status.

The older QM status lane is archived at `archive/legacy-ci/qm-status.yml`. It
is retained as a compatibility/status recipe, not active proof-authority CI:

```bash
ruff check theory_verifier tests scripts
mypy --strict theory_verifier tests scripts
python3 -m theory_verifier --json theory_verifier_manifest.json
python3 scripts/check_declarative_rules.py --json
python3 scripts/check_proofs.py
python3 scripts/evaluate_born_direct_one_pass.py
python3 scripts/evaluate_born_readout_attempt.py
python3 scripts/evaluate_s2_born_proof_search.py
python3 scripts/evaluate_qm_direct_one_pass.py
python3 scripts/evaluate_cgsc_qm_one_pass_closure.py
python3 scripts/check_qm_scientific_status.py
python3 scripts/evaluate_qm_inevitability_route.py
python3 scripts/evaluate_qm_hard_wall_probe.py
python3 scripts/evaluate_qm_semantic_kernel_route.py
python3 scripts/evaluate_qm_semantic_content_scaffolds.py
python3 scripts/evaluate_born_wall_separation.py
python3 scripts/check_born_scientific_status.py
python3 scripts/evaluate_full_qm_proof_attempt.py
python3 -m unittest discover -s tests
lake build
```

The `QM Scientific Status` badge reports the current scientific proof boundary:
the finite standard-QM sector is conditionally closed, and the active
Born/Hilbert frontier is context-first universal endpoint data plus
carrier-frontier exhaustion. The `IDT v8 Lean CI` badge reports whether the
Lean + IDT v8 migration-stop workflow is passing. Neither badge means that
exact fundamental QM has been proved.

The underlying checks are:

```bash
python3 -m theory_verifier --json theory_verifier_manifest.json
python3 scripts/sync_formal_proof_ledger.py --check
lake env lean Proofs/IDTCore.lean
python3 -m unittest discover -s tests
```

Compile the QM universal-pattern bench:

```bash
python3 scripts/qm_bench.py --json
```

Optional development tools:

```bash
python3 -m pip install -r requirements-dev.txt
ruff check .
mypy --strict theory_verifier tests scripts
```

## Public Claim Boundary

IDT may be described as a candidate executable language for physical
interpretation and AI-assisted scientific reasoning.

It must not be presented as:

- a completed derivation of QM or GR;
- a numerical derivation of \(\hbar\), \(G_N\), or \(\alpha_{\mathrm{em}}\);
- an explanation of dark matter or dark energy;
- an experimentally confirmed replacement for established physics.
