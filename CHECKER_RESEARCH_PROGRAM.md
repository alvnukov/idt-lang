# A versioned scientific checker and parallel primitive research

The target is an executable, auditable description of **specified known
constraints**, not a permanently complete world model. A search-ready release
is a scoped engineering milestone. It neither proves a candidate nor ends
checker development. The authoritative work/acceptance ledger is
`Proofs/MetaLang/V8CheckerResearchProgram.lean`.

## Existing primitives are retained

`data/existing_primitive_inventory.json` registers **14 historical base
candidates and one lower-law candidate**, plus nine supporting records:
the legacy scaffold, four semantic contracts, two pair-law realizations, one
closed-selector route and one collection of ten U0 law families with four
variants each. This is a source-grounded inventory, not an exhaustive theorem
about every idea ever mentioned in the repository.

The canonical context-first vocabulary contains five declarations: admissible
context cover, local outcome-event presheaf, inheritance transitions,
facticization witness relation and stable distinguishability. Other historical
bases remain distinct: four-element B0, B0 with F/Q/action scale, B1 variants,
closed-distinction/loss-accounting B2 variants, B3, ZB1, ZB2 and U0. Their
inconsistencies and scoped failures are preserved, not reconciled by relabeling.

Every registered record is now in `data/candidate_history/`, with exact source
text, line spans, whole-file and excerpt hashes, historical qualifications and
missing prediction bridges. `data/existing_primitive_registration.json` records
the original archive addresses. Source capture validates the current file hash;
historical replay uses the retained text, so later editing or removal of the
original source does not erase the proposal. Source text is never executed by
this archival adapter.

These records use `family: source_theory`. The checker returns `unsupported`,
zero physical cases checked, `adapter_status: missing`, and no proof/empirical
upgrade. A historical claim in source text cannot change that result. An
unchanged-history result means only no regression; the report separately lists
all missing source adapters and per-status evaluation counts. Old toy routines
have not been silently translated into modern QM/SM tests.

```sh
python3 scripts/archive_existing_primitives.py
python3 scripts/check_candidate_history.py
```

## Two tracks with independent acceptance criteria

| Track | Work | Required handoff |
| --- | --- | --- |
| Checker | Version requirements, add adapters/data comparisons, check independent controls, replay all history | Exact capability and validity domain; unimplemented areas remain visible |
| Primitive research | Select retained candidates, state imports, attempt prediction bridges, run discriminating probes | Reproducible evidence or a precise missing bridge, plus a checker-gap report |

The tracks can run concurrently on independent artifacts. Shared-code edits
must be coordinated, and Lean builds remain sequential. Checker changes cannot
be justified solely because they help a favored candidate; candidate acceptance
cannot be justified by a successful checker release. No status upgrade follows
from scheduling, preservation, a fixture hit, or a historical label.

Safe acceleration already used here: independent read-only inventory and
coverage audits alongside implementation; compact exact-arithmetic probes;
lossless evidence compression. Proposed next acceleration: prioritize adapter
work by how many **distinct preserved candidates** it discriminates. Keep the
complete regression run; priority must not remove failed or unsupported cases.

## What the world-constraint code does and does not contain

`V8PrimitiveEmpiricalConstraintLedger.lean` enumerates 46 evidence families in
seven sectors. Its current candidate-specific coverage is nine partially
executable QM families; the remaining 37 are unassessed. Imported QM/SM benchmark
engines are not derivations of those sectors from the archived primitive bases.
Source pointers are not versioned numerical datasets, and synthetic scale
fixtures are not laboratory measurements.

Inventory validation now requires all 46 canonical requirements exactly once,
with unchanged ID, sector, evidence tier and source family, independent of
order. Empty, incomplete, duplicated or altered inventories become `unassessed`
before either confirmation or rejection. Lean regression theorems exercise
these cases. The existing `confirmedLowerBase` label still classifies a table
of **caller-supplied status labels**; it is not a checked proof or an empirical
authority. Linking those labels to verified evidence remains explicitly open.

Before a real data comparison can count as implemented, it needs source/version
and hashes, units, uncertainties and correlations, a candidate-to-observable
map, validity/approximation error, and a comparison rule fixed before inspecting
the result. Missing data/adapter, unsupported domain, exhausted budget and
numerical failure must not become scientific rejection or acceptance.

## Research feedback already captured

`sm_neutral_singlet_scope_probe` adds three neutral Weyl singlets to the supplied
minimal SM spectrum. All six anomaly checks and the neutral-Higgs check pass
their finite requirements; only `sm_minimal_multiplet_content` finds a mismatch.
The complete result is retained in history and in a regression control.

This says the candidate is **not the exact imported minimal-content target**.
It does not exclude every such extension, explain neutrino masses, select a
lower primitive base or constitute an experiment. The distinction is a concrete
test of how candidate research should improve checker scope discipline.

The next scientific bottleneck is the explicit prediction bridge from one of
the retained primitive specifications, especially quantitative readout and
composition. The next checker bottleneck is evidence-linked, versioned data
coverage. Neither is recorded as completed.
