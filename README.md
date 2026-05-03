# IDT Lang

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

These are successes of reconstruction discipline and executable claim control.
They are not claims that IDT has already derived all of QM, GR, or the constants
of nature.

## Repository Layout

- `ORIGIN.md` — project origin and motivation.
- `PUBLIC_CLAIM_SHEET.md` — public claim boundary and current auditable
  successes.
- `PROTOLANGUAGE.md` — canonical entry point and public positioning.
- `sections/` — modular theory body.
- `scripts/graph_query.py` — file-based research graph query and cautious edit
  helper for the verifier manifest.
- `theory_verifier/` — executable manifest verifier.
- `theory_verifier_manifest_v6_0.json` — current machine-checkable manifest.
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
python3 -m theory_verifier --json theory_verifier_manifest_v6_0.json
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
mypy --strict theory_verifier tests
```

## Public Claim Boundary

IDT may be described as a candidate executable language for physical
interpretation and AI-assisted scientific reasoning.

It must not be presented as:

- a completed derivation of QM or GR;
- a numerical derivation of \(\hbar\), \(G_N\), or \(\alpha_{\mathrm{em}}\);
- an explanation of dark matter or dark energy;
- an experimentally confirmed replacement for established physics.
