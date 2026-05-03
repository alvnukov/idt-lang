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
  claims.

## Repository Layout

- `PROTOLANGUAGE.md` — canonical entry point and public positioning.
- `sections/` — modular theory body.
- `theory_verifier/` — executable manifest verifier.
- `theory_verifier_manifest_v6_0.json` — current machine-checkable manifest.
- `tests/` — verifier unit tests.
- `data/` — documented data anchors used by verifier-facing research notes.

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
