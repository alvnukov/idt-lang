# Versioning Policy

Canonical entry point:

`PROTOLANGUAGE.md`

Canonical theory body:

`sections/`

Rules:

1. New theory versions are git commits, not new versioned Markdown files.
2. Every accepted version must have an annotated git tag.
3. Tag format: `vMAJOR.MINOR.PATCH`.
4. The first canonical tag is `v5.1.0`.
5. Since `v5.5.0`, theory content is modularized under `sections/`.
6. This public snapshot starts from the canonical modular source and does not include legacy full-copy archives.
7. Before tagging, every new object/formula/readout layer must state its known-experiment gate.
8. If the gate is missing, the object is `speculative_scaffold` and must not be presented as accepted theory.

Recommended release flow:

```bash
git status --short
git add PROTOLANGUAGE.md VERSIONING.md sections/ theory_verifier/ tests/ *.json *.yaml *.md *.py data/
git commit -m "Advance protolanguage to vX.Y.Z"
git tag -a vX.Y.Z -m "Inherited Distinguishability Protolanguage vX.Y.Z"
```

Do not create full-copy files named like `*_vX_Y.md` for normal theory evolution.
