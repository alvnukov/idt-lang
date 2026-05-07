# Theory Verifier Package Boundary

The target proof architecture is Lean + IDT v8.

This Python package is retained only for compatibility and IDT v8 input
checking during migration:

- `declarative.py` is the active IDT v8 declarative-rule input checker.
- `core.py`, `__main__.py`, and legacy manifest execution remain compatibility
  infrastructure, not proof authority.
- `qm_bench.py` is a compatibility/demo surface, not a proof source of truth.

Only Lean artifacts that build under `lake build` may assign machine-checked
formal proof status. Python checks may validate structured inputs or legacy
diagnostics, but they must not upgrade physical or QM claims to `formal_proof`.
