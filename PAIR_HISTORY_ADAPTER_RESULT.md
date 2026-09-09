# First shared native pair-history adapter

## Result and boundary

The archived signed-integer and Gaussian-integer realizations both satisfy the
same selected finite algebraic requirements at the default bounds. This does
not select the physical carrier. The generic pair-history lower law remains
unsupported: it does not itself supply a carrier, weight or operational map.

The adapter implements the original integer addition, multiplication and weight
from `Proofs/QMClosure/PairHistoryMeasureProbe.lean`. It binds by the full archived
specification hash, not by a suggestive name or historical claim. Source text is
not executed. Tests independently assert the correspondence of each source to
its own carrier; passing both models alone would not detect swapped bindings.

The six checks are empty weight, unit-amplitude weight, bounded nonnegativity,
seven-term Sorkin I3, product-weight factorization and a two-path interference
existence witness. Default integer boxes contain 3 scalar or 9 plane amplitudes;
I3 checks 27 or 729 triples respectively. Finite exhaustion cannot refute an
existence claim on the infinite carrier. All results retain their assumptions,
bounds and missing physical bridges. This is not a laboratory Sorkin test.

## A rejected bridge, not a rejected candidate

For histories `1,i`, the normalized real Gram projection is `diag(1/2,1/2)`.
It preserves every single-system real-coefficient weight. But for the diagonal
composite event, native Gaussian multiplication gives `W(1*1+i*i)/4 = 0`, while
the tensor of projected matrices gives `1/2`. Projection discarded imaginary
pair information needed at composition.

`Proofs/QMClosure/PairHistoryAdapterSafety.lean` proves this exact discrepancy
and the unit-weight capability distinction: the integer scalar has
`W(1+a)` in `{0,4}` when `W(a)=1`, whereas Gaussian `a=i` gives 2. These are
algebraic facts, not a derivation of physical preparability or continuous phases.
The Python adapter retains the native operations and never uses this projection.
No existing real-kernel candidate or its explicit tensor assumptions is changed.

## Controls and the remaining blind spot

| Supplied law | Independent witness or outcome | Meaning |
| --- | --- | --- |
| Scalar fourth power | I3(1,1,1) = 36 | Fails the selected pair-history law |
| Scalar absolute value | I3(-1,1,1) = 2 | Fails the selected pair-history law |
| Zero weight | W(1) = 0 | Fails the unit convention; missing interference witness remains inconclusive |
| Gaussian multiplication, weight a²+2b² | Product defect at i,i is -3 | Weight and multiplication are incompatible with the selected factorization law |
| Split multiplication, weight a²-b² | W(u) = -1 | Fails selected nonnegativity |
| Dual multiplication u²=0, weight a² | Survives; W(u)=0 for nonzero u | These gates do not distinguish hidden zero-weight directions |

All six controls are retained in `data/amplitude_algebra_controls.json` and the
candidate history. The first counterexample found by enumeration need not be
the explanatory witness in this table. Phase and zero-weight samples are
diagnostics only; neither is an automatic global exclusion rule.

## Reviewed historical transition

Only two of the original 300 candidates changed: `unsupported` became
`no_counterexample_within_bounds` for the two exact source realizations, with
new algebraic checks and scope. This is new adapter coverage, not confirmation
of either primitive base. The other 298 results were unchanged.

The two baseline pins were individually reviewed and updated with that reason.
The original capture index and unsupported observations are unchanged. Their
old/new full observation hashes are:

- Signed scalar: old `3ed6b4dfa2b92c1fa0fb1a65ee93df221d9fd84a2f0f1779ab97416bf1a3b69f`;
  new `9f317ddae8ab2df42546ef688360ce1ce851399869964b9f9daeb07b3f39f8fe`.
- Gaussian: old `7d74b571d44e96b023a09fcf08d98cf3805f746cd0c8560ff2ee109e8e92888a`;
  new `529e6bc04d2d97a5b8a7bceccb582a4ea4b08e88c8d91242fd8bd5f8e4c61d7a`.
- Six-control observation: `af05877b24a193d55695cd50f7f7da8456243c15dbc8a8841763af34968a921a`.

The archive now contains 306 candidate entries. Twenty-two of the 24 source
records still lack an adapter; physical prediction bridges remain open for all
24. No manifest proof status, empirical status or theory version is upgraded.

## Next research obligation

Develop an explicit operational preparation/readout/composition contract and
ask whether the scalar, Gaussian and degenerate carriers differ under it.
Do not add nondegeneracy or complex phase as a requirement merely to select
Gaussian amplitudes: justify each requirement and its physical scope first.
The U0 collection's 40 variants are not a shortcut to 40 physics predictions;
they still need quantitative adapters. The authoritative work and bridge-wall
ledger is `Proofs/MetaLang/V8CheckerResearchProgram.lean`.

## Verification of this milestone

The seven checker test modules passed 101 tests, including fresh replay of the
complete candidate history. Ruff and strict mypy passed for all seven checker
modules and the new test module. Both changed/new Lean targets built; the
declarative-rules check, graph validation and claim audit passed. Python language
server diagnostics were unavailable (pyright was not installed); they are not
reported as a successful check. These engineering checks do not close the
physical bridges listed above.
