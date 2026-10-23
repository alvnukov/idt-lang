# Native integer Bell bridge: conditional result and exact wall

The retained signed-scalar and Gaussian pair-history realizations both support
the same supplied finite Bell protocol with exact CHSH value `14/5` and uniform
setting game-win probability `17/20`. Integer amplitudes alone therefore do not
force Bell-local correlations **once this normalized-weight operational bridge is
supplied**. This is neither an IDT-derived physical prediction nor experimental
evidence, a new physics discovery, or a derivation of QM.

## What is supplied and what is computed

`theory_experiments/native_bell_bridge.py` binds only the two reviewed full source
specifications through the existing `resolve_source_algebra` adapter. Source ids,
filenames, and historical labels do not establish the binding. Explicit supplied
algebras are also accepted. Unknown sources/bridges, nonquadratic or negative-eta
weights, scalar-carrier violations, and operations outside this bridge are
`unsupported`, not counterexamples to the primitive base. Malformed schemas are
input errors. A zero-total preparation is an undefined readout (`inconclusive`),
never a zero-denominator probability.

The preparation is the 2-by-2 amplitude table `C = I`, with each integer embedded
as `(integer, 0)` in its original native carrier. The supplied setting matrices are

```text
A0 = [[1, 0], [0, 1]]       A1 = [[1, 1], [1, -1]]
B0 = [[2, 1], [-1, 2]]      B1 = [[2, -1], [1, 2]]
```

The program computes `D = A C B^T`, native weights, and
`p(i,j|x,y) = Fraction(weight(D[i,j]), sum_of_context_weights)` through the
bound model's addition, multiplication, and weight methods. There is no
noninteger amplitude extension and no hardcoded QM probability table.

| Context `(x,y)` | Total native weight | Correlation |
| --- | ---: | ---: |
| `(0,0)` | 10 | 3/5 |
| `(0,1)` | 10 | 3/5 |
| `(1,0)` | 20 | 4/5 |
| `(1,1)` | 20 | -4/5 |

All one-party marginals are `(1/2, 1/2)`. With outcomes labelled by row/column
parity, `S = E00 + E01 + E10 - E11 = 14/5`, and the descriptive game-win average
is `17/20`. An exact no-signalling diagnostic records the marginal differences
across these four contexts; it is not a physical-admissibility or rejection gate.
The matrices and preparation were chosen without dataset fitting;
there is no Hensen comparison, p-value, observational likelihood, or data-based
selection in this family.

The same native preparation with all setting matrices equal to `I` gives `S=2`
and game-win probability `3/4`. Both protocols complete the execution check;
neither is a candidate rejection or ranking. Different supplied protocols do not
by themselves prove underdetermination of a fixed physical experiment. The exact
wall is the missing **source-derived map from the same symbolic preparation and
settings to these operations**, including physical preparability and readout.

The composite table, local action, outcome interpretation, normalized probability
readout, settings, and preparability are supplied, not derived Born/tensor/QM
structure. `empirical_status` remains `not_tested` and `proof_status` remains
`not_attempted` in the pipeline report.
The evaluator itself does not run Lean (`proof_check = not_run_by_this_evaluator`).

## Scale is not a global quotient

Every admitted setting obeys `M^T M = s I` for an exact positive integer `s`.
The report separates exact norm preservation (`s=1`), scaled norm preservation,
integer determinant, and integer-lattice inverse existence. In particular,
`A1^2=2I` and `B0 B1=5I` supply readout-projective reversibility only: they are
not integer-lattice bijections or established physical reversible dynamics.

Multiplying a whole preparation or an admitted matrix by a common nonzero integer
changes raw weights while preserving this direct normalized readout. This holds
for homogeneous continuations, not for every allowed future reference operation.
The executable countercontrol uses **two-outcome vectors of native amplitudes**:

```text
v  = [(1,0), (0,0)]       2v = [(2,0), (0,0)]
r  = [(0,0), (1,0)]
direct:       (1,0) for both v and 2v
after +r:     (1/2,1/2) versus (4/5,1/5)
```

Here the displayed direct/continued pairs are probabilities; `(1,0)` and `(0,1)`
in the shorthand mode-vector argument are not single Gaussian amplitudes. The
fixed reference breaks the common-scale equivalence. Existing raw-weight
semantics and native-operation contracts are unchanged; no global quotient or
retrofit of `native_operations` or `universe_bench` is asserted.

## Artifacts, controls, and reproduction

`Proofs/QMClosure/NativeBellScaledBridge.lean` provides separate mathematical
artifacts for this supplied structure and its scope. It does not formally verify
the Python implementation, derive the operational bridge, or certify physical
realizability. The typed task/result record is in
`Proofs/MetaLang/V8CheckerResearchProgram.lean`. No manifest status, public claim,
or theory version is upgraded.

`data/native_bell_bridge_controls.json` retains exactly eight structured inputs:
scalar/Gaussian witnesses, scalar/Gaussian all-identity controls, doubled Gaussian
preparation, zero preparation, a non-scaled-isometric operation `diag(1,2)`, and
the unbound `context_first_b0_five` source. Independent integer/Fraction tests
check the arithmetic and supplied-versus-derived distinctions.

After the source tree is frozen and checked, the existing command records the
whole batch using the standard cache/history machinery:

```bash
python3 scripts/screen_hypotheses.py \
  --batch-file data/native_bell_bridge_controls.json \
  --max-cases 4 --fresh --json
```

For a disposable reproduction, add explicit `--history-dir` and `--cache-dir`
paths outside the tracked history. The mixed control batch exits `3` because
unsupported/inconclusive controls are deliberately retained. `max_cases < 4`
executes zero contexts and performs no native readout; the other limit fields are
unused. `no_counterexample_within_bounds` means only that all four supplied
contexts executed, for both `S=2` and `S=14/5`.

Prior supplied-physics benchmarks already knew scaled-Hadamard/Bell arithmetic.
The new value is exact binding to retained native integer realizations, the
machine-checkable scale-scope distinction, and durable scoped reporting—not the
discovery of Bell violation or a new physical law. Historical observations and
pins are preserved rather than rewritten to fit the new adapter.
