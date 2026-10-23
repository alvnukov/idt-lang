# History merge, substitution, and descent

## Result and scope

`Proofs/QMClosure/HistoryMergeDescent.lean` separates three routes that can
otherwise look like a derivation of additive context transformations:

| Route | Checked result | Remaining boundary |
| --- | --- | --- |
| Uniform substitution plus evaluation congruence | A unique represented transformation exists under explicit surjectivity; it is additive. Without surjectivity, additivity holds on reachable pairs. | The evaluation, coherent merge, substitution interpretation, and congruence are supplied. |
| Preservation of every equality between finite history sums | Equivalent to preserving zero and binary addition. | This is an exact characterization, not an independent derivation of additivity. |
| Equal/real-collinear refinement or preservation of state equivalence | Insufficient: the concrete transported quartic rotation passes these weaker requirements but fails arbitrary refinement. | A fixed comparison frame is not a coherent-history congruence. |

These are universal conditional mathematical theorems and concrete negative
controls, not a primitive-derived quantum dynamics result. No manifest status
is upgraded. QM, SM, and GR are not proved or experimentally confirmed here.

## 1. Uniform substitution is not quotient completeness

A history is a finite list of occurrences from one supplied coherent family.
Its evaluation is **defined** as the sum of supplied occurrence amplitudes.
Concatenation therefore evaluates additively. A fixed substitution sends each
occurrence to a finite target list and extends by `flatMap`; preservation of
concatenation is structural.

The independent descent condition is:

```text
eval(a, P) = eval(a, Q)
  implies eval(b, substitute(σ, P)) = eval(b, substitute(σ, Q)).
```

It says that the transformed value does not depend on which history represents
the original value. With explicit surjectivity of `eval(a, ·)`, this is
equivalent to existence of a unique total function `T` satisfying
`T(eval(a, P)) = eval(b, substitute(σ, P))`. The theorem uses ordinary classical
choice to select representatives. This adds no physical assumption beyond the
stated premises.

With the supplied additive evaluation and substitution definitions, the
equivariance equation implies additivity on pairs of reachable values.
Surjectivity extends that conclusion to all pairs in the carrier.
Neither all-vector reachability nor a physical continuum is inferred from
vague accessibility language. Unrestricted lists provide joint realizability
by construction; a physically restricted history family would additionally
need admissibility and closure of the relevant concatenations. There is no
global joint table for all incompatible contexts in this construction.

The three-label negative control uses amplitudes `(1, 1, -1)` and an involutive
relabeling fixing label `0` while swapping `1` and `2`. Each atomic squared
weight is preserved, and substitution preserves concatenation. Nevertheless,
the equal-valued singleton histories `[0]` and `[1]` transform to values `1`
and `-1`, so descent fails. The coherent event `[0, 2]` has squared weight `0`
before relabeling and `4` afterward: **whole-event weights are not preserved**.
This is a counterexample to the specified implication, not a model of all IDT
primitives or all operational constraints.

## 2. Arbitrary refinement is exactly additivity

For an occurrencewise map `f`, `HistDescends f` requires preservation of every
equality between finite sums. The checked equivalence is:

```text
HistDescends(f) iff f(0) = 0 and f(x + y) = f(x) + f(y) for all x, y.
```

The forward direction compares `[0]` with the empty list and `[x+y]` with
`[x,y]`; the reverse direction is list induction. Calling this unrestricted
refinement requirement a new physical explanation of additivity would conceal
that it already has exactly that mathematical strength.

## 3. Weaker consistency conditions do not suffice

The existing concrete family `quarticRotate` transports supplied real quadratic
rotations through `phi(x) = x |x|` and its inverse `psi`. Its homogeneity is now
checked for every real scalar, including negative scalars. Consequently it
respects binary refinements along any **real** line, including equal-piece splits.
It need not respect sums of noncollinear vectors.

The compiled negative control combines real-collinear refinement with failure
of `HistDescends` for the concrete coefficients `(3/5, 4/5)`. Existing quartic
readout weights distinguish the two pipelines by `2` versus `194/25`; these
numbers are readout weights, not vector outputs. Ordinary scalar history merge
still has the existing third-order residual `I3 = 36`, so this does not rescue
the quartic model as a QM gate hit. Transported merge restores the supplied
quadratic representation instead of deriving an independent physical merge.

For a supplied nonnegative weight `W`, with `W(v)=0` exactly at `v=0`, and a
supplied positive comparison-port weight `c`, define
`p(r,x) = W(x+r)/(W(x+r)+c)`. Equality for **every** reference `r` implies
`x=y`: choose `r=-x`. Thus every function preserves this state equivalence;
that property alone cannot force additivity. Conversely, equality of the
normalized readouts across the two merge/transformation pipelines for every
reference is equivalent to additivity. All-reference access, the fixed positive
port, the carrier, and this normalization are explicit premises. This is a
fixed comparison frame, not ordinary projective/ray equivalence, and not a
derivation of Born normalization or the full measurement set.

The concrete state-equivalence control instantiates these premises with
`W = planeQ4` and `c = 1`: the nonadditive quartic rotation still preserves
the resulting faithful state equivalence.

## False-rejection control: completeness must be established first

Descent is not a universal filter on any convenient representation. The new
module also checks the ordinary linear map `phaseFlip(a,b) = (a,-b)`: it is
real-homogeneous, additive, involutive, and preserves the sum of squares. Yet
the lossy scalar adapter `scalarTotal(a,b) = a+b` identifies `(1,0)` and `(0,1)`
at value `1`, while their post-action totals are `1` and `-1`. No scalar function
can factor this action through that adapter.

This failure rejects the **adapter/action pairing**, not the linear phase flip
or QM. The operation is mode-sensitive before merging; it is not a well-defined
operation on an already-merged scalar preparation. Quotient completeness may
be demanded only after establishing that the chosen equivalence identifies
complete preparations for the admitted continuation family. Equal current
readouts or equal single-port amplitudes do not establish that condition.

## Prior context and open bridges

Goyal, Knuth, and Skilling distinguish structural composition of measurement
sequences from composition of their representations: parallel coarsening and
series composition yield structural relations, while the pair postulate and
well-defined continuous representation operators are additional requirements
(§II.1–II.2, equations 6–9 and S1–S5). This is relevant prior context for the
same structural-versus-represented distinction, not evidence that those
requirements follow from IDT or a novelty claim for the mathematics here.
[Origin of Complex Quantum Amplitudes and Feynman's Rules](https://arxiv.org/html/0907.0909v3).

The local Lean `OpenBridge` ledger retains seven physical obligations: actual
admissible histories/concatenation; the amplitude carrier and additive
evaluation; contexts acting by uniform substitution; evaluation congruence;
preparation-equivalence completeness for admitted continuations;
surjective reachability/continuum; and access to all references plus a fixed
positive comparison port. The context vocabulary and `BoundPrimitiveGeneratedBase` do not
currently bind this whole history/merge realization. Concrete
`BoundPrimitiveGeneratedBase` inhabitants do exist (for example the rank-three
wall construction); their existence does not establish these physical bridges.

No Hilbert, Born, tensor-product, or physical-scale derivation is imported into
these claims. The mathematical ingredients are supplied additive algebra, real
numbers, classical choice for factorization, and the existing coordinate
transport example. A physically grounded realization and the neighboring
representation, dynamics, composites, and physical-scale closures remain open.
