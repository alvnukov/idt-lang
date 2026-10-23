# Continuation sufficiency and the boundary of a finite certificate

## Result and scope

`Proofs/QMClosure/ContinuationSufficiency.lean` supplies an exact mathematical
criterion for comparing preparations under a **supplied** deterministic model.
An output-compatible relation closed under every supplied action guarantees
equal readouts after every finite action word. The proof is induction on words;
it requires neither a finite state space nor an equivalence relation.

This is a conditional mathematical result, not a new physical primitive or a
derivation of quantum mechanics. Classical finite machines satisfy the same
criterion. No QM, SM, GR, measurement, or physical-scale status is upgraded.

## 1. Three different requirements

Supply states `S`, actions `A`, a total deterministic transition
`step : A → S → S`, a readout `readout : S → O`, and an adapter `q : S → Q`.
`run(step, s, word)` applies the actions in list order. Every word in `A*` is
legal here, including the empty word. A restricted physical operation grammar
is not represented by this assumption.

The module distinguishes:

| Requirement | Meaning |
| --- | --- |
| `BehaviorEquivalent step readout x y` | Every finite continuation gives equal final readouts. |
| `PredictivelySufficient step readout q` | Equal adapter values imply behavior equivalence. |
| `UpdateSufficient step q` | Equal adapter values remain equal after each action. |

Predictive sufficiency concerns observable predictions. Update sufficiency
concerns whether the adapter itself supports an autonomous deterministic update.
They are not interchangeable. Output compatibility plus update sufficiency is
a sufficient condition for predictive sufficiency, not a necessary one.

For an arbitrary relation `R`, output compatibility means
`R(x,y) → readout(x)=readout(y)`. Successor closure means
`R(x,y) → R(step(a,x),step(a,y))` for every action `a`. The theorem
`relation_sound_for_all_words` establishes the all-word conclusion.

Behavior equivalence is itself output-compatible, successor-closed, and an
equivalence relation. `behavior_is_greatest_compatible_closed_relation` states
that every output-compatible successor-closed relation is included in it.
“Greatest” refers to relation inclusion, not a largest physical state space.

`behavior_coordinate_transport_iff` also checks invariance under a supplied
bijection of state coordinates, transporting both transitions and readout.
That bijection is an input. The result does not select linear coordinates,
additive operations, a Hilbert space, or a preferred physical representation.

## 2. Exact controls

### Predictive sufficiency need not permit adapter updates

The four states `a,b,c,d` have readouts `0,0,1,1` and adapter values `0,0,1,2`.
The single action sends `a→c`, `b→d`, and fixes `c,d`. The only distinct pair
merged by the adapter is `a,b`: they agree now and have readout `1` after every
nonempty continuation. Thus the adapter is predictively sufficient for **all**
words, not just a sampled horizon. Its two successors have different adapter
values, so update sufficiency fails.

Lean checks `split_q_predictively_sufficient` and
`split_q_not_update_sufficient`. The first uses the general all-word theorem;
it is not a bounded-word enumeration.

### A lossy adapter can hide a reversible observable difference

The closed three-state fixture has coordinate pairs `(2,0)`, `(1,1)`, `(1,-1)`.
The action flips the second coordinate: it fixes the first state and swaps the
last two. The adapter is `q(x,y)=x+y`. The supplied rational readout is
`q²/(q²+1)`; this formula is not derived as a Born rule.

The first two states both have adapter value `2` and initial readout `4/5`.
After the action their readouts are respectively `4/5` and `0`. Lean checks
the involution, the coordinate interpretation, these exact values, and failure
of predictive sufficiency. This rejects the lossy adapter/action pairing,
not the phase flip. It makes the false-rejection boundary from
[section 180](180-history-merge-descent-boundary.md) operationally explicit.

### One-step agreement is not continuation completeness

The reversible four-state cycle `0→1→2→3→0` has output `1` only at state `3`.
States `0,1` agree on the empty word and after one step, but differ after two
steps. Lean checks bijectivity and this concrete delayed witness. The Python
tests additionally exercise cycles of size `n+3` with longer delays; the Lean
module does **not** claim an arbitrary-delay family theorem.

## 3. Executable certificate versus kernel-checked theorem

Run the finite demonstration with:

```bash
python3 scripts/check_continuation_sufficiency.py --demo
```

The finite checker accepts the strict model schema `idt-continuation-model/1`:
`transitions` contains one target-state row per action, `readouts` one vector
of exact rational strings per state, and `adapter` one integer label per state.
Limits are 1–64 states, 0–16 actions, and readout width 1–16; adapter labels are
signed 32-bit nominal labels. A zero-action model admits only the empty word.
Readout strings are integers or fractions with a signed numerator of at most
12 digits and a positive denominator of at most 12 digits; floats are rejected.
Rational vectors are mathematical output labels, not automatically probability
distributions. Empirical uncertainty, tolerances, and fitting are unsupported.

Use `--model-file PATH` for a model and optionally `--certificate-file PATH`
to verify an existing certificate against that expected model. Certificate
schema `idt-continuation-certificate/1` has either kind `stable_relation` with
`pairs`, or kind `distinguishing_word` with `origin` and `word`. Its digest
binds the full normalized model, not merely an adapter or a favorable sample.
Each input file is limited to 128 KiB. For `N` states, supported certificate
words have length at most `N²`; this is a checker bound, not a bound on `A*`.

A successful stable-relation certificate must include every adapter-equal
pair, preserve current readouts, and be closed under every action. Those finite
checks give an all-word guarantee for exactly that total deterministic model.
A distinguishing-word certificate provides a concrete observable failure.
Verification uses the expected model independently of certificate assertions.
Certificate non-acceptance can mean invalid data or a certificate outside these
supported limits; it is not a mathematical or physical candidate rejection.

The generic induction theorem and the three Lean controls are kernel-checked.
Python verifies concrete certificates independently; its serialized models and
certificates are **not** reified into Lean. The generic theorem therefore does
not itself kernel-check a Python-produced certificate. Neither layer establishes
that a finite model exhausts physically possible preparations or operations.

## 4. Remaining bridges and prior context

The local Lean `OpenBridge` ledger names the outstanding obligations: physical
state/model adequacy; the actual action alphabet and full-word legality; the
exact readout/measurement bridge; stochastic instruments and adaptive protocols;
accepted-primitive binding and quantum selection; and Python-certificate kernel
reification. `open_bridge_list_length` checks only the list's six-entry shape.

This operational behavior relation does not fill the accepted
`stableDistinguishabilityRelation` or kernel-offdiagonal requirements by a name
change. A concrete `BoundPrimitiveGeneratedBase` inhabitant already exists
elsewhere; existence of that inhabitant does not supply these semantic bridges.

Goyal, Knuth, and Skilling explicitly require pair-valued representations and
well-defined continuous representation operators in §II.2, equations 8–9 of
[Origin of Complex Quantum Amplitudes and Feynman's Rules](https://arxiv.org/html/0907.0909v3).
Those requirements are not derived from IDT here. This is relevant prior
context, not a novelty claim for the continuation mathematics.

A useful next bridge is to bind a specific candidate's actual finite closed
preparation/action model and exact readouts, then audit the physical adequacy
of that binding. It is not to declare this general machine criterion a new
primitive or to infer quantum selection from a passing classical certificate.
