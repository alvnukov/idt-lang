# Destructive composition: a checked boundary, not a QM reconstruction

The source artifact is
[`DestructiveCompositionBoundary.lean`](../Proofs/QMClosure/DestructiveCompositionBoundary.lean),
namespace `IDT.QMClosure.DestructiveCompositionBoundary`. Its research ledger
distinguishes compiled artifacts, paper-only arguments awaiting formalization,
and open physical bridges. No manifest status is upgraded.

## Checked finite destructive-composition diagnostic

Reuse the rational pair-kernel calculus from `CoherentReferencePositivity.lean`:
an event weight is the sum of kernel entries over all pairs in the event, and
independent kernels compose by entrywise tensor multiplication. These event
weights are **not** an ordinary distribution of detector-outcome probabilities.

On two histories, let D have diagonal 1/6 and off-diagonal 1/3; let R have
diagonal 1 and off-diagonal −1/2. There is no normalization adjustment.

- `candidate_and_companion_normalized`: both total event weights equal 1.
- `candidate_event_nonnegative` and `companion_all_events_nonnegative`: all
  local events have nonnegative weights.
- `one_companion_all_events_nonnegative`: all 16 events of D ⊗ R have
  nonnegative weights.
- `two_companions_parity_weight_negative`: in (D ⊗ R) ⊗ R, the event
  {((d,a),b) : d = a xor b} has weight −1/2.
- `one_companion_test_does_not_suffice` packages the last two statements.

Thus one partial destructive-companion test does not establish compatibility
with repeated copies of that companion. D also passes arbitrarily many
self-copy tests, as established in the reused module. Neither fact selects
strong positivity by itself.

## Checked outer countermodel: cancellation and composition do not fix I3

For any finite rational amplitude vector a with sum a = 1, define

    μ_a(E) = (sum over i in E of a_i)^4,
    (a ⊗ b)_(i,j) = a_i b_j.

This is an entire closed family, not just an evaluation of n⁴:

- `quartic_event_nonnegative` and `quartic_normalized` prove nonnegativity and
  normalization.
- `tensor_amplitude_normalized` proves closure of normalized amplitudes under
  independent tensor composition.
- `quartic_product_events` proves multiplicativity on product events.
- `coarse_amplitude_normalized` and `quartic_coarse_event` prove closure under
  summing amplitudes over fibers and equality with the original event pullback.

For a = (1,1,1,−1,−1), `quartic_example_normalized` and
`quartic_example_cancellation` give total normalization and a nonempty
zero-weight event {0,3}. The singleton events {0}, {1}, {2} are pairwise
disjoint (`quartic_example_disjoint_events`), but their inclusion-exclusion
third-order term equals 36 (`quartic_example_third_order`).

Consequently, cancellation plus these tensor/coarse-graining closure demands
does not imply I3 = 0. The family is outside the quadratic pair-kernel ansatz;
it is not proposed as a viable physical model or a rejection of the full IDT
primitive base. Its event weights need not be bounded by 1 and are not
detector-outcome probabilities.

## Paper-only routes awaiting formalization

The following are recorded in Lean as `paperOnlyPendingFormalization`, not as
checked universal theorems:

1. Supply the exact rank-one seed C = t tᵀ, t = (1,1,−1). Its kth tensor power
   has (3^k+1)/2 positive and (3^k−1)/2 negative amplitudes. Correlated events
   can therefore generate integer reference coefficients v when
   3^k ≥ 2 max |v| + 1. With all such events admitted, this supplies a route
   from repeated-seed compatibility to real positive semidefiniteness.
2. Assume a Hermitian representation D = A+iB. For real vectors x,y and
   w = x⊗y−y⊗x, the square-composite form is

       wᵀ(D⊗D)w = 2[(xᵀAx)(yᵀAy) − (xᵀAy)^2 − (xᵀBy)^2].

   Real quadratic positivity of D and D⊗D would then imply complex positive
   semidefiniteness. This assumes, and does not derive, the complex carrier.
3. Replacing the exact seed by a generic imperfect negative-real-pair seed
   requires a parity-limit argument. The finite R calculation above does not
   prove this universal extension.

The supplied assumptions are pair-kernel representation, tensor multiplication,
unlimited independent copies, admission of all correlated events, and
availability of the destructive companion. They are not inferred physical
primitives. The exact-seed route requires that particular C to be available;
the generic route still needs a negative real pair. The origin of pair arity
and I3 = 0, the complex carrier, dynamics, detector probabilities, and physical
scale bridges remain open.

## Relation to existing work

[Dowker–Wilkes, arXiv:2011.06120v2, Theorem 4](https://arxiv.org/html/2011.06120v2)
classifies tensor-closed subsets of weakly positive systems: each lies within
the strongly positive class or within the entrywise-nonnegative class.
An available negative companion excludes the latter branch, giving containment
in the strongly positive class, **not equality with that whole class** without
further assumptions. The finite artifact does not formalize this external
classification, and no novelty claim is made.

Verification: `lake build Proofs.QMClosure.DestructiveCompositionBoundary`.
The module is also a default `Proofs` library root. This result does not prove
QM, derive Born readout, or upgrade any physical closure obligation.
