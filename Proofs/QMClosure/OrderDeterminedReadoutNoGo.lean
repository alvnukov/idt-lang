import Mathlib.Tactic

namespace IDT
namespace QMClosure

/-!
# Order-determined constraints do not entail additivity

`B1PrimitiveBaseRankThreeWall` showed that the constraints accumulated along the
primitive-base chain are satisfied by three arbitrary points with non-empty,
non-total relations. Every field in that chain is a `CheckedProp`, a bare
`Type`, a distinctness of finitely many points, a non-emptiness or non-totality
of a relation, or one involution equation. None of them mentions addition on
the value scale.

This file asks what that costs, and answers it exactly.

Call a constraint on readouts *order-determined* when it cannot distinguish two
readouts that order their outcomes the same way. The theorem below exhibits two
non-negative normalized readouts on three alternatives that induce exactly the
same order, where one is additive over the split `{0,1} | 2` and the other is
not. Hence no order-determined constraint entails additivity -- not even with
normalization and non-negativity already assumed.

Additivity over disjoint alternatives is the `exclusivity_additivity`
obligation, and the Born readout needs it. So an order-determined primitive
cannot select the Born rule, however many such primitives are added.

Scope. This is a statement about a class of constraints, not about the
context-first programme, and it is not a claim that relational constraints are
useless: the `AtLeastThree` rank condition really did exclude two-element
carriers. It says that constraints of this class cannot reach additivity, so
reaching it requires a primitive carrying arithmetic on the value scale. It
does not say which primitive would suffice.
-/

/-- A readout of three alternatives: non-negative and normalized. -/
structure NormalizedReadout where
  first : ℚ
  second : ℚ
  third : ℚ
  firstNonneg : 0 ≤ first
  secondNonneg : 0 ≤ second
  thirdNonneg : 0 ≤ third
  normalized : first + second + third = 1

/--
Two readouts order their three alternatives identically. The three reflexive
comparisons are omitted because they hold for every readout.
-/
def SameOrder (left right : NormalizedReadout) : Prop :=
  (left.first ≤ left.second ↔ right.first ≤ right.second)
    ∧ (left.second ≤ left.first ↔ right.second ≤ right.first)
    ∧ (left.first ≤ left.third ↔ right.first ≤ right.third)
    ∧ (left.third ≤ left.first ↔ right.third ≤ right.first)
    ∧ (left.second ≤ left.third ↔ right.second ≤ right.third)
    ∧ (left.third ≤ left.second ↔ right.third ≤ right.second)

/--
A constraint that cannot tell apart two readouts inducing the same order. Any
constraint that does not mention the readout at all is of this kind; see
`readout_blind_is_order_determined`.
-/
def OrderDetermined (constraint : NormalizedReadout → Prop) : Prop :=
  ∀ left right : NormalizedReadout,
    SameOrder left right → (constraint left ↔ constraint right)

/-- Additivity over the split `{first, second} | third`. -/
def AdditiveOverSplit (readout : NormalizedReadout) : Prop :=
  readout.third = readout.first + readout.second

/-- Weights `1/6 < 2/6 < 3/6`. Normalized, and additive over the split. -/
def additiveReadout : NormalizedReadout where
  first := 1 / 6
  second := 2 / 6
  third := 3 / 6
  firstNonneg := by norm_num
  secondNonneg := by norm_num
  thirdNonneg := by norm_num
  normalized := by norm_num

/-- Weights `1/10 < 3/10 < 6/10`. Normalized, same order, not additive. -/
def nonAdditiveReadout : NormalizedReadout where
  first := 1 / 10
  second := 3 / 10
  third := 6 / 10
  firstNonneg := by norm_num
  secondNonneg := by norm_num
  thirdNonneg := by norm_num
  normalized := by norm_num

theorem additive_readout_is_additive : AdditiveOverSplit additiveReadout := by
  unfold AdditiveOverSplit additiveReadout
  norm_num

theorem non_additive_readout_is_not_additive :
    ¬ AdditiveOverSplit nonAdditiveReadout := by
  unfold AdditiveOverSplit nonAdditiveReadout
  norm_num

/-- The two readouts order their three alternatives identically. -/
theorem additive_and_non_additive_readouts_share_order :
    SameOrder additiveReadout nonAdditiveReadout := by
  unfold SameOrder additiveReadout nonAdditiveReadout
  norm_num

/--
The result. No order-determined constraint admitting the additive readout can
entail additivity, because it must equally admit the non-additive one.
-/
theorem order_determined_constraints_do_not_entail_additivity
    (constraint : NormalizedReadout → Prop)
    (orderOnly : OrderDetermined constraint)
    (admitsAdditive : constraint additiveReadout) :
    ¬ (∀ readout : NormalizedReadout,
        constraint readout → AdditiveOverSplit readout) := by
  intro entailsAdditivity
  have admitsNonAdditive : constraint nonAdditiveReadout :=
    (orderOnly additiveReadout nonAdditiveReadout
      additive_and_non_additive_readouts_share_order).mp admitsAdditive
  exact non_additive_readout_is_not_additive
    (entailsAdditivity nonAdditiveReadout admitsNonAdditive)

/-- A constraint that never inspects the readout at all. -/
def ReadoutBlind (constraint : NormalizedReadout → Prop) : Prop :=
  ∀ left right : NormalizedReadout, constraint left ↔ constraint right

/--
The constraints accumulated in the primitive-base chain are of this kind: they
speak about carriers and relations between them, never about weights. They are
a special case of order-determined, so the no-go covers them a fortiori.
-/
theorem readout_blind_is_order_determined
    (constraint : NormalizedReadout → Prop)
    (blind : ReadoutBlind constraint) :
    OrderDetermined constraint :=
  fun left right _ => blind left right

/-- Corollary for the constraint style the chain actually uses. -/
theorem readout_blind_constraints_do_not_entail_additivity
    (constraint : NormalizedReadout → Prop)
    (blind : ReadoutBlind constraint)
    (admitsAdditive : constraint additiveReadout) :
    ¬ (∀ readout : NormalizedReadout,
        constraint readout → AdditiveOverSplit readout) :=
  order_determined_constraints_do_not_entail_additivity constraint
    (readout_blind_is_order_determined constraint blind) admitsAdditive

inductive OrderDeterminedNoGoFinding where
  | sameOrderReadoutsDisagreeOnAdditivity
  | normalizationAndNonnegativityDoNotRestoreAdditivity
  | readoutBlindConstraintsAreOrderDetermined
  | additivityRequiresValueScaleArithmetic
  deriving DecidableEq, Repr

def orderDeterminedNoGoFindings : List OrderDeterminedNoGoFinding :=
  [ .sameOrderReadoutsDisagreeOnAdditivity,
    .normalizationAndNonnegativityDoNotRestoreAdditivity,
    .readoutBlindConstraintsAreOrderDetermined,
    .additivityRequiresValueScaleArithmetic ]

theorem order_determined_no_go_records_four_findings :
    orderDeterminedNoGoFindings.length = 4 := by
  rfl

inductive OrderDeterminedNoGoOpenObligation where
  | identifyMinimalValueScaleArithmeticPrimitive
  | testWhetherCoarseGrainingClosureSufficesForAdditivity
  | extendNoGoBeyondThreeAlternatives
  | separateAdditivityFromQuadraticReadout
  deriving DecidableEq, Repr

def orderDeterminedNoGoOpenObligations :
    List OrderDeterminedNoGoOpenObligation :=
  [ .identifyMinimalValueScaleArithmeticPrimitive,
    .testWhetherCoarseGrainingClosureSufficesForAdditivity,
    .extendNoGoBeyondThreeAlternatives,
    .separateAdditivityFromQuadraticReadout ]

theorem order_determined_no_go_keeps_four_open_obligations :
    orderDeterminedNoGoOpenObligations.length = 4 := by
  rfl

def orderDeterminedNoGoClaimBoundary : String :=
  "Finite no-go over three alternatives: order-determined constraints, including every readout-blind one, do not entail additivity over a split even with normalization and non-negativity assumed. It does not derive the Born rule, does not refute the context-first programme, and does not identify which arithmetic primitive would suffice."

end QMClosure
end IDT
