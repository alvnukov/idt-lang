import Proofs.QMClosure.OperationalContextQuotient
import Proofs.QMClosure.RawNetworkMedialWall

/-!
# Observational probability selection for actual raw native words

The input operation satisfies the observed laws in `ObservedData`, together
with observed first-output diagonal transparency. No exact raw square-swap,
mediality, or transparency equation is added. Native circuit words are evaluated
using the original operation on the original raw carrier.

`Law` supplies six probability conditions at all finite widths. Its prepared
equivalence condition is explicitly stronger than literal raw-array equality:
pointwise equivalence in every stated one-hole observation context must preserve
the probability field. This probability-consistency premise is not derived from
the literal raw contract.

Passing to observational classes preserves the actual circuit evaluator. On
that quotient, transparency identifies the original operation with its canonical
normalization. The existing raw selection theorem then applies to the identical
supplied probability field. Selection and uniqueness do not use a law-existence
witness or a positive-reference premise.

A separate construction uses the normalized supplied weight when the reference
weight is positive. An observationally zero reference contradicts the law's
observational prepared consistency, normalization, permutation, and vacuum
conditions already on one and two wires, without any gate dynamics or
transparency premise. A null reference is observationally zero, so existence
for this stronger observational contract is
equivalent to positive reference weight without transparency. This is not a
positivity necessity claim for the older literal raw law. No physical
availability, outcome actualization, primitive upgrade, or full QM closure is
asserted.
-/

namespace IDT.QMClosure.ObservedRawProbabilitySelection

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open OperationalContextQuotient RawOperationalHilbert
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open scoped BigOperators

variable {V : Type*}

/-- Only the first output needs a transparency premise. Quotient square-swap
supplies the corresponding statement for the second output. -/
def ObservedTransparent (d : ObservedData V) : Prop :=
  ∀ x, ObservationalEq d.operation d.weight (d.operation (x, x)).1 x

/-- The six all-width probability conditions on actual raw preparations.
Prepared equivalence is observational, rather than literal equality. -/
structure Law (d : ObservedData V) (v : V) where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Native ι → ι → ℝ
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) i,
    0 ≤ prob s c i
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι),
    ∑ i, prob s c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c e : Native ι),
    (∀ i, ObservationalEq d.operation d.weight
      (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c i)
      (RawNetworkMedialWall.prepared d.operation d.chosenZero v s e i)) →
    prob s c = prob s e
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (e : Equiv.Perm ι) i,
    prob s (.seq c (.permute e)) i = prob s c (e i)
  spectator_pair : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i j k : ι) (hij : i ≠ j),
    k ≠ i → k ≠ j → prob s (.seq c (.pair i j hij)) k = prob s c k
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Native ι) i,
    prob (.inl s) (padCircuit κ c) (.inl i) = prob s c i

variable {d : ObservedData V} {v : V}

/-- Forget the explicit observational strengthening without changing `prob`. -/
def Law.toRawSemanticsLaw (L : Law d v) :
    RawNetworkMedialWall.RawSemanticsLaw d.operation d.chosenZero v where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h := by
    apply L.prepared_eq s c e
    intro i context
    rw [congrFun h i]
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

/-- Observed first-output transparency becomes exact quotient transparency. -/
theorem quotient_transparent (d : ObservedData V) (transparent : ObservedTransparent d)
    (x : ObservedData.Space d) : d.quotientOperation (x, x) = (x, x) := by
  have hfirst : (d.quotientOperation (x, x)).1 = x := by
    induction x using Quotient.inductionOn with
    | _ x => exact Quotient.sound (transparent x)
  calc
    d.quotientOperation (x, x) =
        (MedialSwapRoot.firstChannel d.quotientOperation x x,
          MedialSwapRoot.firstChannel d.quotientOperation x x) :=
      MedialSwapRoot.raw_operation_eq_symmetric d.quotientOperation d.quotient_square (x, x)
    _ = (x, x) := Prod.ext hfirst hfirst

/-- The normalized quotient gate is its original descended gate. -/
theorem quotient_normalizedOperation_eq (d : ObservedData V)
    (transparent : ObservedTransparent d)
    (p : Data.Carrier d.quotientData × Data.Carrier d.quotientData) :
    d.quotientData.normalizedOperation p = d.quotientOperation p := by
  change (WeightFreeRawProbability.RawOperationalData.ofWeighted d.quotientData).normalizedOperation p =
    (WeightFreeRawProbability.RawOperationalData.ofWeighted d.quotientData).operation p
  exact congrFun (WeightFreeRawProbability.normalizedOperation_eq_original
    (WeightFreeRawProbability.RawOperationalData.ofWeighted d.quotientData)
    (quotient_transparent d transparent)) p

/-- Evaluating the actual raw gate commutes with passage to observational classes. -/
theorem evalRaw_class (d : ObservedData V) {ι : Type} [DecidableEq ι]
    (c : Native ι) (x : ι → V) :
    WeightFreeRawProbability.evalRaw d.quotientOperation c (fun i => d.classOf (x i)) =
      fun i => d.classOf (WeightFreeRawProbability.evalRaw d.operation c x i) := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij =>
    funext k
    by_cases hki : k = i
    · simp [WeightFreeRawProbability.evalRaw, hki]
    · by_cases hkj : k = j
      · simp [WeightFreeRawProbability.evalRaw, hkj, hij.symm]
      · simp [WeightFreeRawProbability.evalRaw, hki, hkj]
  | permute e => rfl
  | seq c e hc he =>
    simp only [WeightFreeRawProbability.evalRaw, hc, he]

/-- The existing normalized raw adapter denotes classes of the original arrays. -/
theorem rawPrepared_eq_class (d : ObservedData V) (transparent : ObservedTransparent d)
    (v : V) {ι : Type} [DecidableEq ι] (s : ι) (c : Native ι) :
    RawNativeProbabilitySelection.rawPrepared d.quotientData (d.classOf v) s c =
      fun i => d.classOf (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c i) := by
  unfold RawNativeProbabilitySelection.rawPrepared
  rw [← WeightFreeRawProbability.evalRaw_eq_lift]
  have hoperation : (fun p => d.quotientData.normalizedOperation p) = d.quotientOperation :=
    funext (quotient_normalizedOperation_eq d transparent)
  rw [hoperation]
  have hsource : single (V := Data.Carrier d.quotientData) s (d.classOf v) =
      fun i => d.classOf (RawNetworkMedialWall.rawSource d.chosenZero v s i) := by
    funext i
    by_cases hi : i = s <;>
      simp [single, RawNetworkMedialWall.rawSource, hi, Data.carrier_zero,
        ObservedData.quotientData]
  rw [hsource]
  exact evalRaw_class d c (RawNetworkMedialWall.rawSource d.chosenZero v s)

/-- Transport the same supplied probability field, without selecting a witness. -/
def Law.toQuotientLaw (L : Law d v) (transparent : ObservedTransparent d) :
    RawNativeProbabilitySelection.RawLaw d.quotientData (d.classOf v) where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h := by
    apply L.prepared_eq s c e
    intro i
    have hi :
        d.classOf (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c i) =
          d.classOf (RawNetworkMedialWall.prepared d.operation d.chosenZero v s e i) := by
      simpa only [rawPrepared_eq_class d transparent v] using congrFun h i
    exact Quotient.exact hi
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

/-- Transport preserves the entire polymorphic probability field definitionally. -/
theorem Law.toQuotientLaw_probability (L : Law d v) (transparent : ObservedTransparent d) :
    @RawNativeProbabilitySelection.RawLaw.prob _ d.quotientData (d.classOf v)
      (L.toQuotientLaw transparent) = @Law.prob V d v L := rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Observationally equal output coordinates have equal probabilities.
Only observational preparation consistency and permutation covariance are used. -/
theorem observationally_equal_coordinate_probabilities (L : Law d v)
    (s : ι) (c : Native ι) (i j : ι)
    (hcoord : ObservationalEq d.operation d.weight
      (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c i)
      (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c j)) :
    L.prob s c i = L.prob s c j := by
  have he : ∀ k, ObservationalEq d.operation d.weight
      (RawNetworkMedialWall.prepared d.operation d.chosenZero v s
        (.seq c (.permute (Equiv.swap i j))) k)
      (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c k) := by
    intro k
    change ObservationalEq d.operation d.weight
      (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c (Equiv.swap i j k))
      (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c k)
    by_cases hki : k = i
    · subst k
      intro context
      simpa only [Equiv.swap_apply_left] using (hcoord context).symm
    by_cases hkj : k = j
    · subst k
      intro context
      simpa only [Equiv.swap_apply_right] using hcoord context
    · intro context
      simp only [Equiv.swap_apply_def, if_neg hki, if_neg hkj]
  have hs := congrFun (L.prepared_eq s (.seq c (.permute (Equiv.swap i j))) c he) i
  have hp := L.output_perm s c (Equiv.swap i j) i
  rw [Equiv.swap_apply_left] at hp
  exact hs.symm.trans hp

/-- Conditional selection for actual raw words; no positive-reference premise. -/
theorem probability_eq_normSq (L : Law d v) (transparent : ObservedTransparent d)
    (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = Complex.normSq (c.eval (source s) i) :=
  RawNativeProbabilitySelection.raw_probability_eq_normSq (L.toQuotientLaw transparent) s c i

/-- Absolute weight agreement does not divide by the reference weight. -/
theorem probability_weight_identity (L : Law d v) (transparent : ObservedTransparent d)
    (s : ι) (c : Native ι) (i : ι) :
    d.weight (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c i) =
      L.prob s c i * d.weight v := by
  have h := RawNativeProbabilitySelection.raw_probability_weight_identity
    (L.toQuotientLaw transparent) s c i
  rw [rawPrepared_eq_class d transparent v] at h
  exact h

/-- Division is stated only with an explicitly positive reference weight. -/
theorem probability_eq_weight_ratio (L : Law d v) (transparent : ObservedTransparent d)
    (s : ι) (c : Native ι) (i : ι) (positive : 0 < d.weight v) :
    L.prob s c i =
      d.weight (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c i) / d.weight v := by
  rw [probability_weight_identity L transparent s c i]
  exact (mul_div_cancel_right₀ _ (ne_of_gt positive)).symm

/-- Uniqueness compares supplied laws, rather than assuming their existence. -/
theorem probabilities_equal (L M : Law d v) (transparent : ObservedTransparent d)
    (s : ι) (c : Native ι) (i : ι) : L.prob s c i = M.prob s c i :=
  (probability_eq_normSq L transparent s c i).trans
    (probability_eq_normSq M transparent s c i).symm

/-- Extensional uniqueness of the circuit-indexed probability field. -/
theorem probability_fields_equal (L M : Law d v) (transparent : ObservedTransparent d) :
    @Law.prob V d v L = @Law.prob V d v M := by
  funext α instF instD s c i
  exact probabilities_equal L M transparent s c i

/-! ## Separate law existence from the supplied conserved weight -/

/-- Positive reference weight directly constructs an observational law.
This construction uses neither transparency nor the selection theorem. -/
def normalizedReadoutLaw (d : ObservedData V) (v : V) (positive : 0 < d.weight v) :
    Law d v := by
  let R := RawNetworkMedialWall.readoutLaw d.operation d.chosenZero v
    (fun x => d.weight x / d.weight v)
    (by change d.weight d.chosenZero / d.weight v = 0; rw [d.vacuum, zero_div])
    (div_self (ne_of_gt positive))
    (fun x => div_nonneg (d.nonnegative x) (le_of_lt positive))
    (fun x y => by rw [← add_div, d.conserved, add_div])
  exact {
    prob := R.prob
    nonnegative := R.nonnegative
    normalized := R.normalized
    prepared_eq := by
      intro ι instF instD s c e h
      funext i
      change d.weight (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c i) /
          d.weight v =
        d.weight (RawNetworkMedialWall.prepared d.operation d.chosenZero v s e i) /
          d.weight v
      rw [weight_eq (h i)]
    output_perm := R.output_perm
    spectator_pair := R.spectator_pair
    vacuum := R.vacuum }

theorem normalizedReadoutLaw_probability (d : ObservedData V) (v : V)
    (positive : 0 < d.weight v) (s : ι) (c : Native ι) (i : ι) :
    (normalizedReadoutLaw d v positive).prob s c i =
      d.weight (RawNetworkMedialWall.prepared d.operation d.chosenZero v s c i) / d.weight v := rfl

/-- An observationally zero reference is inconsistent with observational
prepared consistency, normalization, permutation covariance, and vacuum padding.
No gate dynamics is used in this contradiction. -/
theorem no_law_of_reference_observational_zero (d : ObservedData V) (v : V)
    (reference_zero : ObservationalEq d.operation d.weight v d.chosenZero) :
    ¬ Nonempty (Law d v) := by
  rintro ⟨L⟩
  let s : Unit ⊕ Unit := .inl ()
  let t : Unit ⊕ Unit := .inr ()
  have hone : L.prob (() : Unit) .identity () = 1 := by
    simpa using L.normalized (() : Unit) .identity
  have hleft : L.prob s .identity s = 1 := by
    have hv := L.vacuum (κ := Unit) (() : Unit) .identity ()
    simpa only [s, padCircuit] using hv.trans hone
  have hequal : L.prob s .identity s = L.prob s .identity t :=
    observationally_equal_coordinate_probabilities L s .identity s t (by
      simpa [s, t, RawNetworkMedialWall.prepared, WeightFreeRawProbability.evalRaw,
        RawNetworkMedialWall.rawSource] using reference_zero)
  have htotal : L.prob s .identity s + L.prob s .identity t = 1 := by
    simpa [s, t, Fintype.sum_sum_type] using L.normalized s .identity
  linarith

/-- Null weight makes a reference equivalent to the chosen zero in every
stated observation context. No observed transparency premise is used. -/
theorem reference_observational_zero_of_weight_eq_zero (d : ObservedData V) (v : V)
    (null : d.weight v = 0) : ObservationalEq d.operation d.weight v d.chosenZero := by
  have hsq : ‖d.feature v‖ ^ 2 = 0 := (d.norm_feature_sq v).trans null
  have hnorm : ‖d.feature v‖ = 0 := by nlinarith [norm_nonneg (d.feature v)]
  have hfeature : d.feature v = d.feature d.chosenZero :=
    (norm_eq_zero.mp hnorm).trans d.feature_zero.symm
  exact (d.feature_eq_iff_observationalEq v d.chosenZero).mp hfeature

/-- A null raw reference is also the quotient carrier's literal zero. -/
theorem classOf_eq_zero_of_weight_eq_zero (d : ObservedData V) (v : V)
    (null : d.weight v = 0) : d.classOf v = (0 : Data.Carrier d.quotientData) :=
  Quotient.sound (reference_observational_zero_of_weight_eq_zero d v null)

/-- Null references cannot support the strengthened all-width probability law. -/
theorem no_law_of_weight_eq_zero (d : ObservedData V) (v : V)
    (null : d.weight v = 0) : ¬ Nonempty (Law d v) :=
  no_law_of_reference_observational_zero d v
    (reference_observational_zero_of_weight_eq_zero d v null)

/-- A supplied observational law forces positive reference weight, independently
of transparency and independently of conditional probability selection. -/
theorem reference_positive (L : Law d v) : 0 < d.weight v := by
  by_contra hpositive
  have null : d.weight v = 0 := le_antisymm (le_of_not_gt hpositive) (d.nonnegative v)
  exact no_law_of_weight_eq_zero d v null ⟨L⟩

/-- Exact existence criterion for this observational contract, without an
observed transparency premise. It does not classify older literal raw laws. -/
theorem law_nonempty_iff_positive_weight (d : ObservedData V) (v : V) :
    Nonempty (Law d v) ↔ 0 < d.weight v := by
  constructor
  · rintro ⟨L⟩
    exact reference_positive L
  · intro positive
    exact ⟨normalizedReadoutLaw d v positive⟩

end

end IDT.QMClosure.ObservedRawProbabilitySelection
