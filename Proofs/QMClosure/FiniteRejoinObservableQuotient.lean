import Proofs.QMClosure.FiniteRejoinReversibleQuadraticReadout
import Proofs.QMClosure.LocalBranchOperatorFaithfulness
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The observable quotient of a reversible finite rejoin

This conditional construction consumes the reconstructed positive quadratic
readout on the full supplied domain. Its equivalence relation is null difference,
equivalently equality of every additive-reference readout. It descends the native
branches and derives exact swap-square on this observable quotient.

A positive reference readout supplies normalized serial SourceResponse. Existing
local-branch theorems then provide faithful native generated arithmetic and its
canonical algebraic conjugation. Serial multiplication is derived by that adapter.

Exact fourth rejoin here concerns the observable quotient. Hidden null directions
can retain other periods on the original carrier. Equality of individual weights
alone supplies no state identification. The null subgroup has no asserted ambient
scalar-ideal structure. Physical adjoint, physical time reversal, actualization,
and full QM remain outside these conclusions.

-/

noncomputable section

namespace IDT.QMClosure.FiniteRejoinObservableQuotient

open QuadraticRecordRefinement

variable {V : Type*} [AddCommMonoid V]
variable {G : FiniteRejoinReversibleQuadraticReadout.Gate V} {W : V → ℝ}

/-- Additive directions invisible to the supplied full-domain quadratic readout. -/
def nullSubgroup (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) : AddSubgroup G.Carrier :=
  h.quadratic.nullSubgroup

/-- Preparations modulo null differences of the reconstructed readout. -/
abbrev Observable (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) := G.Carrier ⧸ nullSubgroup h

/-- Canonical additive projection, with the original monoid operations preserved. -/
def projection (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) : G.Carrier →+ Observable h :=
  QuotientAddGroup.mk' (nullSubgroup h)

theorem projection_surjective (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    Function.Surjective (projection h) :=
  QuotientAddGroup.mk'_surjective (nullSubgroup h)

/-- Quotient equality records the readout of a difference. -/
theorem projection_eq_iff (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (x y : G.Carrier) :
    projection h x = projection h y ↔ W (x - y) = 0 := by
  exact QuotientAddGroup.eq_iff_sub_mem

theorem projection_eq_zero_iff (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (x : G.Carrier) :
    projection h x = 0 ↔ W x = 0 := by
  exact QuotientAddGroup.eq_zero_iff x

/-- This is exactly the equivalence tested by every additive coherent reference. -/
theorem projection_eq_iff_all_reference_tests
    (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (x y : G.Carrier) :
    projection h x = projection h y ↔ ∀ z : G.Carrier, W (x + z) = W (y + z) := by
  rw [projection_eq_iff]
  exact PositiveQuadraticPolarization.null_iff_all_reference_tests h.quadratic x y

private theorem readout_eq_of_projection_eq (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W)
    {x y : G.Carrier} (he : projection h x = projection h y) : W x = W y := by
  have ht := h.quadratic.null_translate y (x - y) ((projection_eq_iff h x y).mp he)
  have heq : y + (x - y) = x := by abel
  rw [heq] at ht
  exact ht

/-- The full-domain readout descends through null-difference equivalence. -/
def weight (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) : Observable h → ℝ :=
  Quotient.lift (fun x : G.Carrier => W x) (by
    intro x y hxy
    exact readout_eq_of_projection_eq h (Quotient.sound hxy))

@[simp] theorem weight_projection (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (x : G.Carrier) :
    weight h (projection h x) = W x := rfl

/-- Positivity and the parallelogram law survive the additive quotient. -/
theorem positiveQuadratic (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    PositiveQuadratic (weight h) := by
  constructor
  · intro u
    obtain ⟨x, rfl⟩ := projection_surjective h u
    exact h.quadratic.nonnegative x
  · intro u v
    obtain ⟨x, rfl⟩ := projection_surjective h u
    obtain ⟨y, rfl⟩ := projection_surjective h v
    simpa only [← map_add, ← map_sub, weight_projection] using
      h.quadratic.parallelogram x y

/-- The descended quadratic readout has precisely one zero-readout class. -/
theorem weight_eq_zero_iff (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (u : Observable h) :
    weight h u = 0 ↔ u = 0 := by
  obtain ⟨x, rfl⟩ := projection_surjective h u
  rw [weight_projection]
  exact (projection_eq_zero_iff h x).symm

theorem branchA_preserves_null (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    nullSubgroup h ≤ (nullSubgroup h).comap G.a := by
  intro x hx
  change W x = 0 at hx
  change W (G.a x) = 0
  rw [(h.branch_halves x).1, hx, zero_div]

theorem branchB_preserves_null (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    nullSubgroup h ≤ (nullSubgroup h).comap G.b := by
  intro x hx
  change W x = 0 at hx
  change W (G.b x) = 0
  rw [(h.branch_halves x).2, hx, zero_div]

/-- The inverse-word gains follow from the original branch halves. -/
theorem inverseA_weight (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (x : V) :
    W (G.inverseA x) = 2 * W x := by
  have hback : G.a (G.inverseA x) = x :=
    congrArg (fun f : AddMonoid.End V => f x) G.inverseA_laws.2
  have hx := (h.branch_halves (G.inverseA x)).1
  rw [hback] at hx
  linarith

theorem inverseB_weight (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (x : V) :
    W (G.inverseB x) = 2 * W x := by
  have hback : G.b (G.inverseB x) = x :=
    congrArg (fun f : AddMonoid.End V => f x) G.inverseB_laws.2
  have hx := (h.branch_halves (G.inverseB x)).2
  rw [hback] at hx
  linarith

theorem inverseA_preserves_null (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    nullSubgroup h ≤ (nullSubgroup h).comap G.inverseA := by
  intro x hx
  change W x = 0 at hx
  change W (G.inverseA x) = 0
  rw [inverseA_weight h, hx, mul_zero]

theorem inverseB_preserves_null (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    nullSubgroup h ≤ (nullSubgroup h).comap G.inverseB := by
  intro x hx
  change W x = 0 at hx
  change W (G.inverseB x) = 0
  rw [inverseB_weight h, hx, mul_zero]

/-- Descended first native branch. -/
def A (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) : AddMonoid.End (Observable h) :=
  QuotientAddGroup.map (nullSubgroup h) (nullSubgroup h) G.a (branchA_preserves_null h)

/-- Descended second native branch. -/
def B (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) : AddMonoid.End (Observable h) :=
  QuotientAddGroup.map (nullSubgroup h) (nullSubgroup h) G.b (branchB_preserves_null h)

@[simp] theorem A_projection (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (x : G.Carrier) :
    A h (projection h x) = projection h (G.a x) := rfl

@[simp] theorem B_projection (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (x : G.Carrier) :
    B h (projection h x) = projection h (G.b x) := rfl

/-- The quotient branch halves hold at every quotient preparation. -/
theorem branch_halves (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (u : Observable h) :
    weight h (A h u) = weight h u / 2 ∧
    weight h (B h u) = weight h u / 2 := by
  obtain ⟨x, rfl⟩ := projection_surjective h u
  simpa only [A_projection, B_projection, weight_projection] using h.branch_halves x

theorem transparent_coefficients (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    A h + B h = 1 := by
  apply AddMonoidHom.ext
  intro u
  obtain ⟨x, rfl⟩ := projection_surjective h u
  change A h (projection h x) + B h (projection h x) = projection h x
  rw [A_projection, B_projection, ← map_add]
  exact congrArg (projection h)
    (congrArg (fun f : AddMonoid.End V => f x) G.transparent)

theorem commute_coefficients (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    A h * B h = B h * A h := by
  apply AddMonoidHom.ext
  intro u
  obtain ⟨x, rfl⟩ := projection_surjective h u
  change projection h (G.a (G.b x)) = projection h (G.b (G.a x))
  exact congrArg (projection h)
    (congrArg (fun f : AddMonoid.End V => f x) G.commute.eq)

/-- Vanishing same-history output becomes exact equality only after quotienting. -/
theorem same_coefficients (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    A h * A h + B h * B h = 0 := by
  apply AddMonoidHom.ext
  intro u
  obtain ⟨x, rfl⟩ := projection_surjective h u
  change projection h (G.a (G.a x)) + projection h (G.b (G.b x)) = 0
  rw [← map_add]
  exact (projection_eq_zero_iff h (G.same x)).mpr (h.same_null x)

/-- The mixed action is derived by expanding the square of transparency. -/
theorem cross_coefficients (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    A h * B h + B h * A h = 1 := by
  have ht : (A h + B h) * (A h + B h) = 1 := by
    rw [transparent_coefficients h, one_mul]
  have he : (A h * A h + B h * B h) + (A h * B h + B h * A h) = 1 := by
    calc
      _ = (A h + B h) * (A h + B h) := by noncomm_ring
      _ = 1 := ht
  rwa [same_coefficients h, zero_add] at he

theorem double_mixed_coefficients (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    A h * B h + A h * B h = 1 := by
  simpa only [← commute_coefficients h] using cross_coefficients h

/-- Complete additive symmetric mixer on observable preparations. -/
def operation (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    (Observable h × Observable h) →+ (Observable h × Observable h) where
  toFun p := (A h p.1 + B h p.2, B h p.1 + A h p.2)
  map_zero' := by simp
  map_add' p q := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add] <;> abel

theorem operation_transparent (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (u : Observable h) :
    operation h (u, u) = (u, u) := by
  have ht : A h u + B h u = u :=
    congrArg (fun f : AddMonoid.End (Observable h) => f u) (transparent_coefficients h)
  apply Prod.ext
  · exact ht
  · change B h u + A h u = u
    simpa only [add_comm] using ht

/-- Exact complete swap-square is obtained on the observable quotient. -/
theorem operation_square (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W)
    (p : Observable h × Observable h) :
    operation h (operation h p) = p.swap := by
  have hs (u : Observable h) : A h (A h u) + B h (B h u) = 0 :=
    congrArg (fun f : AddMonoid.End (Observable h) => f u) (same_coefficients h)
  have hc (u : Observable h) : A h (B h u) + B h (A h u) = u :=
    congrArg (fun f : AddMonoid.End (Observable h) => f u) (cross_coefficients h)
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · change A h (A h x + B h y) + B h (B h x + A h y) = y
    calc
      _ = (A h (A h x) + B h (B h x)) +
          (A h (B h y) + B h (A h y)) := by simp only [map_add]; abel
      _ = y := by rw [hs x, hc y, zero_add]
  · change B h (A h x + B h y) + A h (B h x + A h y) = x
    calc
      _ = (A h (B h x) + B h (A h x)) +
          (A h (A h y) + B h (B h y)) := by simp only [map_add]; abel
      _ = x := by rw [hc x, hs y, add_zero]

/-- Existing local-branch arithmetic now applies to the descended native mixer. -/
def nativeGate (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) : LocalBranchOperatorFaithfulness.Gate (Observable h) where
  operation := operation h
  transparent := operation_transparent h
  square := operation_square h

/-- The native gate's derived inverse agrees with the quotient inverse. -/
theorem native_neg (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (u : (nativeGate h).Carrier) :
    ((-u : (nativeGate h).Carrier) : Observable h) = -(u : Observable h) := by
  have he : ((-u : (nativeGate h).Carrier) : Observable h) + (u : Observable h) = 0 := by
    exact neg_add_cancel u
  exact eq_neg_of_add_eq_zero_left he

/-- Explicit additive transport between the two derived group presentations. -/
def nativeCarrierEquiv (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    (nativeGate h).Carrier ≃+ Observable h where
  toFun u := u
  invFun u := u
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The descended readout expressed on the existing native carrier synonym. -/
def nativeWeight (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (u : (nativeGate h).Carrier) : ℝ :=
  weight h ((nativeCarrierEquiv h) u)

@[simp] theorem nativeWeight_projection
    (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (x : G.Carrier) :
    nativeWeight h (projection h x) = W x := rfl

theorem nativeWeight_eq_zero_iff
    (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W)
    (u : (nativeGate h).Carrier) : nativeWeight h u = 0 ↔ u = 0 := by
  exact weight_eq_zero_iff h (u : Observable h)

/-- Quadratic transport explicitly accounts for the derived inverse. -/
theorem nativePositiveQuadratic (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    PositiveQuadratic (nativeWeight h) := by
  constructor
  · intro u
    exact (positiveQuadratic h).nonnegative ((nativeCarrierEquiv h) u)
  · intro u v
    change weight h ((nativeCarrierEquiv h) (u + v)) +
        weight h ((nativeCarrierEquiv h) (u - v)) =
      2 * weight h ((nativeCarrierEquiv h) u) +
        2 * weight h ((nativeCarrierEquiv h) v)
    rw [map_add, map_sub]
    exact (positiveQuadratic h).parallelogram
      ((nativeCarrierEquiv h) u) ((nativeCarrierEquiv h) v)

@[simp] theorem nativeA_apply (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W)
    (u : (nativeGate h).Carrier) :
    ((nativeGate h).A u : Observable h) = A h (u : Observable h) := by
  change A h u + B h 0 = A h u
  rw [map_zero, add_zero]

@[simp] theorem nativeB_apply (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W)
    (u : (nativeGate h).Carrier) :
    ((nativeGate h).B u : Observable h) = B h (u : Observable h) := by
  change B h u + A h 0 = B h u
  rw [map_zero, add_zero]

theorem native_branch_half (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (c : Bool)
    (u : (nativeGate h).Carrier) :
    nativeWeight h ((nativeGate h).branch c u) = nativeWeight h u / 2 := by
  cases c with
  | false =>
    change weight h (((nativeGate h).B u : (nativeGate h).Carrier) : Observable h) = _
    rw [nativeB_apply]
    exact (branch_halves h (u : Observable h)).2
  | true =>
    change weight h (((nativeGate h).A u : (nativeGate h).Carrier) : Observable h) = _
    rw [nativeA_apply]
    exact (branch_halves h (u : Observable h)).1

/-- The original finite rejoin has exact fourth branch equality after descent. -/
theorem native_fourth_rejoin (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    (nativeGate h).A ^ 4 = (nativeGate h).B ^ 4 :=
  (nativeGate h).fourth_coefficients_equal

section Reference

variable (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) (p : V) (hp : 0 < W p)

/-- Normalize the supplied full-domain readout at an actual positive reference. -/
def wordWeight (w : LocalBranchOperatorFaithfulness.Word) : ℝ :=
  nativeWeight h ((nativeGate h).evalWord w (projection h p)) / W p

include hp

theorem wordWeight_nil : wordWeight h p [] = 1 := by
  change W p / W p = 1
  exact div_self (ne_of_gt hp)

theorem wordWeight_singleton (c : Bool) : wordWeight h p [c] = 1 / 2 := by
  unfold wordWeight
  rw [LocalBranchOperatorFaithfulness.Gate.evalWord_singleton, native_branch_half]
  change (W p / 2) / W p = 1 / 2
  field_simp [ne_of_gt hp]

theorem wordWeight_step (c : Bool) (w : LocalBranchOperatorFaithfulness.Word) :
    wordWeight h p (c :: w) = wordWeight h p [c] * wordWeight h p w := by
  unfold wordWeight
  rw [LocalBranchOperatorFaithfulness.Gate.evalWord_cons]
  change nativeWeight h ((nativeGate h).branch c
      ((nativeGate h).evalWord w (projection h p))) / W p = _
  rw [native_branch_half]
  have hs : nativeWeight h ((nativeGate h).evalWord [c] (projection h p)) / W p = 1 / 2 :=
    wordWeight_singleton h p hp c
  rw [hs]
  ring

/-- The serial step, source extensionality and column are derived from the
quadratic readout. Multiplicativity is subsequently derived by SourceResponse. -/
def sourceResponse : LocalBranchOperatorFaithfulness.SourceResponse (nativeGate h) where
  reference := projection h p
  weight := wordWeight h p
  step := wordWeight_step h p hp
  extensional := by
    intro x y he
    exact congrArg (fun u : (nativeGate h).Carrier => nativeWeight h u / W p) he
  column := by
    rw [wordWeight_singleton h p hp true, wordWeight_singleton h p hp false]
    norm_num

/-- The existing adapter derives concatenation multiplicativity from local steps. -/
theorem wordWeight_append (x y : LocalBranchOperatorFaithfulness.Word) :
    wordWeight h p (x ++ y) = wordWeight h p x * wordWeight h p y :=
  (sourceResponse h p hp).weight_append x y

/-- The descended positive reference has infinite integer additive order. -/
theorem reference_int_torsion_free (n : ℤ)
    (hn : n • (sourceResponse h p hp).reference = 0) : n = 0 :=
  (sourceResponse h p hp).reference_int_torsion_free n hn

/-- The positive reference separates the entire native generated operator algebra. -/
theorem generatedEvaluation_injective :
    Function.Injective (sourceResponse h p hp).evaluate :=
  (sourceResponse h p hp).generatedEvaluation_injective

/-- Faithful Gaussian-dyadic evaluation uses the existing arithmetic presentation. -/
theorem dyadicReference_injective : Function.Injective
    (fun d => (sourceResponse h p hp).operatorResponse.dyadicOperator d
      (sourceResponse h p hp).reference) :=
  (sourceResponse h p hp).dyadicReference_injective

/-- Exact native generated-ring coverage by the existing arithmetic subring. -/
def generatedArithmeticEquiv :
    (nativeGate h).generated ≃+* (sourceResponse h p hp).operatorResponse.arithmeticSubring :=
  (sourceResponse h p hp).operatorResponse.generatedArithmeticEquiv

/-- Canonical conjugation on the native generated operator algebra. -/
def canonicalConjugation : (nativeGate h).generated ≃+* (nativeGate h).generated :=
  (sourceResponse h p hp).operatorResponse.canonicalConjugation

theorem canonicalConjugation_a :
    canonicalConjugation h p hp (nativeGate h).generatedA = (nativeGate h).generatedB :=
  (sourceResponse h p hp).operatorResponse.canonicalConjugation_a

theorem canonicalConjugation_b :
    canonicalConjugation h p hp (nativeGate h).generatedB = (nativeGate h).generatedA :=
  (sourceResponse h p hp).operatorResponse.canonicalConjugation_b

theorem canonicalConjugation_involutive :
    Function.Involutive (canonicalConjugation h p hp) :=
  (sourceResponse h p hp).operatorResponse.canonicalConjugation_involutive

end Reference

end IDT.QMClosure.FiniteRejoinObservableQuotient
