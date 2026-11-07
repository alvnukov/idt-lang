import Proofs.QMClosure.OriginalGateProbabilityWall
import Proofs.QMClosure.ResponseNativeProbabilitySelection
import Proofs.QMClosure.SourceLocalOriginalSemantics

/-!
# Bare diagonal-signature invariance does not select probabilities

The signature below is supplied mathematical data, not a
probability or physically available deterministic response. Arbitrary fixed
references belong to the existing one-hole context grammar; neither copying
nor independent physical preparation of these references is assumed.

The same original gate has exact square/medial laws and preserves the supplied
signature on every diagonal, but fails contextual diagonal transparency.
All six fields of every existing OriginalLaw transfer to the response contract
without modifying its probability values. Thus bare diagonal invariance cannot
replace contextual transparency in the response probability selection theorem.
No physical availability, actualization, Born derivation, or QM closure follows.
-/

namespace IDT.QMClosure.ResponseDiagonalSignatureWall

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open OperationalContextQuotient ResponseContextQuotient
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open scoped BigOperators

abbrev V := OriginalGateProbabilityWall.V
abbrev T := OriginalGateProbabilityWall.operation
abbrev W := OriginalGateProbabilityWall.weight
abbrev v := OriginalGateProbabilityWall.reference
abbrev g := OriginalGateProbabilityWall.diagonal

/-- Exact raw laws imply their observed versions for every response context. -/
def responseData : Data V ℝ where
  chosenZero := 0
  operation := T
  signature := W
  square p := by
    dsimp only [T]
    rw [OriginalGateProbabilityWall.operation_square]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  medial a b c d := by
    rw [OriginalGateProbabilityWall.operation_medial]
    intro _
    rfl

theorem diagonal_signature (x : V) : W (T (x, x)).1 = W x := by
  dsimp only [T]
  rw [OriginalGateProbabilityWall.operation_diagonal]
  simp [W, OriginalGateProbabilityWall.weight, OriginalGateProbabilityWall.diagonal]

theorem zero_fixed : (T ((0 : V), 0)).1 = 0 := by
  dsimp only [T]
  rw [OriginalGateProbabilityWall.operation_diagonal]
  simp [OriginalGateProbabilityWall.diagonal]

theorem zero_signature : W (0 : V) = 0 := by
  simp [W, OriginalGateProbabilityWall.weight]

theorem source_signature : W v = 2 :=
  OriginalGateProbabilityWall.reference_weight

theorem source_positive : 0 < W v :=
  OriginalGateProbabilityWall.positive_reference

theorem source_diagonal_signature : W (g v) = W v := by
  simpa only [OriginalGateProbabilityWall.operation_diagonal] using diagonal_signature v

theorem source_diagonal_signature_value : W (g v) = 2 :=
  source_diagonal_signature.trans source_signature

/-- The context reference depends only on the fixed comparison point x. -/
def cancelReference (x : V) : V := (-Complex.I * x.1, -Complex.I * x.2)

def a : ℂ := (1 + Complex.I) / 2

theorem a_ne_zero : a ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [a, Complex.div_re, Complex.div_im] at hr

/-- First-output cancellation is exact in both decorated sectors. -/
theorem cancel_output (x y : V) :
    (T (y, cancelReference x)).1 = (a * (y.1 - x.1), -a * (y.2 - x.2)) := by
  apply Prod.ext <;> apply Complex.ext <;>
    simp [T, OriginalGateProbabilityWall.operation, cancelReference, a,
      CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem cancel_self (x : V) : (T (x, cancelReference x)).1 = 0 := by
  rw [cancel_output]
  simp

theorem signature_zero_iff (x : V) : W x = 0 ↔ x = 0 := by
  constructor
  · intro hw
    by_contra hx
    have hp := OriginalGateProbabilityWall.supplied_weight_positive x hx
    change 0 < W x at hp
    linarith
  · rintro rfl
    exact zero_signature

/-- Full contextual equivalence separates the entire raw carrier. -/
theorem responseEq_iff_eq (x y : V) : ResponseEq T W x y ↔ x = y := by
  constructor
  · intro h
    have hc := h (.left .first .hole (cancelReference x))
    change W (T (x, cancelReference x)).1 = W (T (y, cancelReference x)).1 at hc
    rw [cancel_self, zero_signature] at hc
    have hz := (signature_zero_iff _).mp hc.symm
    rw [cancel_output] at hz
    have hp : a * (y.1 - x.1) = 0 := congrArg Prod.fst hz
    have hm : -a * (y.2 - x.2) = 0 := congrArg Prod.snd hz
    have h1 : y.1 = x.1 := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left a_ne_zero)
    have h2 : y.2 = x.2 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (neg_ne_zero.mpr a_ne_zero))
    exact (Prod.ext h1 h2).symm
  · rintro rfl
    intro _
    rfl

/-- A concrete one-hole reference witnesses failure at the chosen mixed source. -/
def witnessContext : Context V := .left .first .hole (0, Complex.I)

theorem witness_context_diagonal : W (witnessContext.eval T (g v)) = 1 / 2 := by
  norm_num [witnessContext, Context.eval, select, T, W, g,
    OriginalGateProbabilityWall.operation, OriginalGateProbabilityWall.weight,
    OriginalGateProbabilityWall.diagonal, OriginalGateProbabilityWall.reference,
    CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im,
    Complex.normSq_apply]

theorem witness_context_source : W (witnessContext.eval T v) = 5 / 2 := by
  norm_num [witnessContext, Context.eval, select, T, W,
    OriginalGateProbabilityWall.operation, OriginalGateProbabilityWall.weight,
    OriginalGateProbabilityWall.reference,
    CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im,
    Complex.normSq_apply]

theorem source_not_responseEq_diagonal : ¬ ResponseEq T W (g v) v := by
  intro h
  have hc := h witnessContext
  rw [witness_context_diagonal, witness_context_source] at hc
  norm_num at hc

theorem not_observedTransparent : ¬ ObservedTransparent responseData := by
  intro h
  apply source_not_responseEq_diagonal
  simpa only [responseData, OriginalGateProbabilityWall.operation_diagonal] using h v

/-! ## Structural syntax adapter, with the original raw evaluator -/

def toOriginal {ι : Type} : Native ι → OriginalGateProbabilityWall.Original ι
  | .identity => .identity
  | .pair i j hij => .pair i j hij
  | .permute e => .permute e
  | .seq c d => .seq (toOriginal c) (toOriginal d)

theorem toOriginal_eval {ι : Type} [DecidableEq ι]
    (c : Native ι) (x : ι → V) :
    (toOriginal c).eval x = WeightFreeRawProbability.evalRaw T c x := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij => rfl
  | permute e => rfl
  | seq c d hc hd =>
    change (toOriginal d).eval ((toOriginal c).eval x) = _
    rw [hc, hd]
    rfl

theorem basisInput_eq_source {ι : Type} [DecidableEq ι] (s : ι) :
    ResponseNativeProbabilitySelection.basisInput responseData v s =
      OriginalGateProbabilityWall.source s := rfl

theorem toOriginal_prepared {ι : Type} [DecidableEq ι]
    (s : ι) (c : Native ι) :
    (toOriginal c).eval (OriginalGateProbabilityWall.source s) =
      ResponseNativeProbabilitySelection.prepared responseData v s c := by
  rw [toOriginal_eval]
  rfl

theorem toOriginal_padCircuit {ι : Type} (κ : Type) (c : Native ι) :
    toOriginal (NativeVacuumProbabilityFamily.padCircuit κ c) =
      OriginalGateProbabilityWall.padCircuit κ (toOriginal c) := by
  induction c with
  | identity => rfl
  | pair i j hij => rfl
  | permute e => rfl
  | seq c d hc hd => simp only [NativeVacuumProbabilityFamily.padCircuit,
      toOriginal, OriginalGateProbabilityWall.padCircuit, hc, hd]

/-- Every old law transfers, with precisely the old probability values. -/
def transportLaw (L : OriginalGateProbabilityWall.OriginalLaw) :
    ResponseNativeProbabilitySelection.Law responseData v where
  prob s c i := L.prob s (toOriginal c) i
  nonnegative s c i := L.nonnegative s (toOriginal c) i
  normalized s c := L.normalized s (toOriginal c)
  prepared_eq s c d h := by
    apply L.prepared_eq s (toOriginal c) (toOriginal d)
    rw [toOriginal_prepared, toOriginal_prepared]
    funext i
    exact (responseEq_iff_eq _ _).mp (h i)
  output_perm s c e i := L.output_perm s (toOriginal c) e i
  spectator_pair s c i j k hij hki hkj :=
    L.spectator_pair s (toOriginal c) i j k hij hki hkj
  vacuum s c i := by
    rw [toOriginal_padCircuit]
    exact L.vacuum s (toOriginal c) i

theorem transportLaw_probability (L : OriginalGateProbabilityWall.OriginalLaw)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    (transportLaw L).prob s c i = L.prob s (toOriginal c) i := rfl

/-- Chronological order 01;02;12, unchanged from the old literal witness. -/
def witness : Native (Fin 3) :=
  .seq (.seq (.pair 0 1 (by decide)) (.pair 0 2 (by decide)))
    (.pair 1 2 (by decide))

theorem toOriginal_witness : toOriginal witness = OriginalGateProbabilityWall.witness := rfl

def quarterLaw := transportLaw OriginalGateProbabilityWall.quarterLaw
def threeQuarterLaw := transportLaw OriginalGateProbabilityWall.threeQuarterLaw

theorem quarter_probability : quarterLaw.prob 0 witness 1 = 1 / 4 :=
  OriginalGateProbabilityWall.quarter_probability

theorem three_quarter_probability : threeQuarterLaw.prob 0 witness 1 = 1 / 2 :=
  OriginalGateProbabilityWall.three_quarter_probability

theorem response_probability_nonunique :
    quarterLaw.prob 0 witness 1 ≠ threeQuarterLaw.prob 0 witness 1 := by
  rw [quarter_probability, three_quarter_probability]
  norm_num

/-- Bare global diagonal-signature invariance, exact structural laws, a fixed
zero, and a positive chosen-source signature coexist with distinct laws
satisfying the entire six-field response contract at every finite width. -/
theorem bare_diagonal_invariance_does_not_select :
    (∀ x, W (T (x, x)).1 = W x) ∧
    (T ((0 : V), 0)).1 = 0 ∧
    0 < W v ∧
    ∃ L M : ResponseNativeProbabilitySelection.Law responseData v,
      L.prob 0 witness 1 ≠ M.prob 0 witness 1 :=
  ⟨diagonal_signature, zero_fixed, source_positive,
    quarterLaw, threeQuarterLaw, response_probability_nonunique⟩

end
end IDT.QMClosure.ResponseDiagonalSignatureWall
