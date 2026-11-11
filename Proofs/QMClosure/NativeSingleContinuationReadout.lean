import Proofs.QMClosure.FixedCornerHalfMixtureReadout
import Proofs.QMClosure.NativeGeneratorMixtureReadout

/-!
# One fixed-corner continuation law and two native generator transfers

For a rotation-invariant real function on all Gaussian integers, the prescribed
four corner probes transform by a coordinate permutation under the affine map
`z ↦ turn z - (1,0)`. Conjugation by this map rotates a translation. Consequently,
equal-pair-sum congruence under the single translation `(1,0)` implies the three
remaining signed coordinate continuation laws.

For a real readout on the supplied initial two-relator presentation, one scalar
normalization and its two universal native generator transfers derive the unit
and fixed-half native transfer contract. They also derive rotation invariance
of the integer restriction. Adding the single universal corner-pair law then
selects the squared norm on every presented history.

The grammar, real-valued readout, normalization, two universal native transfer
laws and single universal pair-sufficiency law remain supplied contracts.
Equal-half ensemble arithmetic is external to coherent composition. Physical
origins, event/frequency interpretation and full QM closure remain open.
-/

noncomputable section

namespace IDT.QMClosure.NativeSingleContinuationReadout

open FiniteMixtureContinuationRank
open FiniteTranslationSmallRankSupport
open IDT.FixedCornerHalfMixtureReadout
open NativeInitialHistoryPresentation
open SingleCalibrationScalarFaithfulness
open NativeGeneratorMixtureReadout

attribute [local instance] presentationCommRing presentationCharZero

section Geometry

/-- An affine quarter turn preserving the prescribed corner-probe family. -/
def cornerTurn (z : IntegerLattice) : IntegerLattice := turn z - (1, 0)

/-- Three affine quarter turns give the inverse on the full integer lattice. -/
def cornerTurnInverse (z : IntegerLattice) : IntegerLattice :=
  cornerTurn (cornerTurn (cornerTurn z))

/-- Output corner `j` after the affine turn reads input corner `cornerPermutation j`. -/
def cornerPermutation : Fin 4 → Fin 4 := ![2, 0, 3, 1]

/-- The affine corner turn has order four. -/
theorem cornerTurn_four (z : IntegerLattice) :
    cornerTurn (cornerTurn (cornerTurn (cornerTurn z))) = z := by
  apply Prod.ext <;> dsimp [cornerTurn, turn] <;> ring

/-- Conjugation rotates every integer-lattice translation. -/
theorem cornerTurn_inverse_add (z s : IntegerLattice) :
    cornerTurn (cornerTurnInverse z + s) = z + turn s := by
  apply Prod.ext <;> dsimp [cornerTurnInverse, cornerTurn, turn] <;> ring

/-- Rotation invariance turns the affine corner action into a fixed permutation. -/
theorem fixedCornerProbes_cornerTurn (f : IntegerLattice → ℝ)
    (hrot : ∀ z, f (turn z) = f z) (z : IntegerLattice) (j : Fin 4) :
    fixedCornerProbes f (cornerTurn z) j =
      fixedCornerProbes f z (cornerPermutation j) := by
  have hcorner : cornerTurn z + normCorner j =
      turn (z + normCorner (cornerPermutation j)) := by
    fin_cases j <;> apply Prod.ext <;>
      norm_num [cornerTurn, cornerPermutation, normCorner, turn,
        Matrix.cons_val_two, Matrix.cons_val_three] <;> ring
  change f (cornerTurn z + normCorner j) = f (z + normCorner (cornerPermutation j))
  rw [hcorner, hrot]

/-- Equal sums of probe pairs are preserved by the affine corner turn. -/
theorem fixedCornerProbes_pairCongruent_cornerTurn (f : IntegerLattice → ℝ)
    (hrot : ∀ z, f (turn z) = f z) :
    PairCongruentUnder (fixedCornerProbes f) cornerTurn := by
  intro a b c d h
  funext j
  change fixedCornerProbes f (cornerTurn a) j + fixedCornerProbes f (cornerTurn b) j =
    fixedCornerProbes f (cornerTurn c) j + fixedCornerProbes f (cornerTurn d) j
  simp only [fixedCornerProbes_cornerTurn f hrot]
  exact congrFun h (cornerPermutation j)

/-- Three forward transports preserve pair equality under the inverse map. -/
theorem fixedCornerProbes_pairCongruent_cornerTurnInverse (f : IntegerLattice → ℝ)
    (hrot : ∀ z, f (turn z) = f z) :
    PairCongruentUnder (fixedCornerProbes f) cornerTurnInverse := by
  intro a b c d h
  have hK := fixedCornerProbes_pairCongruent_cornerTurn f hrot
  exact hK _ _ _ _ (hK _ _ _ _ (hK _ _ _ _ h))

/-- One translation law transports to its quarter-turned translation. -/
theorem pairCongruent_translation_turn (f : IntegerLattice → ℝ)
    (hrot : ∀ z, f (turn z) = f z) (s : IntegerLattice)
    (hs : PairCongruentUnder (fixedCornerProbes f) (fun z => z + s)) :
    PairCongruentUnder (fixedCornerProbes f) (fun z => z + turn s) := by
  intro a b c d h
  have hpre := fixedCornerProbes_pairCongruent_cornerTurnInverse f hrot a b c d h
  have hshift := hs _ _ _ _ hpre
  have hpost := fixedCornerProbes_pairCongruent_cornerTurn f hrot _ _ _ _ hshift
  simpa only [cornerTurn_inverse_add] using hpost

/-- The single positive-real unit translation supplies all four local laws. -/
theorem fixedCornerPairLaws_of_single_translation (f : IntegerLattice → ℝ)
    (hrot : ∀ z, f (turn z) = f z)
    (hsingle : PairCongruentUnder (fixedCornerProbes f) (fun z => z + (1, 0))) :
    ∀ j, PairCongruentUnder (fixedCornerProbes f) (fun z => z + localStep j) := by
  have h1 := pairCongruent_translation_turn f hrot (1, 0) hsingle
  have h2 := pairCongruent_translation_turn f hrot (turn (1, 0)) h1
  have h3 := pairCongruent_translation_turn f hrot (turn (turn (1, 0))) h2
  intro j
  fin_cases j
  · simpa [localStep] using hsingle
  · simpa [localStep, turn] using h2
  · simpa [localStep, turn] using h1
  · simpa [localStep, turn] using h3

end Geometry

/-- The one continuation premise uses exactly the prescribed four probes of
this readout's integer restriction. -/
def SingleContinuationLaw (W : Presentation → ℝ) : Prop :=
  PairCongruentUnder (fixedCornerProbes (integerReadout W)) (fun z => z + (1, 0))

/-- The reduced premises derive the complete native-transfer and local-pair contract. -/
theorem native_contract_of_single_continuation
    (W : Presentation → ℝ) (hnorm : W a + W b = 1)
    (ha : ∀ p, W (a * p) = W a * W p)
    (hb : ∀ p, W (b * p) = W b * W p)
    (hsingle : SingleContinuationLaw W) : NativeTransfer W ∧ FixedCornerPairLaws W := by
  let L := nativeTransfer_of_normalized_generator_transfer W hnorm ha hb
  refine ⟨L, ?_⟩
  unfold FixedCornerPairLaws
  apply fixedCornerPairLaws_of_single_translation (integerReadout W) ?_ hsingle
  intro z
  change W (Arithmetic.gaussian phase (turn z)) = W (Arithmetic.gaussian phase z)
  rw [gaussian_turn, readout_phase_mul L]

/-- The squared norm on the faithful algebraic model is a conclusion for the
supplied arbitrary readout under the reduced premises. -/
theorem readout_eq_complex_norm_of_single_continuation
    (W : Presentation → ℝ) (hnorm : W a + W b = 1)
    (ha : ∀ p, W (a * p) = W a * W p)
    (hb : ∀ p, W (b * p) = W b * W p)
    (hsingle : SingleContinuationLaw W) (p : Presentation) :
    W p = Complex.normSq (complexEval p) := by
  obtain ⟨L, M⟩ := native_contract_of_single_continuation W hnorm ha hb hsingle
  exact readout_eq_complex_norm L M p

/-- Every dyadic Gaussian normal form has the selected raw readout. -/
theorem readout_normal_form_of_single_continuation
    (W : Presentation → ℝ) (hnorm : W a + W b = 1)
    (ha : ∀ p, W (a * p) = W a * W p)
    (hb : ∀ p, W (b * p) = W b * W p)
    (hsingle : SingleContinuationLaw W) (k : ℕ) (z : IntegerLattice) :
    W (NormalForm.value k z) =
      ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / (4 : ℝ) ^ k := by
  obtain ⟨L, M⟩ := native_contract_of_single_continuation W hnorm ha hb hsingle
  exact readout_normal_form L M k z

/-- Global multiplication, reflection and native mixer conservation follow
through the derived contract. -/
theorem global_readout_laws_of_single_continuation
    (W : Presentation → ℝ) (hnorm : W a + W b = 1)
    (ha : ∀ p, W (a * p) = W a * W p)
    (hb : ∀ p, W (b * p) = W b * W p)
    (hsingle : SingleContinuationLaw W) :
    (∀ p q, W (p * q) = W p * W q) ∧
      (∀ p, W (reflection p) = W p) ∧
      (∀ p, 0 ≤ W p) ∧
      (∀ p, W p = 0 ↔ p = 0) ∧
      (∀ p : Presentation × Presentation,
        W (mixer p).1 + W (mixer p).2 = W p.1 + W p.2) := by
  obtain ⟨L, M⟩ := native_contract_of_single_continuation W hnorm ha hb hsingle
  exact ⟨readout_multiplicative L M, readout_reflection L M,
    readout_nonnegative L M, readout_zero_iff L M, mixer_conservation L M⟩

section Witness

/-- The concrete squared-norm readout satisfies the exact single translation law. -/
theorem modelReadout_single_continuation : SingleContinuationLaw modelReadout := by
  unfold SingleContinuationLaw
  rw [modelReadout_integer]
  exact normReadout_pairCongruent_translation (1, 0)

/-- All reduced premises have a concrete inhabitant. -/
theorem modelReadout_reduced_contract :
    modelReadout a + modelReadout b = 1 ∧
      (∀ p, modelReadout (a * p) = modelReadout a * modelReadout p) ∧
      (∀ p, modelReadout (b * p) = modelReadout b * modelReadout p) ∧
      SingleContinuationLaw modelReadout := by
  refine ⟨?_, ?_, ?_, modelReadout_single_continuation⟩
  · rw [readout_a modelReadout_native, readout_b modelReadout_native]
    norm_num
  · intro p
    rw [modelReadout_native.left_a, readout_a modelReadout_native]
    ring
  · intro p
    rw [modelReadout_native.left_b, readout_b modelReadout_native]
    ring

end Witness

end IDT.QMClosure.NativeSingleContinuationReadout
