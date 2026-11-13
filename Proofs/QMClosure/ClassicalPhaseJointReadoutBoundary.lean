import Proofs.QMClosure.ClassicalFinitePhaseRepresentation

/-! A joint-readout boundary for one proposed character transformation.

The ambient cone remains the full positive classical distribution cone from
ClassicalFinitePhaseRepresentation. The map H preserves the six chosen
preparations and their nonnegative normalized mixtures, but fails positivity on
the full simplex. A positive generated joint preparation and a positive generated
joint effect also witness failure of its specified tensor extension.

No restricted 60-state composite cone, all-reference atomicity, ball/SO(d)
reconstruction or full physical-core countermodel is asserted here.
-/

namespace IDT.QMClosure.ClassicalPhaseJointReadoutBoundary

noncomputable section

open ClassicalFinitePhaseRepresentation

def character (axis : Fin 3) (s : Ω) : ℚ := sign (axisValue axis s)

@[simp] theorem axisValue_x (s : Ω) : axisValue 0 s = s.2 := rfl
@[simp] theorem axisValue_y (s : Ω) : axisValue 1 s = Bool.xor s.1 s.2 := rfl
@[simp] theorem axisValue_z (s : Ω) : axisValue 2 s = s.1 := rfl

def swapQP : Ω ≃ Ω where
  toFun s := (s.2, s.1)
  invFun s := (s.2, s.1)
  left_inv := by rintro ⟨q, p⟩; rfl
  right_inv := by rintro ⟨q, p⟩; rfl

def W : Module.End ℚ Local := (permutationAction swapQP).toLinearMap

theorem W_normalized (ρ : Local) (hρ : normalized ρ) : normalized (W ρ) :=
  permutation_normalized swapQP ρ hρ

theorem W_coordinates (ρ : Local) :
    coordinates (W ρ) 0 = coordinates ρ 2 ∧
      coordinates (W ρ) 1 = coordinates ρ 1 ∧
      coordinates (W ρ) 2 = coordinates ρ 0 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp [coordinates, W, permutationAction, swapQP, sign, Fintype.sum_prod_type]
    ring

def H : Module.End ℚ Local where
  toFun ρ s := (total ρ + character 0 s * coordinates ρ 2 -
    character 1 s * coordinates ρ 1 + character 2 s * coordinates ρ 0) / 4
  map_add' := by
    intro ρ σ
    funext s
    simp [total, coordinates, Finset.sum_add_distrib, mul_add]
    ring
  map_smul' := by
    intro c ρ
    funext s
    simp [total, coordinates, smul_eq_mul, Fintype.sum_prod_type]
    ring

theorem H_apply (ρ : Local) (s : Ω) :
    H ρ s = (total ρ + character 0 s * coordinates ρ 2 -
      character 1 s * coordinates ρ 1 + character 2 s * coordinates ρ 0) / 4 := rfl

theorem fourier_reconstruction (ρ : Local) (s : Ω) :
    ρ s = (total ρ + character 0 s * coordinates ρ 0 +
      character 1 s * coordinates ρ 1 + character 2 s * coordinates ρ 2) / 4 := by
  rcases s with ⟨q, p⟩
  cases q <;> cases p <;>
    simp [total, coordinates, character, sign, Fintype.sum_prod_type] <;> ring

theorem H_total (ρ : Local) : total (H ρ) = total ρ := by
  simp [total, H_apply, character, sign, Fintype.sum_prod_type]
  ring

theorem H_coordinates (ρ : Local) :
    coordinates (H ρ) 0 = coordinates ρ 2 ∧
      coordinates (H ρ) 1 = -coordinates ρ 1 ∧
      coordinates (H ρ) 2 = coordinates ρ 0 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp [coordinates, H_apply, total, character, sign, Fintype.sum_prod_type]
    ring

theorem H_involutive : H * H = 1 := by
  apply LinearMap.ext
  intro ρ
  funext s
  obtain ⟨hx, hy, hz⟩ := H_coordinates ρ
  change H (H ρ) s = ρ s
  rw [H_apply, H_total, hz, hy, hx]
  calc
    _ = (total ρ + character 0 s * coordinates ρ 0 +
        character 1 s * coordinates ρ 1 + character 2 s * coordinates ρ 2) / 4 := by ring
    _ = ρ s := (fourier_reconstruction ρ s).symm

abbrev Label := Fin 3 × Bool

def transformLabel (l : Label) : Label :=
  (![2, 1, 0] l.1, if l.1 = 1 then !l.2 else l.2)

def labelPermutation : Label ≃ Label where
  toFun := transformLabel
  invFun := transformLabel
  left_inv := by rintro ⟨axis, out⟩; fin_cases axis <;> cases out <;> decide +kernel
  right_inv := by rintro ⟨axis, out⟩; fin_cases axis <;> cases out <;> decide +kernel

/-- H swaps the x/z preparation pairs and flips the y outcome. -/
theorem H_preparation (l : Label) :
    H (preparation l.1 l.2) = preparation (labelPermutation l).1 (labelPermutation l).2 := by
  rcases l with ⟨axis, out⟩
  fin_cases axis <;> cases out <;> decide +kernel

def chosenMixture (w : Label → ℚ) : Local :=
  ∑ l, w l • preparation l.1 l.2

def IsChosenMixture (ρ : Local) : Prop :=
  ∃ w : Label → ℚ, (∀ l, 0 ≤ w l) ∧ (∑ l, w l) = 1 ∧ ρ = chosenMixture w

theorem chosen_mixture_normalized (w : Label → ℚ)
    (hpositive : ∀ l, 0 ≤ w l) (hsum : (∑ l, w l) = 1) :
    normalized (chosenMixture w) := by
  constructor
  · intro s
    change 0 ≤ ∑ l, w l * preparation l.1 l.2 s
    exact Finset.sum_nonneg (fun l _ =>
      mul_nonneg (hpositive l) ((preparation_normalized l.1 l.2).1 s))
  · have htotal : total (chosenMixture w) = ∑ l, w l * total (preparation l.1 l.2) := by
      simp only [total, chosenMixture, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
    rw [htotal]
    have hp (l : Label) : total (preparation l.1 l.2) = 1 := (preparation_normalized l.1 l.2).2
    simpa only [hp, mul_one] using hsum

theorem H_preserves_chosen_mixtures (ρ : Local) (hρ : IsChosenMixture ρ) :
    IsChosenMixture (H ρ) := by
  obtain ⟨w, hw, hsum, rfl⟩ := hρ
  let w' : Label → ℚ := fun l => w (labelPermutation.symm l)
  refine ⟨w', fun l => hw _, ?_, ?_⟩
  · exact (labelPermutation.symm.sum_comp w).trans hsum
  · calc
      H (chosenMixture w) = ∑ l, w l • preparation (labelPermutation l).1 (labelPermutation l).2 := by
        simp only [chosenMixture, map_sum, map_smul, H_preparation]
      _ = chosenMixture w' := by
        apply Fintype.sum_equiv labelPermutation
        intro l
        simp only [w', Equiv.symm_apply_apply]

theorem H_point_mass_negative : H (pointMass (false, false)) (true, true) = -1 / 2 := by
  norm_num [H_apply, total, coordinates, character, pointMass, sign,
    Fintype.sum_prod_type]

theorem H_not_positive_on_full_simplex :
    ¬ (∀ ρ : Local, normalized ρ → nonnegative (H ρ)) := by
  intro h
  have hp := h _ (pointMass_normalized (false, false)) (true, true)
  rw [H_point_mass_negative] at hp
  norm_num at hp

def productPreparation (ρ σ : Local) : Joint := fun s => ρ s.1 * σ s.2

theorem product_normalized (ρ σ : Local) (hρ : normalized ρ) (hσ : normalized σ) :
    normalized (productPreparation ρ σ) := by
  constructor
  · rintro ⟨a, b⟩
    exact mul_nonneg (hρ.1 a) (hσ.1 b)
  · have htotal : total (productPreparation ρ σ) = total ρ * total σ := by
      simp [total, productPreparation, Fintype.sum_prod_type]
      ring
    rw [htotal, hρ.2, hσ.2, one_mul]

/-- A small positive preparation grammar, entirely within the full simplex. -/
inductive GeneratedPreparation : Joint → Prop
  | chosenProduct (axisA axisB : Fin 3) (outA outB : Bool) :
      GeneratedPreparation (productPreparation (preparation axisA outA) (preparation axisB outB))
  | cnot {ρ : Joint} : GeneratedPreparation ρ → GeneratedPreparation (G ρ)

theorem generated_preparation_normalized {ρ : Joint} (hρ : GeneratedPreparation ρ) :
    normalized ρ := by
  induction hρ with
  | chosenProduct axisA axisB outA outB =>
    exact product_normalized _ _ (preparation_normalized _ _) (preparation_normalized _ _)
  | cnot h ih => exact G_normalized _ ih

def input : Joint := productPreparation (preparation 0 false) (preparation 2 false)
def bell : Joint := G input

theorem bell_generated : GeneratedPreparation bell :=
  .cnot (.chosenProduct 0 2 false false)

theorem bell_normalized : normalized bell := generated_preparation_normalized bell_generated

theorem bell_diagonal (a b : Ω) : bell (a, b) = if a = b then 1 / 4 else 0 := by
  rcases a with ⟨qA, pA⟩
  rcases b with ⟨qB, pB⟩
  cases qA <;> cases pA <;> cases qB <;> cases pB <;>
    norm_num [bell, input, productPreparation, G, permutationAction, cnotPermutation,
      preparation]

def f (s : Ω) : Ω := (!s.2, !s.1)

def K : Module.End ℚ Local := Jy * W

def kPermutation : Ω ≃ Ω where
  toFun := f
  invFun := f
  left_inv := by rintro ⟨q, p⟩; cases q <;> cases p <;> rfl
  right_inv := by rintro ⟨q, p⟩; cases q <;> cases p <;> rfl

theorem K_permutation : K = (permutationAction kPermutation).toLinearMap := rfl

theorem liftA_K_permutation :
    liftA K = (permutationAction (Equiv.prodCongr kPermutation (Equiv.refl Ω))).toLinearMap := rfl

def eventCondition (s : Ω × Ω) : Prop := s.1.2 = false ∧ s.2.1 = false

instance (s : Ω × Ω) : Decidable (eventCondition s) := inferInstanceAs
  (Decidable (s.1.2 = false ∧ s.2.1 = false))

def eventEffect : Joint →ₗ[ℚ] ℚ where
  toFun ρ := ∑ s, if eventCondition s then ρ s else 0
  map_add' := by
    intro ρ σ
    change (∑ s, if eventCondition s then ρ s + σ s else 0) =
      (∑ s, if eventCondition s then ρ s else 0) + (∑ s, if eventCondition s then σ s else 0)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : eventCondition s <;> simp [h]
  map_smul' := by
    intro c ρ
    change (∑ s, if eventCondition s then c * ρ s else 0) =
      c * (∑ s, if eventCondition s then ρ s else 0)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : eventCondition s <;> simp [h]

theorem event_nonnegative (ρ : Joint) (hρ : nonnegative ρ) : 0 ≤ eventEffect ρ := by
  change 0 ≤ ∑ s, if eventCondition s then ρ s else 0
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact hρ s
  · exact le_rfl

theorem event_le_total (ρ : Joint) (hρ : nonnegative ρ) : eventEffect ρ ≤ total ρ := by
  change (∑ s, if eventCondition s then ρ s else 0) ≤ ∑ s, ρ s
  apply Finset.sum_le_sum
  intro s _
  split_ifs
  · exact le_rfl
  · exact hρ s

/-- The readout protocol consists of the first-wire positive permutation,
the classical CNOT, and the stated binary product event. -/
def selectedEffect : Joint →ₗ[ℚ] ℚ := eventEffect.comp (G.comp (liftA K))

theorem selected_effect_valid (ρ : Joint) (hρ : normalized ρ) :
    0 ≤ selectedEffect ρ ∧ selectedEffect ρ ≤ 1 := by
  have hk : normalized (liftA K ρ) := by
    rw [liftA_K_permutation]
    exact permutation_normalized _ _ hρ
  have hg := G_normalized _ hk
  exact ⟨event_nonnegative _ hg.1, (event_le_total _ hg.1).trans_eq hg.2⟩

/-- The diagonal support relation follows from the defined event protocol. -/
theorem selected_effect_support (ρ : Joint) :
    selectedEffect ρ = ∑ s : Ω × Ω, if s.1 = f s.2 then ρ s else 0 := by
  simp [selectedEffect, eventEffect, eventCondition, G, K, Jy, W, liftA,
    permutationAction, cnotPermutation, flipBoth, swapQP, f,
    Fintype.sum_prod_type]
  ring

theorem H_bell_support_entry (a b : Ω) (hab : a = f b) :
    (liftA H bell) (a, b) = -1 / 8 := by
  subst a
  change H (fun a => bell (a, b)) (f b) = -1 / 8
  rcases b with ⟨q, p⟩
  cases q <;> cases p <;>
    norm_num [H_apply, total, coordinates, character, sign, f,
      bell_diagonal, Fintype.sum_prod_type]

theorem H_extension_selected_effect : selectedEffect (liftA H bell) = -1 / 2 := by
  rw [selected_effect_support]
  calc
    _ = ∑ s : Ω × Ω, if s.1 = f s.2 then (-1 / 8 : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      split_ifs with h
      · exact H_bell_support_entry s.1 s.2 h
      · rfl
    _ = -1 / 2 := by norm_num [f, Fintype.sum_prod_type]

theorem H_extension_selected_effect_negative : selectedEffect (liftA H bell) < 0 := by
  rw [H_extension_selected_effect]
  norm_num

end

end IDT.QMClosure.ClassicalPhaseJointReadoutBoundary
