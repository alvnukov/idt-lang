import Proofs.QMClosure.FiniteCovariantNoiseWall

/-!
# Binary classical noise under an exact exchange root

The comparison is rational total variation of classical joint distributions.
No coherent amplitude, detector calibration, or outcome-origin claim is made.
-/

namespace IDT.QMClosure.BinaryNoiseMixingWall

noncomputable section

open RationalFiniteDistribution FiniteCovariantNoiseWall

variable {V : Type*}

/-- The mixed output escapes the four binary input pairs. -/
theorem mixed_output_outside_binary (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap) (hdiag : ∀ x, F (x, x) = (x, x))
    {a b : V} (hab : a ≠ b) :
    ¬ ((F (a, b)).1 = a ∨ (F (a, b)).1 = b) ∨
      ¬ ((F (a, b)).2 = a ∨ (F (a, b)).2 = b) := by
  by_contra hh
  push Not at hh
  rcases hh with ⟨hu, hv⟩
  have haa : F (a, b) ≠ (a, a) := by
    intro h
    have heq := square_swap_injective F hsquare (h.trans (hdiag a).symm)
    exact hab (congrArg Prod.snd heq).symm
  have hbb : F (a, b) ≠ (b, b) := by
    intro h
    have heq := square_swap_injective F hsquare (h.trans (hdiag b).symm)
    exact hab (congrArg Prod.fst heq)
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact haa (Prod.ext hu hv)
  · exact (mixed_output_not_routing F hsquare hab).1 (Prod.ext hu hv)
  · exact (mixed_output_not_routing F hsquare hab).2 (Prod.ext hu hv)
  · exact hbb (Prod.ext hu hv)

private theorem binary_product_coeff (a b : V) (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (product (mixture p hp hp' (dirac a) (dirac b))
      (mixture p hp hp' (dirac a) (dirac b))).coeff =
      (p * p) • Finsupp.single (a, a) 1 +
      (p * (1 - p)) • Finsupp.single (a, b) 1 +
      (p * (1 - p)) • Finsupp.single (b, a) 1 +
      ((1 - p) * (1 - p)) • Finsupp.single (b, b) 1 := by
  simp only [product, map, bind_coeff, mixture, dirac, map_add, map_smul, extend_single, Function.comp_apply]
  module

private theorem map_binary_product_coeff (F : V × V → V × V) (a b : V)
    (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (map F (product (mixture p hp hp' (dirac a) (dirac b))
      (mixture p hp hp' (dirac a) (dirac b)))).coeff =
      (p * p) • Finsupp.single (F (a, a)) 1 +
      (p * (1 - p)) • Finsupp.single (F (a, b)) 1 +
      (p * (1 - p)) • Finsupp.single (F (b, a)) 1 +
      ((1 - p) * (1 - p)) • Finsupp.single (F (b, b)) 1 := by
  change extend (fun v => (dirac (F v)).coeff) _ = _
  rw [binary_product_coeff]
  simp only [map_add, map_smul, dirac, extend_single]
  module

private theorem l1_four_atoms {X : Type*} (u v x y : X)
    (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (q : ℚ) (hq : 0 ≤ q) :
    l1 (q • Finsupp.single u 1 + q • Finsupp.single v 1 -
      q • Finsupp.single x 1 - q • Finsupp.single y 1) = 4 * q := by
  classical
  let d : X →₀ ℚ := q • Finsupp.single u 1 + q • Finsupp.single v 1 -
    q • Finsupp.single x 1 - q • Finsupp.single y 1
  have hs : d.support ⊆ {u, v, x, y} := by
    intro z hz
    by_contra hh
    have hz' : z ≠ u ∧ z ≠ v ∧ z ≠ x ∧ z ≠ y := by simpa using hh
    have hd : d z = 0 := by simp [d, hz'.1, hz'.2.1, hz'.2.2.1, hz'.2.2.2]
    exact Finsupp.mem_support_iff.mp hz hd
  change d.sum (fun _ q => |q|) = _
  rw [Finsupp.sum_of_support_subset d hs _ (by simp)]
  simp [d, huv, hux, huy, hvx, hvy, hxy, Ne.symm huv, Ne.symm hux, Ne.symm huy,
    Ne.symm hvx, Ne.symm hvy, Ne.symm hxy, abs_of_nonneg hq]
  ring

/-- Exact defect for every binary mixing weight, including the endpoints. -/
theorem binary_noise_tv_exact (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap) (hdiag : ∀ x, F (x, x) = (x, x))
    {a b : V} (hab : a ≠ b) (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    let μ := mixture p hp hp' (dirac a) (dirac b)
    tv (map F (product μ μ)) (product μ μ) = 2 * p * (1 - p) := by
  dsimp only
  unfold tv
  rw [map_binary_product_coeff, binary_product_coeff, hdiag a, hdiag b]
  have hdiff :
      (p * p) • Finsupp.single (a, a) (1 : ℚ) +
        (p * (1 - p)) • Finsupp.single (F (a, b)) 1 +
        (p * (1 - p)) • Finsupp.single (F (b, a)) 1 +
        ((1 - p) * (1 - p)) • Finsupp.single (b, b) 1 -
        ((p * p) • Finsupp.single (a, a) 1 +
        (p * (1 - p)) • Finsupp.single (a, b) 1 +
        (p * (1 - p)) • Finsupp.single (b, a) 1 +
        ((1 - p) * (1 - p)) • Finsupp.single (b, b) 1) =
      (p * (1 - p)) • Finsupp.single (F (a, b)) 1 +
        (p * (1 - p)) • Finsupp.single (F (b, a)) 1 -
        (p * (1 - p)) • Finsupp.single (a, b) 1 -
        (p * (1 - p)) • Finsupp.single (b, a) 1 := by abel
  rw [hdiff, l1_four_atoms]
  · ring
  · exact fun h => hab (congrArg Prod.fst (square_swap_injective F hsquare h))
  · exact (mixed_output_not_routing F hsquare hab).1
  · exact (mixed_output_not_routing F hsquare hab).2
  · exact (mixed_output_not_routing F hsquare hab.symm).2
  · exact (mixed_output_not_routing F hsquare hab.symm).1
  · exact fun h => hab (congrArg Prod.fst h)
  · exact mul_nonneg hp (sub_nonneg.mpr hp')

/-- Balanced binary input has total-variation defect exactly one half. -/
theorem balanced_binary_noise_tv (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap) (hdiag : ∀ x, F (x, x) = (x, x))
    {a b : V} (hab : a ≠ b) :
    let μ := mixture (1 / 2) (by norm_num) (by norm_num) (dirac a) (dirac b)
    tv (map F (product μ μ)) (product μ μ) = 1 / 2 := by
  convert binary_noise_tv_exact F hsquare hdiag hab (1 / 2) (by norm_num) (by norm_num) using 1; norm_num

private theorem product_coeff (μ ν : FinDist V) (a b : V) :
    (product μ ν).coeff (a, b) = μ.coeff a * ν.coeff b := by
  classical
  by_cases ha : μ.coeff a = 0 <;> by_cases hb : ν.coeff b = 0 <;>
    simp [product, map, bind_coeff, extend_apply, dirac, Finsupp.single_apply, Finsupp.sum, ite_and, ha, hb]

/-- Every interior binary input yields a joint output outside all products,
including products with unequal factors. -/
theorem binary_noise_not_product (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap) (hdiag : ∀ x, F (x, x) = (x, x))
    {a b : V} (hab : a ≠ b) (p : ℚ) (hp : 0 < p) (hp' : p < 1) :
    let μ := mixture p (le_of_lt hp) (le_of_lt hp') (dirac a) (dirac b)
    ∀ ν ρ : FinDist V, map F (product μ μ) ≠ product ν ρ := by
  dsimp only
  intro ν ρ heq
  have hinj := square_swap_injective F hsquare
  have haa : F (a, b) ≠ (a, a) := fun h => hab (congrArg Prod.snd (hinj (h.trans (hdiag a).symm))).symm
  have hbb : F (a, b) ≠ (b, b) := fun h => hab (congrArg Prod.fst (hinj (h.trans (hdiag b).symm)))
  have hbaa : F (b, a) ≠ (a, a) := fun h => hab (congrArg Prod.fst (hinj (h.trans (hdiag a).symm))).symm
  have hbba : F (b, a) ≠ (b, b) := fun h => hab (congrArg Prod.snd (hinj (h.trans (hdiag b).symm)))
  have habpair : (a, b) ≠ (b, a) := fun h => hab (congrArg Prod.fst h)
  have hc := congrArg FinDist.coeff heq
  rw [map_binary_product_coeff, hdiag a, hdiag b] at hc
  have hAA := congrArg (fun d : V × V →₀ ℚ => d (a, a)) hc
  have hBB := congrArg (fun d : V × V →₀ ℚ => d (b, b)) hc
  have hAB := congrArg (fun d : V × V →₀ ℚ => d (a, b)) hc
  have hBA := congrArg (fun d : V × V →₀ ℚ => d (b, a)) hc
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hAA hBB hAB hBA
  simp [hab, hab.symm, haa, hbb, hbaa, hbba,
    (mixed_output_not_routing F hsquare hab).1, (mixed_output_not_routing F hsquare hab).2,
    (mixed_output_not_routing F hsquare hab.symm).1, (mixed_output_not_routing F hsquare hab.symm).2,
    product_coeff, -mul_eq_zero, -zero_eq_mul] at hAA hBB hAB hBA
  have hrect : (ν.coeff a * ρ.coeff a) * (ν.coeff b * ρ.coeff b) =
      (ν.coeff a * ρ.coeff b) * (ν.coeff b * ρ.coeff a) := by ring
  rw [← hAA, ← hBB, ← hAB, ← hBA] at hrect
  nlinarith [mul_pos hp (sub_pos.mpr hp')]

end
end IDT.QMClosure.BinaryNoiseMixingWall
