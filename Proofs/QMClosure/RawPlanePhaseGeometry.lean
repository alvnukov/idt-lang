import Proofs.QMClosure.RawPlanePhaseFamily

/-!
# Ordinary complex two-plane geometry for the phase family

The parameter is attached to the actual complex span of the input pair.
At dependent pairs every member of the phase family agrees with the native
operation. No physical primitive interpretation is asserted.
-/

namespace IDT.QMClosure.RawPlanePhaseGeometry

noncomputable section

open RawPlanePhaseFamily
open scoped Topology

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

def wedge (x y : Vec) : Vec :=
  ![x 1 * y 2 - x 2 * y 1,
    x 2 * y 0 - x 0 * y 2,
    x 0 * y 1 - x 1 * y 0]

def parameter (x y : Vec) : ℝ :=
  (Complex.normSq (wedge x y 0) + Complex.normSq (wedge x y 1)) / W (wedge x y)

/-- Membership in the ordinary complex linear span, with no geometry witness. -/
def InPlane (x y z : Vec) : Prop := ∃ r s : ℂ, z = r • x + s • y

theorem wedge_change_basis (x y : Vec) (r s t u : ℂ) :
    wedge (r • x + s • y) (t • x + u • y) = (r * u - s * t) • wedge x y := by
  ext i
  fin_cases i <;> simp [wedge, Pi.smul_apply, smul_eq_mul] <;> ring

theorem wedge_swap (x y : Vec) : wedge y x = -wedge x y := by
  ext i
  fin_cases i <;> simp [wedge] <;> ring

theorem parameter_smul_wedge (v : Vec) (c : ℂ) (hc : c ≠ 0) :
    (Complex.normSq ((c • v) 0) + Complex.normSq ((c • v) 1)) / W (c • v) =
      (Complex.normSq (v 0) + Complex.normSq (v 1)) / W v := by
  have hn : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, W_smul]
  rw [← mul_add, mul_div_mul_left _ _ hn]

theorem parameter_change_basis (x y : Vec) (r s t u : ℂ)
    (hdet : r * u - s * t ≠ 0) :
    parameter (r • x + s • y) (t • x + u • y) = parameter x y := by
  unfold parameter
  rw [wedge_change_basis]
  exact parameter_smul_wedge _ _ hdet

theorem parameter_swap (x y : Vec) : parameter y x = parameter x y := by
  simpa using parameter_change_basis x y 0 1 1 0 (by norm_num)

theorem parameter_nonnegative (x y : Vec) : 0 ≤ parameter x y := by
  exact div_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (W_nonnegative _)

theorem parameter_le_one (x y : Vec) : parameter x y ≤ 1 := by
  apply div_le_one_of_le₀
  · unfold W
    exact le_add_of_nonneg_right (Complex.normSq_nonneg _)
  · exact W_nonnegative _

theorem parameter_of_wedge_eq_zero {x y : Vec} (h : wedge x y = 0) :
    parameter x y = 0 := by
  simp [parameter, h]

theorem continuous_wedge : Continuous (fun p : Vec × Vec => wedge p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [wedge] <;> fun_prop

theorem continuous_parameter_at (p : Vec × Vec) (hp : wedge p.1 p.2 ≠ 0) :
    ContinuousAt (fun q : Vec × Vec => parameter q.1 q.2) p := by
  have hw : W (wedge p.1 p.2) ≠ 0 := by
    exact fun he => hp ((W_eq_zero_iff _).mp he)
  unfold parameter
  have hn : Continuous (fun q : Vec × Vec =>
      Complex.normSq (wedge q.1 q.2 0) + Complex.normSq (wedge q.1 q.2 1)) :=
    ((Complex.continuous_normSq.comp ((continuous_apply 0).comp
      continuous_wedge)).add (Complex.continuous_normSq.comp
        ((continuous_apply 1).comp continuous_wedge)))
  exact hn.continuousAt.div (continuous_W.comp continuous_wedge).continuousAt hw

theorem wedge_eq_zero_dependent {x y : Vec} (h : wedge x y = 0) :
    ∃ z : Vec, ∃ c d : ℂ, x = c • z ∧ y = d • z := by
  have h12 : x 1 * y 2 - x 2 * y 1 = 0 := by
    simpa [wedge] using congrFun h 0
  have h20 : x 2 * y 0 - x 0 * y 2 = 0 := by
    simpa [wedge] using congrFun h 1
  have h01 : x 0 * y 1 - x 1 * y 0 = 0 := by
    simpa [wedge] using congrFun h 2
  by_cases hx0 : x 0 = 0
  · by_cases hx1 : x 1 = 0
    · by_cases hx2 : x 2 = 0
      · refine ⟨y, 0, 1, ?_, by simp⟩
        ext i
        fin_cases i <;> simp [hx0, hx1, hx2]
      · refine ⟨x, 1, y 2 / x 2, by simp, ?_⟩
        ext i
        fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul]
        · change y 0 = y 2 / x 2 * x 0
          field_simp
          linear_combination h20
        · change y 1 = y 2 / x 2 * x 1
          field_simp
          linear_combination -h12
        · change y 2 = y 2 / x 2 * x 2
          field_simp
    · refine ⟨x, 1, y 1 / x 1, by simp, ?_⟩
      ext i
      fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul]
      · change y 0 = y 1 / x 1 * x 0
        field_simp
        linear_combination -h01
      · change y 1 = y 1 / x 1 * x 1
        field_simp
      · change y 2 = y 1 / x 1 * x 2
        field_simp
        linear_combination h12
  · refine ⟨x, 1, y 0 / x 0, by simp, ?_⟩
    ext i
    fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul]
    · change y 0 = y 0 / x 0 * x 0
      field_simp
    · change y 1 = y 0 / x 0 * x 1
      field_simp
      linear_combination h01
    · change y 2 = y 0 / x 0 * x 2
      field_simp
      linear_combination -h20

theorem native_smul_same (z : Vec) (c d : ℂ) :
    native (c • z) (d • z) = (a * c + b * d) • z := by
  simp [native, smul_smul, add_smul]

/-- The entire fixed-parameter family glues along the rank-one locus. -/
theorem familyM_of_dependent (t : ℝ) {x y : Vec} (h : wedge x y = 0) :
    familyM t x y = native x y := by
  rcases wedge_eq_zero_dependent h with ⟨z, c, d, rfl, rfl⟩
  rw [familyM, H_smul, H_smul, native_smul_same, H_smul, H_H_neg,
    native_smul_same]

theorem familyOperation_of_dependent (t : ℝ) {p : Vec × Vec}
    (h : wedge p.1 p.2 = 0) :
    familyOperation t p = (native p.1 p.2, native p.2 p.1) := by
  have hs : wedge p.2 p.1 = 0 := by rw [wedge_swap, h, neg_zero]
  simp only [familyOperation, familyM_of_dependent _ h, familyM_of_dependent _ hs]

theorem inPlane_left (x y : Vec) : InPlane x y x := by
  exact ⟨1, 0, by simp⟩

theorem inPlane_right (x y : Vec) : InPlane x y y := by
  exact ⟨0, 1, by simp⟩

theorem inPlane_zero (x y : Vec) : InPlane x y 0 := by
  exact ⟨0, 0, by simp⟩

theorem inPlane_smul {x y z : Vec} (c : ℂ) (hz : InPlane x y z) :
    InPlane x y (c • z) := by
  rcases hz with ⟨r, s, rfl⟩
  exact ⟨c * r, c * s, by simp [smul_add, smul_smul]⟩

theorem inPlane_add {x y z w : Vec} (hz : InPlane x y z) (hw : InPlane x y w) :
    InPlane x y (z + w) := by
  rcases hz with ⟨r, s, rfl⟩
  rcases hw with ⟨t, u, rfl⟩
  exact ⟨r + t, s + u, by simp [add_smul]; abel⟩

theorem inPlane_H {x y z : Vec} (t : ℝ) (hz : InPlane x y z) :
    InPlane x y (H t z) := by
  exact inPlane_smul _ hz

theorem inPlane_native {x y z w : Vec} (hz : InPlane x y z) (hw : InPlane x y w) :
    InPlane x y (native z w) := by
  exact inPlane_add (inPlane_smul _ hz) (inPlane_smul _ hw)

theorem inPlane_familyM {x y z w : Vec} (t : ℝ)
    (hz : InPlane x y z) (hw : InPlane x y w) : InPlane x y (familyM t z w) := by
  exact inPlane_H _ (inPlane_native (inPlane_H _ hz) (inPlane_H _ hw))

theorem parameter_eq_or_dependent {x y z w : Vec}
    (hz : InPlane x y z) (hw : InPlane x y w) :
    parameter z w = parameter x y ∨ wedge z w = 0 := by
  rcases hz with ⟨r, s, rfl⟩
  rcases hw with ⟨t, u, rfl⟩
  by_cases hdet : r * u - s * t = 0
  · right
    rw [wedge_change_basis, hdet, zero_smul]
  · exact Or.inl (parameter_change_basis _ _ _ _ _ _ hdet)

/-- Every pair in one plane is evaluated by the same fixed-parameter operation. -/
theorem familyM_parameter_locality {x y z w : Vec}
    (hz : InPlane x y z) (hw : InPlane x y w) :
    familyM (parameter z w) z w = familyM (parameter x y) z w := by
  rcases parameter_eq_or_dependent hz hw with hp | hd
  · rw [hp]
  · rw [familyM_of_dependent _ hd, familyM_of_dependent _ hd]

end
end IDT.QMClosure.RawPlanePhaseGeometry
