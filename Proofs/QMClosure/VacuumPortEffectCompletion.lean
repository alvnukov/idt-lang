import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Two-coordinate completion with a fixed coordinate sum

These are coordinate geometry results over supplied complex vectors. The input
lift adds two zero coordinates; "vacuum" is only the name of that mathematical
embedding. The construction does not establish availability of physical ports,
an encoding bridge, a circuit implementing the completed vector, or a detector
probability law. In particular, it makes no exact finite-circuit or density
claim and does not derive QM from IDT primitives.
-/

namespace IDT.QMClosure.VacuumPortEffectCompletion

open scoped BigOperators

noncomputable section

def coordinateWeight {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

def overlap {ι : Type*} [Fintype ι] (v x : ι → ℂ) : ℂ :=
  ∑ i, star (v i) * x i

def deficit {n : ℕ} (ψ : Fin n → ℂ) (c : ℝ) : ℂ :=
  1 - (Real.sqrt c : ℂ) * ∑ i, ψ i

def completionOffset (d : ℂ) (c : ℝ) : ℝ :=
  Real.sqrt ((1 - c - Complex.normSq d / 2) / 2)

def completionAncilla (d : ℂ) (c : ℝ) : Fin 2 → ℂ :=
  ![d / 2 + (completionOffset d c : ℂ),
    d / 2 - (completionOffset d c : ℂ)]

def completedVector {n : ℕ} (ψ : Fin n → ℂ) (c : ℝ) : (Fin n ⊕ Fin 2) → ℂ :=
  Sum.elim (fun i => (Real.sqrt c : ℂ) * ψ i)
    (completionAncilla (deficit ψ c) c)

def vacuumInput {n : ℕ} (x : Fin n → ℂ) : (Fin n ⊕ Fin 2) → ℂ :=
  Sum.elim x (fun _ => 0)

theorem completionAncilla_sum (d : ℂ) (c : ℝ) :
    ∑ i, completionAncilla d c i = d := by
  simp [completionAncilla, Fin.sum_univ_two]

theorem completionAncilla_weight (d : ℂ) (c : ℝ)
    (hbudget : Complex.normSq d ≤ 2 * (1 - c)) :
    coordinateWeight (completionAncilla d c) = 1 - c := by
  have hnonneg : 0 ≤ (1 - c - Complex.normSq d / 2) / 2 := by linarith
  have hsquare := Real.sq_sqrt hnonneg
  change completionOffset d c ^ 2 = _ at hsquare
  simp only [coordinateWeight, completionAncilla, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im]
  simp only [Complex.normSq_apply] at hsquare
  nlinarith

theorem completedVector_sum {n : ℕ} (ψ : Fin n → ℂ) (c : ℝ) :
    ∑ i, completedVector ψ c i = 1 := by
  simp only [completedVector, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    ← Finset.mul_sum, completionAncilla_sum, deficit]
  ring

theorem completedVector_weight {n : ℕ} (ψ : Fin n → ℂ) (c : ℝ)
    (hc : 0 ≤ c) (hunit : coordinateWeight ψ = 1)
    (hbudget : Complex.normSq (deficit ψ c) ≤ 2 * (1 - c)) :
    coordinateWeight (completedVector ψ c) = 1 := by
  have hsqrt : Complex.normSq (Real.sqrt c : ℂ) = c := by
    simpa [Complex.normSq_ofReal, pow_two] using Real.sq_sqrt hc
  simp only [coordinateWeight, completedVector, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Complex.normSq_mul, hsqrt, ← Finset.mul_sum]
  change c * coordinateWeight ψ + coordinateWeight (completionAncilla (deficit ψ c) c) = 1
  rw [hunit, completionAncilla_weight _ _ hbudget]
  ring

/-- Compression against every complex input, without an input normalization assumption. -/
theorem completedVector_overlap {n : ℕ} (ψ x : Fin n → ℂ) (c : ℝ) :
    overlap (completedVector ψ c) (vacuumInput x) =
      (Real.sqrt c : ℂ) * overlap ψ x := by
  simp [overlap, completedVector, vacuumInput, Fintype.sum_sum_type,
    map_mul, mul_assoc, Finset.mul_sum]

theorem completedVector_overlap_weight {n : ℕ} (ψ x : Fin n → ℂ) (c : ℝ)
    (hc : 0 ≤ c) :
    Complex.normSq (overlap (completedVector ψ c) (vacuumInput x)) =
      c * Complex.normSq (overlap ψ x) := by
  rw [completedVector_overlap, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt hc]

/-- Sufficient budget criterion, with an explicit two-coordinate witness. -/
theorem exists_two_coordinate_completion {n : ℕ} (ψ : Fin n → ℂ) (c : ℝ)
    (hc : 0 ≤ c) (hunit : coordinateWeight ψ = 1)
    (hbudget : Complex.normSq (deficit ψ c) ≤ 2 * (1 - c)) :
    ∃ φ : (Fin n ⊕ Fin 2) → ℂ,
      (∑ i, φ i) = 1 ∧ coordinateWeight φ = 1 ∧
      (∀ i, φ (Sum.inl i) = (Real.sqrt c : ℂ) * ψ i) ∧
      (∀ x : Fin n → ℂ, Complex.normSq (overlap φ (vacuumInput x)) =
        c * Complex.normSq (overlap ψ x)) := by
  exact ⟨completedVector ψ c, completedVector_sum ψ c,
    completedVector_weight ψ c hc hunit hbudget, fun _ => rfl,
    fun x => completedVector_overlap_weight ψ x c hc⟩

/-- Cauchy--Schwarz in real and imaginary coordinates. -/
theorem normSq_sum_le_dimension {n : ℕ} (ψ : Fin n → ℂ) :
    Complex.normSq (∑ i, ψ i) ≤ (n : ℝ) * coordinateWeight ψ := by
  have hre := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) (fun i => (ψ i).re)
  have him := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) (fun i => (ψ i).im)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hre him
  have hreSum : (∑ i, ψ i).re = ∑ i, (ψ i).re :=
    map_sum Complex.reAddGroupHom ψ Finset.univ
  have himSum : (∑ i, ψ i).im = ∑ i, (ψ i).im :=
    map_sum Complex.imAddGroupHom ψ Finset.univ
  simp only [Complex.normSq_apply, hreSum, himSum,
    coordinateWeight, Finset.sum_add_distrib, ← pow_two]
  nlinarith

def uniformStrength (n : ℕ) : ℝ := 1 / (16 * (n : ℝ))

theorem uniformStrength_positive {n : ℕ} (hn : 1 ≤ n) : 0 < uniformStrength n := by
  unfold uniformStrength
  positivity

theorem uniformStrength_le_sixteenth {n : ℕ} (hn : 1 ≤ n) :
    uniformStrength n ≤ 1 / 16 := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold uniformStrength
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * n) (by norm_num)).2
  nlinarith

/-- One fixed positive strength per nonzero dimension works for every unit vector. -/
theorem uniformStrength_budget {n : ℕ} (hn : 1 ≤ n) (ψ : Fin n → ℂ)
    (hunit : coordinateWeight ψ = 1) :
    Complex.normSq (deficit ψ (uniformStrength n)) ≤
      2 * (1 - uniformStrength n) := by
  let c := uniformStrength n
  let z : ℂ := (Real.sqrt c : ℂ) * ∑ i, ψ i
  have hc : 0 ≤ c := (uniformStrength_positive hn).le
  have hcupper : c ≤ 1 / 16 := uniformStrength_le_sixteenth hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hcn : c * (n : ℝ) = 1 / 16 := by
    dsimp [c, uniformStrength]
    field_simp
  have hsum := normSq_sum_le_dimension ψ
  rw [hunit, mul_one] at hsum
  have hz : Complex.normSq z ≤ 1 / 16 := by
    have hsqrt : Complex.normSq (Real.sqrt c : ℂ) = c := by
      simpa [Complex.normSq_ofReal, pow_two] using Real.sq_sqrt hc
    dsimp [z]
    rw [Complex.normSq_mul, hsqrt]
    calc
      c * Complex.normSq (∑ i, ψ i) ≤ c * (n : ℝ) := mul_le_mul_of_nonneg_left hsum hc
      _ = 1 / 16 := hcn
  have hre : -(1 / 4 : ℝ) ≤ z.re := by
    have hresq := Complex.re_sq_le_normSq z
    nlinarith
  have hd : Complex.normSq (1 - z) ≤ 25 / 16 := by
    rw [Complex.normSq_sub]
    simp only [Complex.normSq_one, one_mul, Complex.conj_re]
    linarith
  change Complex.normSq (1 - z) ≤ 2 * (1 - c)
  linarith

theorem uniform_two_coordinate_completion {n : ℕ} (hn : 1 ≤ n)
    (ψ : Fin n → ℂ) (hunit : coordinateWeight ψ = 1) :
    0 < uniformStrength n ∧ uniformStrength n < 1 ∧
    ∃ φ : (Fin n ⊕ Fin 2) → ℂ,
      (∑ i, φ i) = 1 ∧ coordinateWeight φ = 1 ∧
      (∀ i, φ (Sum.inl i) = (Real.sqrt (uniformStrength n) : ℂ) * ψ i) ∧
      (∀ x : Fin n → ℂ, Complex.normSq (overlap φ (vacuumInput x)) =
        uniformStrength n * Complex.normSq (overlap ψ x)) := by
  refine ⟨uniformStrength_positive hn, ?_, ?_⟩
  · have h := uniformStrength_le_sixteenth hn
    linarith
  · exact exists_two_coordinate_completion ψ (uniformStrength n)
      (uniformStrength_positive hn).le hunit (uniformStrength_budget hn ψ hunit)

#print axioms exists_two_coordinate_completion
#print axioms uniform_two_coordinate_completion

end

end IDT.QMClosure.VacuumPortEffectCompletion
