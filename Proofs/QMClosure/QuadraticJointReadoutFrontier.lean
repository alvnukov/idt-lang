import Proofs.QMClosure.PositiveQuadraticPolarization

namespace IDT.QMClosure.QuadraticJointReadoutFrontier

open PreparationRecordObstruction PreparationDisturbanceTradeoff
open QuadraticRecordRefinement PositiveQuadraticPolarization

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-!
Conditional compatible-weight-law frontier. Each record has a common global
positive-quadratic extension. Probabilities and stochastic responses are supplied;
no event actualization, detector update, phase invariance, or QM closure follows.
The only Euclidean algebra used below concerns real coefficients, not the carrier.
-/

variable {U : Type*} [AddCommGroup U]
variable {Ω : Type*} [Fintype Ω]

def firstScore (μ : Fin 4 → Ω → ℝ) (r : Ω → ℝ) : ℝ :=
  (marginal μ r 0 + marginal μ r 1 +
    (1 - marginal μ r 2) + (1 - marginal μ r 3)) / 4

def secondScore (μ : Fin 4 → Ω → ℝ) (r : Ω → ℝ) : ℝ :=
  (marginal μ r 0 + (1 - marginal μ r 1) +
    marginal μ r 2 + (1 - marginal μ r 3)) / 4

theorem preparation_rows {Q : U → ℝ} (h : PositiveQuadratic Q) (E F : U) :
    Q (preparations E F 0) = 4 * Q E + 4 * polarization Q E F + Q F ∧
    Q (preparations E F 1) = 4 * Q E - 4 * polarization Q E F + Q F ∧
    Q (preparations E F 2) = Q E + 4 * polarization Q E F + 4 * Q F ∧
    Q (preparations E F 3) = Q E - 4 * polarization Q E F + 4 * Q F := by
  have h0 := integer_coordinate_law h 2 1 E F
  have h1 := integer_coordinate_law h 2 (-1) E F
  have h2 := integer_coordinate_law h 1 2 E F
  have h3 := integer_coordinate_law h 1 (-2) E F
  norm_num [two_zsmul, preparations, sub_eq_add_neg] at h0 h1 h2 h3 ⊢
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Normalization at four points fixes the two diagonal totals and cross total. -/
theorem coefficient_totals (E F : U) (κ : ℝ)
    (f : Ω → U → ℝ) (hq : ∀ r, PositiveQuadratic (f r))
    (μ : Fin 4 → Ω → ℝ) (law : ProbabilityFamily μ)
    (hreal : ∀ a r, f r (preparations E F a) = 5 * κ * μ a r) :
    (∑ r, f r E) = κ ∧ (∑ r, f r F) = κ ∧
      (∑ r, polarization (f r) E F) = 0 := by
  have hn (a : Fin 4) : (∑ r, f r (preparations E F a)) = 5 * κ := by
    simp only [hreal, ← Finset.mul_sum, law.normalized, mul_one]
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  simp_rw [(preparation_rows (hq _) E F).1] at h0
  simp_rw [(preparation_rows (hq _) E F).2.1] at h1
  simp_rw [(preparation_rows (hq _) E F).2.2.1] at h2
  simp_rw [(preparation_rows (hq _) E F).2.2.2] at h3
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at h0 h1 h2 h3
  exact ⟨by linarith, by linarith, by linarith⟩

theorem coefficient_disk (α β γ z x : ℝ)
    (hcs : β^2 ≤ α * γ) (hz : 0 ≤ z ∧ z ≤ 1) (hx : 0 ≤ x ∧ x ≤ 1) :
    ((2*z-1)*(α-γ))^2 + ((2*x-1)*2*β)^2 ≤ (α+γ)^2 := by
  have hz' : (2*z-1)^2 ≤ 1 := by nlinarith
  have hx' : (2*x-1)^2 ≤ 1 := by nlinarith
  have hza := mul_le_mul_of_nonneg_right hz' (sq_nonneg (α-γ))
  have hxb := mul_le_mul_of_nonneg_right hx' (sq_nonneg (2*β))
  nlinarith

/-- Two-dimensional triangle inequality, purely in the real coefficient plane. -/
theorem disk_add (a b t c d u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (h : a^2+b^2 ≤ t^2) (k : c^2+d^2 ≤ u^2) :
    (a+c)^2+(b+d)^2 ≤ (t+u)^2 := by
  have hp : (a*c+b*d)^2 ≤ (t*u)^2 := by
    have h1 := mul_le_mul_of_nonneg_right h (sq_nonneg u)
    have h2 := mul_le_mul_of_nonneg_left k (add_nonneg (sq_nonneg a) (sq_nonneg b))
    nlinarith [sq_nonneg (a*d-b*c)]
  have hd : a*c+b*d ≤ t*u := by
    have htu := mul_nonneg ht hu
    nlinarith [sq_nonneg (a*c+b*d-t*u)]
  nlinarith

omit [Fintype Ω] in
theorem sum_disk (s : Finset Ω) (a b t : Ω → ℝ)
    (ht : ∀ r ∈ s, 0 ≤ t r) (hd : ∀ r ∈ s, (a r)^2+(b r)^2 ≤ (t r)^2) :
    (∑ r ∈ s, a r)^2+(∑ r ∈ s, b r)^2 ≤ (∑ r ∈ s, t r)^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert r s hr ih =>
    simp only [Finset.sum_insert hr]
    exact disk_add _ _ _ _ _ _ (ht r (Finset.mem_insert_self _ _))
      (Finset.sum_nonneg fun j hj => ht j (Finset.mem_insert_of_mem hj))
      (hd r (Finset.mem_insert_self _ _))
      (ih (fun j hj => ht j (Finset.mem_insert_of_mem hj))
        (fun j hj => hd j (Finset.mem_insert_of_mem hj)))

theorem score_coefficient_identities (E F : U) (κ : ℝ)
    (f : Ω → U → ℝ) (hq : ∀ r, PositiveQuadratic (f r))
    (μ : Fin 4 → Ω → ℝ) (law : ProbabilityFamily μ)
    (hreal : ∀ a r, f r (preparations E F a) = 5 * κ * μ a r)
    (rZ rX : Ω → ℝ) :
    10*κ*(2*firstScore μ rZ-1) =
      3 * ∑ r, (2*rZ r-1)*(f r E-f r F) ∧
    5*κ*(2*secondScore μ rX-1) =
      2 * ∑ r, (2*rX r-1)*2*polarization (f r) E F := by
  obtain ⟨ha, hc, hb⟩ := coefficient_totals E F κ f hq μ law hreal
  have hz (r : Ω) : 5*κ*(μ 0 r+μ 1 r-μ 2 r-μ 3 r) =
      6*(f r E-f r F) := by
    obtain ⟨h0,h1,h2,h3⟩ := preparation_rows (hq r) E F
    rw [hreal 0 r] at h0
    rw [hreal 1 r] at h1
    rw [hreal 2 r] at h2
    rw [hreal 3 r] at h3
    linarith
  have hx (r : Ω) : 5*κ*(μ 0 r-μ 1 r+μ 2 r-μ 3 r) =
      16*polarization (f r) E F := by
    obtain ⟨h0,h1,h2,h3⟩ := preparation_rows (hq r) E F
    rw [hreal 0 r] at h0
    rw [hreal 1 r] at h1
    rw [hreal 2 r] at h2
    rw [hreal 3 r] at h3
    linarith
  have hzs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun r _ => congrArg (· * rZ r) (hz r))
  have hxs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun r _ => congrArg (· * rX r) (hx r))
  have hza : (∑ r, (2*rZ r-1)*(f r E-f r F)) =
      2*(∑ r, f r E*rZ r)-2*(∑ r, f r F*rZ r)-(∑ r, f r E)+(∑ r, f r F) := by
    calc
      _ = ∑ r, (2*(f r E*rZ r)-2*(f r F*rZ r)-f r E+f r F) :=
        Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hxb : (∑ r, (2*rX r-1)*2*polarization (f r) E F) =
      4*(∑ r, polarization (f r) E F*rX r)-2*(∑ r, polarization (f r) E F) := by
    calc
      _ = ∑ r, (4*(polarization (f r) E F*rX r)-2*polarization (f r) E F) :=
        Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [mul_sub, mul_add, sub_mul, add_mul, mul_assoc] at hzs hxs
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hzs hxs
  rw [hza,hxb,ha,hc,hb]
  unfold firstScore secondScore marginal
  constructor <;> nlinarith

/-- Universal finite-record ellipse, with arbitrary fixed stochastic responses. -/
theorem joint_score_ellipse (E F : U) (κ : ℝ) (hκ : 0 < κ)
    (f : Ω → U → ℝ) (hq : ∀ r, PositiveQuadratic (f r))
    (μ : Fin 4 → Ω → ℝ) (law : ProbabilityFamily μ)
    (hreal : ∀ a r, f r (preparations E F a) = 5 * κ * μ a r)
    (rZ rX : Ω → ℝ) (hZ : Response rZ) (hX : Response rX) :
    400*(2*firstScore μ rZ-1)^2+225*(2*secondScore μ rX-1)^2 ≤ 144 := by
  obtain ⟨ha,hc,hb⟩ := coefficient_totals E F κ f hq μ law hreal
  obtain ⟨hz,hx⟩ := score_coefficient_identities E F κ f hq μ law hreal rZ rX
  have hd := sum_disk Finset.univ
    (fun r => (2*rZ r-1)*(f r E-f r F))
    (fun r => (2*rX r-1)*2*polarization (f r) E F)
    (fun r => f r E+f r F)
    (fun r _ => add_nonneg ((hq r).nonnegative E) ((hq r).nonnegative F))
    (fun r _ => coefficient_disk _ _ _ _ _
      (cauchy_schwarz (hq r) E F) (hZ r) (hX r))
  simp only [Finset.sum_add_distrib, ha, hc] at hd
  have hκ2 : 0 < κ^2 := sq_pos_of_pos hκ
  have hz2 := congrArg (fun v : ℝ => v^2) hz
  have hx2 := congrArg (fun v : ℝ => v^2) hx
  apply (mul_le_mul_iff_right₀ hκ2).mp
  nlinarith

/-- Existing four-record stage scores are the deterministic-response instance. -/
theorem sequential_joint_score_ellipse (E F : U) (κ : ℝ) (hκ : 0 < κ)
    (f : Fin 4 → U → ℝ) (hq : ∀ r, PositiveQuadratic (f r))
    (μ : Fin 4 → Fin 4 → ℝ) (law : ProbabilityFamily μ)
    (hreal : ∀ a r, f r (preparations E F a) = 5 * κ * μ a r) :
    400*(2*firstSuccess μ-1)^2+225*(2*secondSuccess μ-1)^2 ≤ 144 :=
  joint_score_ellipse E F κ hκ f hq μ law hreal recordZ recordX
    record_responses.1 record_responses.2

omit [Fintype Ω] in
/-- Parity equivalence is a consequence of common quadratic record extensions. -/
theorem parity_equivalent (E F : U) (κ : ℝ) (hκ : 0 < κ)
    (f : Ω → U → ℝ) (hq : ∀ r, PositiveQuadratic (f r))
    (μ : Fin 4 → Ω → ℝ)
    (hreal : ∀ a r, f r (preparations E F a) = 5 * κ * μ a r) :
    ParityEquivalent μ := by
  intro r
  obtain ⟨h0,h1,h2,h3⟩ := preparation_rows (hq r) E F
  rw [hreal 0 r] at h0
  rw [hreal 1 r] at h1
  rw [hreal 2 r] at h2
  rw [hreal 3 r] at h3
  nlinarith

theorem ellipse_endpoint (A B : ℝ)
    (h : 400*(2*A-1)^2+225*(2*B-1)^2 ≤ 144) (ha : A = 4/5) : B = 1/2 := by
  rw [ha] at h
  nlinarith [sq_nonneg (2*B-1)]

theorem ellipse_second_upper (A B : ℝ)
    (h : 400*(2*A-1)^2+225*(2*B-1)^2 ≤ 144) : B ≤ 9/10 := by
  nlinarith [sq_nonneg (2*A-1)]

/-- The ellipse improves the calibrated endpoint, not the best mean-stage bound. -/
theorem ellipse_sum_upper (A B : ℝ)
    (h : 400*(2*A-1)^2+225*(2*B-1)^2 ≤ 144) : A+B ≤ 3/2 := by
  nlinarith [sq_nonneg (16*(2*A-1)-9*(2*B-1)),sq_nonneg (2*A+2*B-3)]

theorem disturbed_scores_violate_ellipse :
    144 < 400*(2*firstSuccess disturbedFamily-1)^2+
      225*(2*secondSuccess disturbedFamily-1)^2 := by
  rw [firstSuccess_eq_of_calibrated _ disturbedFamily_first_calibrated,
    disturbedFamily_secondSuccess]
  norm_num

theorem firstScore_error_lower (μ : Fin 4 → Ω → ℝ) (r : Ω → ℝ) :
    4/5-meanMarginalError μ r targetZ ≤ firstScore μ r := by
  have h0 := neg_le_abs (marginal μ r 0-targetZ 0)
  have h1 := neg_le_abs (marginal μ r 1-targetZ 1)
  have h2 := le_abs_self (marginal μ r 2-targetZ 2)
  have h3 := le_abs_self (marginal μ r 3-targetZ 3)
  norm_num [targetZ] at h0 h1 h2 h3
  norm_num [firstScore,meanMarginalError,Fin.sum_univ_succ,targetZ]
  have hlast : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  simp only [hlast]
  linarith

theorem secondScore_error_lower (μ : Fin 4 → Ω → ℝ) (r : Ω → ℝ) :
    9/10-secondScore μ r ≤ meanMarginalError μ r targetX := by
  have h0 := neg_le_abs (marginal μ r 0-targetX 0)
  have h1 := le_abs_self (marginal μ r 1-targetX 1)
  have h2 := neg_le_abs (marginal μ r 2-targetX 2)
  have h3 := le_abs_self (marginal μ r 3-targetX 3)
  norm_num [targetX] at h0 h1 h2 h3
  norm_num [secondScore,meanMarginalError,Fin.sum_univ_succ,targetX]
  have hlast : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  simp only [hlast]
  linarith

theorem ellipse_robust_upper (A B ε : ℝ)
    (h : 400*(2*A-1)^2+225*(2*B-1)^2 ≤ 144)
    (he : 0 ≤ ε ∧ ε ≤ 3/10) (ha : 4/5-ε ≤ A) :
    B ≤ 1/2+2/5*Real.sqrt (1-(1-10*ε/3)^2) := by
  have hv : 0 ≤ 1-(1-10*ε/3)^2 := by nlinarith
  have hs := Real.sq_sqrt hv
  have hn := Real.sqrt_nonneg (1-(1-10*ε/3)^2)
  have hl : (3/5-2*ε)^2 ≤ (2*A-1)^2 := by nlinarith
  nlinarith [sq_nonneg (2*B-1-4/5*Real.sqrt (1-(1-10*ε/3)^2))]

/-- Robust marginal-error consequence for the stated epsilon range only. -/
theorem marginal_error_frontier (E F : U) (κ : ℝ) (hκ : 0 < κ)
    (f : Ω → U → ℝ) (hq : ∀ r, PositiveQuadratic (f r))
    (μ : Fin 4 → Ω → ℝ) (law : ProbabilityFamily μ)
    (hreal : ∀ a r, f r (preparations E F a) = 5 * κ * μ a r)
    (rZ rX : Ω → ℝ) (hZ : Response rZ) (hX : Response rX)
    (ε : ℝ) (he : 0 ≤ ε ∧ ε ≤ 3/10)
    (herr : meanMarginalError μ rZ targetZ ≤ ε) :
    secondScore μ rX ≤ 1/2+2/5*Real.sqrt (1-(1-10*ε/3)^2) ∧
    2/5*(1-Real.sqrt (1-(1-10*ε/3)^2)) ≤ meanMarginalError μ rX targetX := by
  have ha := firstScore_error_lower μ rZ
  have hb := ellipse_robust_upper _ _ ε
    (joint_score_ellipse E F κ hκ f hq μ law hreal rZ rX hZ hX) he (by linarith)
  exact ⟨hb,by have := secondScore_error_lower μ rX; linarith⟩

end
end IDT.QMClosure.QuadraticJointReadoutFrontier
