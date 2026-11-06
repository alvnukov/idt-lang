import Proofs.QMClosure.QuadraticJointReadoutFrontier

namespace IDT.QMClosure.QuadraticJointReadoutControls

open PreparationRecordObstruction PreparationDisturbanceTradeoff
open QuadraticRecordRefinement QuadraticJointReadoutFrontier

noncomputable section
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-! Sharp controls on a supplied real plane. This is a compatible quadratic
weight construction, not a derivation of physical carrier or instrument data. -/

def signZ : Fin 4 → ℝ := ![1,1,-1,-1]
def signX : Fin 4 → ℝ := ![1,-1,1,-1]

def effect (x z : ℝ) (r : Fin 4) (v : ℝ × ℝ) : ℝ :=
  (v.1^2+v.2^2+signZ r*z*(v.1^2-v.2^2)+2*signX r*x*v.1*v.2)/4

theorem binary_nonnegative (α β γ a b : ℝ) (ha : 0 ≤ α) (hc : 0 ≤ γ)
    (hd : β^2 ≤ α*γ) : 0 ≤ α*a^2+2*β*a*b+γ*b^2 := by
  by_cases hz : α = 0
  · have hb : β = 0 := by nlinarith [sq_nonneg β]
    simp only [hz,hb,zero_mul,mul_zero,zero_add]
    exact mul_nonneg hc (sq_nonneg b)
  · have hp : 0 < α := lt_of_le_of_ne ha (Ne.symm hz)
    apply nonneg_of_mul_nonneg_left _ hp
    have ht := mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg b)
    nlinarith [sq_nonneg (α*a+β*b)]

theorem effect_positiveQuadratic (x z : ℝ) (h : x^2+z^2 ≤ 1) (r : Fin 4) :
    PositiveQuadratic (effect x z r) := by
  have hzp : -1 ≤ z ∧ z ≤ 1 := by constructor <;> nlinarith [sq_nonneg x]
  constructor
  · intro v
    have hp := binary_nonnegative ((1+signZ r*z)/4) (signX r*x/4)
      ((1-signZ r*z)/4) v.1 v.2
    have ha : 0 ≤ (1+signZ r*z)/4 := by
      fin_cases r <;> norm_num [signZ] <;> linarith
    have hc : 0 ≤ (1-signZ r*z)/4 := by
      fin_cases r <;> norm_num [signZ] <;> linarith
    have hd : (signX r*x/4)^2 ≤ ((1+signZ r*z)/4)*((1-signZ r*z)/4) := by
      fin_cases r <;> norm_num [signZ,signX] <;> nlinarith
    have hn := hp ha hc hd
    dsimp [effect]
    nlinarith
  · intro u v
    dsimp [effect]
    ring

theorem effect_total (x z : ℝ) (v : ℝ × ℝ) :
    ∑ r, effect x z r v = v.1^2+v.2^2 := by
  simp [effect,signZ,signX,Fin.sum_univ_succ]
  ring

def realPreparations : Fin 4 → ℝ × ℝ := ![(2,1),(2,-1),(1,2),(1,-2)]

def family (x z : ℝ) (a r : Fin 4) : ℝ := effect x z r (realPreparations a)/5

theorem family_probability (x z : ℝ) (h : x^2+z^2 ≤ 1) :
    ProbabilityFamily (family x z) := by
  constructor
  · intro a r
    exact div_nonneg ((effect_positiveQuadratic x z h r).nonnegative _) (by norm_num)
  · intro a
    unfold family
    rw [← Finset.sum_div,effect_total]
    fin_cases a <;> norm_num [realPreparations]

theorem family_realization (x z : ℝ) (a r : Fin 4) :
    effect x z r (preparations (1,0) (0,1) a) = 5*1*family x z a r := by
  have he : preparations (1,0) (0,1) a = realPreparations a := by
    fin_cases a <;> norm_num [preparations,realPreparations,Prod.ext_iff]
  rw [he]
  unfold family
  ring

theorem family_marginals (x z : ℝ) (a : Fin 4) :
    marginal (family x z) recordZ a = 1/2+3/10*signZ a*z ∧
    marginal (family x z) recordX a = 1/2+2/5*signX a*x := by
  fin_cases a <;> constructor <;>
    norm_num [marginal,family,effect,realPreparations,recordZ,recordX,
      signZ,signX,Fin.sum_univ_succ] <;> ring

theorem family_scores (x z : ℝ) :
    firstSuccess (family x z) = 1/2+3/10*z ∧
    secondSuccess (family x z) = 1/2+2/5*x := by
  unfold firstSuccess secondSuccess
  simp only [(family_marginals x z _).1,(family_marginals x z _).2]
  norm_num [signZ,signX]
  constructor <;> ring

/-- Every point of the closed score ellipse has a common positive-quadratic
four-record realization on the supplied real plane. -/
theorem whole_ellipse_attained (A B : ℝ)
    (h : 400*(2*A-1)^2+225*(2*B-1)^2 ≤ 144) :
    ∃ x z : ℝ, x^2+z^2 ≤ 1 ∧ ProbabilityFamily (family x z) ∧
      (∀ r, PositiveQuadratic (effect x z r)) ∧
      (∀ a r, effect x z r (preparations (1,0) (0,1) a) = 5*1*family x z a r) ∧
      firstSuccess (family x z) = A ∧ secondSuccess (family x z) = B := by
  let x := (5:ℝ)/2*(B-1/2)
  let z := (10:ℝ)/3*(A-1/2)
  have hd : x^2+z^2 ≤ 1 := by dsimp [x,z]; nlinarith
  refine ⟨x,z,hd,family_probability x z hd,effect_positiveQuadratic x z hd,
    family_realization x z,?_,?_⟩
  · rw [(family_scores x z).1]
    dsimp [z]
    ring
  · rw [(family_scores x z).2]
    dsimp [x]
    ring

theorem family_errors (x z : ℝ) (hx : x ≤ 1) (hz : z ≤ 1) :
    meanMarginalError (family x z) recordZ targetZ = 3/10*(1-z) ∧
    meanMarginalError (family x z) recordX targetX = 2/5*(1-x) := by
  have hez (a : Fin 4) :
      |marginal (family x z) recordZ a-targetZ a| = 3/10*(1-z) := by
    rw [(family_marginals x z a).1]
    fin_cases a <;> norm_num [signZ,targetZ]
    all_goals first
      | rw [abs_of_nonpos (by linarith)]; ring
      | rw [abs_of_nonneg (by linarith)]; ring
  have hex (a : Fin 4) :
      |marginal (family x z) recordX a-targetX a| = 2/5*(1-x) := by
    rw [(family_marginals x z a).2]
    fin_cases a <;> norm_num [signX,targetX]
    all_goals first
      | rw [abs_of_nonpos (by linarith)]; ring
      | rw [abs_of_nonneg (by linarith)]; ring
  constructor
  · simp [meanMarginalError,hez]
  · simp [meanMarginalError,hex]

/-- The robust frontier is attained with four globally quadratic record effects. -/
theorem robust_frontier_attained (ε : ℝ) (he : 0 ≤ ε ∧ ε ≤ 3/10) :
    let z := 1-10*ε/3
    let x := Real.sqrt (1-z^2)
    ProbabilityFamily (family x z) ∧
      (∀ r, PositiveQuadratic (effect x z r)) ∧
      (∀ a r, effect x z r (preparations (1,0) (0,1) a) = 5*1*family x z a r) ∧
      meanMarginalError (family x z) recordZ targetZ = ε ∧
      meanMarginalError (family x z) recordX targetX = 2/5*(1-x) ∧
      firstSuccess (family x z) = 4/5-ε ∧
      secondSuccess (family x z) = 1/2+2/5*x := by
  dsimp only
  let z := 1-10*ε/3
  let x := Real.sqrt (1-z^2)
  have hz : 0 ≤ z ∧ z ≤ 1 := by dsimp [z]; constructor <;> linarith
  have hv : 0 ≤ 1-z^2 := by nlinarith
  have hs : x^2 = 1-z^2 := Real.sq_sqrt hv
  have hd : x^2+z^2 ≤ 1 := by linarith
  have hx : x ≤ 1 := by nlinarith [sq_nonneg z]
  obtain ⟨hez,hex⟩ := family_errors x z hx hz.2
  refine ⟨family_probability x z hd,effect_positiveQuadratic x z hd,
    family_realization x z,?_,hex,?_,(family_scores x z).2⟩
  · rw [hez]
    dsimp [z]
    ring
  · rw [(family_scores x z).1]
    dsimp [z]
    ring

/-- The tangent point attains the unchanged best sum of the two stage scores. -/
theorem tangent_attained :
    ProbabilityFamily (family (4/5) (3/5)) ∧
    firstSuccess (family (4/5) (3/5)) = 17/25 ∧
    secondSuccess (family (4/5) (3/5)) = 41/50 ∧
    firstSuccess (family (4/5) (3/5))+secondSuccess (family (4/5) (3/5)) = 3/2 := by
  refine ⟨family_probability _ _ (by norm_num),?_,?_,?_⟩
  all_goals simp only [(family_scores _ _).1,(family_scores _ _).2]
  all_goals norm_num

end
end IDT.QMClosure.QuadraticJointReadoutControls
