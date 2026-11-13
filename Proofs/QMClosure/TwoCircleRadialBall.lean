import Proofs.QMClosure.TwoCircleSphereTransitivity

/-!
# Radiality and ball filling with an explicitly available projection

Full-circle invariance, an attained squared-radius maximum, and availability of
one actual coordinate projection are supplied hypotheses. This bridge does not
establish those hypotheses from finite gates or binary-segment data.
-/

noncomputable section

namespace IDT.QMClosure.TwoCircleSphere

open Set

/-- Membership depends only on squared Euclidean radius. -/
def Radial (C : Set Vec3) : Prop :=
  ∀ p ∈ C, ∀ q, sqnorm q = sqnorm p → q ∈ C

theorem sqnorm_nonneg (p : Vec3) : 0 ≤ sqnorm p := by
  dsimp [sqnorm]
  positivity

theorem sqnorm_eq_zero_iff (p : Vec3) : sqnorm p = 0 ↔ p = ⟨0, 0, 0⟩ := by
  constructor
  · intro hp
    dsimp [sqnorm] at hp
    ext <;> dsimp <;> nlinarith [sq_nonneg p.x, sq_nonneg p.y, sq_nonneg p.z]
  · intro hp
    rw [hp]
    norm_num [sqnorm]

/-- Apply sphere transitivity separately to each nonzero radius slice. -/
theorem radial_of_full_circle_invariance {C : Set Vec3} {s c : ℝ}
    (hs : 0 < s) (haxis : s ^ 2 + c ^ 2 = 1)
    (hC : FullCircleInvariant C s c) : Radial C := by
  intro p hp q hqp
  by_cases hp0 : sqnorm p = 0
  · have hq0 : sqnorm q = 0 := hqp.trans hp0
    have hpO := (sqnorm_eq_zero_iff p).1 hp0
    have hqO := (sqnorm_eq_zero_iff q).1 hq0
    rw [hqO, ← hpO]
    exact hp
  · let r := Real.sqrt (sqnorm p)
    have hr : 0 < r := Real.sqrt_pos.2
      (lt_of_le_of_ne (sqnorm_nonneg p) (Ne.symm hp0))
    have hrsq : r ^ 2 = sqnorm p := Real.sq_sqrt (sqnorm_nonneg p)
    let D := C ∩ sphere r
    have hpS : p ∈ sphere r := hrsq.symm
    have hD : D = sphere r := eq_sphere_of_full_circle_invariance hr hs haxis
      (fun _ hv => hv.2) ⟨p, hp, hpS⟩
      (by
        intro k l hk v hv
        refine ⟨hC.z k l hk v hv.1, ?_⟩
        change sqnorm (rotZ k l v) = r ^ 2
        rw [rotZ_norm k l hk]
        exact hv.2)
      (by
        intro k l hk v hv
        refine ⟨hC.tilt k l hk v hv.1, ?_⟩
        change sqnorm (rotTilt s c k l v) = r ^ 2
        rw [rotTilt_norm s c k l haxis hk]
        exact hv.2)
    have hqD : q ∈ D := by
      rw [hD]
      change sqnorm q = r ^ 2
      exact hqp.trans hrsq.symm
    exact hqD.1

/-- The actual x-axis coordinate projection. -/
def projectX (p : Vec3) : Vec3 := ⟨p.x, 0, 0⟩

/-- The actual y-axis coordinate projection. -/
def projectY (p : Vec3) : Vec3 := ⟨0, p.y, 0⟩

/-- The actual z-axis coordinate projection. -/
def projectZ (p : Vec3) : Vec3 := ⟨0, 0, p.z⟩

/-- Radiality transports x-projection availability to z-projection availability. -/
theorem projectZ_stable_of_projectX {C : Set Vec3} (hC : Radial C)
    (hX : ∀ p ∈ C, projectX p ∈ C) : ∀ p ∈ C, projectZ p ∈ C := by
  intro p hp
  have hperm : (⟨p.z, p.x, p.y⟩ : Vec3) ∈ C := hC p hp _ (by
    dsimp [sqnorm]
    ring)
  have hproj := hX _ hperm
  exact hC _ hproj (projectZ p) (by dsimp [sqnorm, projectX, projectZ]; ring)

/-- Radiality transports y-projection availability to z-projection availability. -/
theorem projectZ_stable_of_projectY {C : Set Vec3} (hC : Radial C)
    (hY : ∀ p ∈ C, projectY p ∈ C) : ∀ p ∈ C, projectZ p ∈ C := by
  intro p hp
  have hperm : (⟨p.x, p.z, p.y⟩ : Vec3) ∈ C := hC p hp _ (by
    dsimp [sqnorm]
    ring)
  have hproj := hY _ hperm
  exact hC _ hproj (projectZ p) (by dsimp [sqnorm, projectY, projectZ]; ring)

/-- An attained maximum sphere plus an available z projection fills the ball.
Attainment and a uniform bound are explicit independent hypotheses. -/
theorem eq_ball_of_radial_projectZ {C : Set Vec3} {R : ℝ}
    (_hR : 0 ≤ R) (hC : Radial C)
    (hmax : ∃ p ∈ C, sqnorm p = R ^ 2)
    (hbound : ∀ p ∈ C, sqnorm p ≤ R ^ 2)
    (hZ : ∀ p ∈ C, projectZ p ∈ C) :
    C = {q | sqnorm q ≤ R ^ 2} := by
  apply Set.Subset.antisymm
  · intro p hp
    exact hbound p hp
  · intro q hq
    obtain ⟨p, hp, hpmax⟩ := hmax
    let ρ := Real.sqrt (sqnorm q)
    have hρ : ρ ^ 2 = sqnorm q := Real.sq_sqrt (sqnorm_nonneg q)
    have hrem : 0 ≤ R ^ 2 - ρ ^ 2 := by
      rw [hρ]
      exact sub_nonneg.2 hq
    let v : Vec3 := ⟨Real.sqrt (R ^ 2 - ρ ^ 2), 0, ρ⟩
    have hvnorm : sqnorm v = R ^ 2 := by
      change Real.sqrt (R ^ 2 - ρ ^ 2) ^ 2 + 0 ^ 2 + ρ ^ 2 = R ^ 2
      rw [Real.sq_sqrt hrem]
      ring
    have hv : v ∈ C := hC p hp v (hvnorm.trans hpmax.symm)
    have hz : projectZ v ∈ C := hZ v hv
    apply hC (projectZ v) hz q
    change sqnorm q = 0 ^ 2 + 0 ^ 2 + ρ ^ 2
    rw [hρ]
    ring

/-- Any one of the three explicit coordinate projections suffices. -/
theorem eq_ball_of_radial_one_axis_projection {C : Set Vec3} {R : ℝ}
    (hR : 0 ≤ R) (hC : Radial C)
    (hmax : ∃ p ∈ C, sqnorm p = R ^ 2)
    (hbound : ∀ p ∈ C, sqnorm p ≤ R ^ 2)
    (hproj : (∀ p ∈ C, projectX p ∈ C) ∨
      (∀ p ∈ C, projectY p ∈ C) ∨ (∀ p ∈ C, projectZ p ∈ C)) :
    C = {q | sqnorm q ≤ R ^ 2} := by
  apply eq_ball_of_radial_projectZ hR hC hmax hbound
  rcases hproj with hX | hY | hZ
  · exact projectZ_stable_of_projectX hC hX
  · exact projectZ_stable_of_projectY hC hY
  · exact hZ

/-- A conditional geometry bridge from two full circles and one actual
projection, with the radius bound and its attainment supplied explicitly. -/
theorem eq_ball_of_full_circle_and_one_axis_projection {C : Set Vec3} {R s c : ℝ}
    (hR : 0 ≤ R) (hs : 0 < s) (haxis : s ^ 2 + c ^ 2 = 1)
    (hC : FullCircleInvariant C s c)
    (hmax : ∃ p ∈ C, sqnorm p = R ^ 2)
    (hbound : ∀ p ∈ C, sqnorm p ≤ R ^ 2)
    (hproj : (∀ p ∈ C, projectX p ∈ C) ∨
      (∀ p ∈ C, projectY p ∈ C) ∨ (∀ p ∈ C, projectZ p ∈ C)) :
    C = {q | sqnorm q ≤ R ^ 2} :=
  eq_ball_of_radial_one_axis_projection hR
    (radial_of_full_circle_invariance hs haxis hC) hmax hbound hproj

end IDT.QMClosure.TwoCircleSphere
