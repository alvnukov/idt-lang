import Proofs.QMClosure.FiniteGateFrameDimension

/-!
# Preparation bounds and scalar orbit bounds

Fixed-endpoint binary averages bound each real linear functional on the
preparation set. Algebraic spanning transfers this to each individual orbit
of any supplied preparation-preserving linear endomorphism. The orbit bound
may depend on the functional, endomorphism, and starting vector. One constant
bounds all nonnegative powers for each such choice. No norm or topology is
assumed in this argument.
-/

namespace IDT.QMClosure.FiniteGatePreparationBounds

open IDT.QMClosure.FiniteGateFrameDimension

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

noncomputable section

/-- The two endpoints are fixed before selecting a preparation. -/
theorem binary_functional_bound (S : Set V) (E : V →ₗ[ℝ] V)
    (hbinary : BinarySegment S E) (f : V →ₗ[ℝ] ℝ) :
    ∃ B : ℝ, ∀ s ∈ S, |f (E s)| ≤ B := by
  obtain ⟨a, _, b, _, hab⟩ := hbinary
  refine ⟨|f a| + |f b|, ?_⟩
  intro s hs
  obtain ⟨t, ht, hE⟩ := hab s hs
  have ht_nonneg : 0 ≤ t := ht.1
  have ht_le : t ≤ 1 := ht.2
  have hcoeff_nonneg : 0 ≤ 1 - t := by linarith
  have hcoeff_le : 1 - t ≤ 1 := by linarith
  rw [hE, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  calc
    |(1 - t) * f a + t * f b| ≤ |(1 - t) * f a| + |t * f b| := abs_add_le _ _
    _ = (1 - t) * |f a| + t * |f b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hcoeff_nonneg, abs_of_nonneg ht_nonneg]
    _ ≤ |f a| + |f b| := by
      have ha := mul_le_mul_of_nonneg_right hcoeff_le (abs_nonneg (f a))
      have hb := mul_le_mul_of_nonneg_right ht_le (abs_nonneg (f b))
      linarith

namespace Frame

variable (F : FiniteGateFrameDimension.Frame V)

/-- The common average is an algebraic composition. Its availability on the
preparation set is unnecessary for the scalar bound below. -/
theorem common_average_eq (v : V) : F.R v = F.Ex (F.Ez v) := by
  rw [F.Ex_character, F.Ez_character]
  simp only [LinearMap.add_apply, map_add, F.character_mul]
  simp

theorem binary_reconstruction (v : V) :
    v = F.Ex v + F.Ey v + F.Ez v - (2 : ℝ) • F.R v := by
  have h := F.character_sum v
  simp only [F.character_zero, F.character_one, F.character_two, F.character_three,
    FiniteGateFrameDimension.Frame.Qx, FiniteGateFrameDimension.Frame.Qy,
    FiniteGateFrameDimension.Frame.Qz, LinearMap.sub_apply] at h
  calc
    v = F.R v + (F.Ex v - F.R v) + (F.Ey v - F.R v) + (F.Ez v - F.R v) := h.symm
    _ = F.Ex v + F.Ey v + F.Ez v - (2 : ℝ) • F.R v := by module

/-- Every real linear functional is uniformly bounded on preparations. -/
theorem functional_preparation_bound (f : V →ₗ[ℝ] ℝ) :
    ∃ B : ℝ, ∀ s ∈ F.preparations, |f s| ≤ B := by
  obtain ⟨Bx, hx⟩ := binary_functional_bound _ F.Ex F.binary_x f
  obtain ⟨By, hy⟩ := binary_functional_bound _ F.Ey F.binary_y f
  obtain ⟨Bz, hz⟩ := binary_functional_bound _ F.Ez F.binary_z f
  obtain ⟨Br, hr⟩ := binary_functional_bound _ F.Ez F.binary_z (f.comp F.Ex)
  have hr' : ∀ s ∈ F.preparations, |f (F.R s)| ≤ Br := by
    intro s hs
    rw [common_average_eq F]
    exact hr s hs
  refine ⟨Bx + By + Bz + 2 * Br, ?_⟩
  intro s hs
  have hrepr : f s = f (F.Ex s) + f (F.Ey s) + f (F.Ez s) - 2 * f (F.R s) := by
    conv_lhs => rw [binary_reconstruction F s]
    simp only [map_add, map_sub, map_smul, smul_eq_mul]
  rw [hrepr]
  calc
    |f (F.Ex s) + f (F.Ey s) + f (F.Ez s) - 2 * f (F.R s)| ≤
        |f (F.Ex s) + f (F.Ey s)| + |f (F.Ez s)| + |2 * f (F.R s)| := by
      have hsub := abs_sub (f (F.Ex s) + f (F.Ey s) + f (F.Ez s)) (2 * f (F.R s))
      have hadd := abs_add_le (f (F.Ex s) + f (F.Ey s)) (f (F.Ez s))
      linarith
    _ ≤ |f (F.Ex s)| + |f (F.Ey s)| + |f (F.Ez s)| + 2 * |f (F.R s)| := by
      rw [abs_mul]
      norm_num
      linarith [abs_add_le (f (F.Ex s)) (f (F.Ey s))]
    _ ≤ Bx + By + Bz + 2 * Br := by
      linarith [hx s hs, hy s hs, hz s hs, hr' s hs]

end Frame

/-- Endomorphism powers use multiplication by composition. -/
theorem powers_preserve_preparations (S : Set V) (A : Module.End ℝ V)
    (hA : ∀ s ∈ S, A s ∈ S) :
    ∀ n : ℕ, ∀ s ∈ S, (A ^ n) s ∈ S := by
  intro n
  induction n with
  | zero =>
    intro s hs
    simpa only [pow_zero, Module.End.one_apply] using hs
  | succ n ih =>
    intro s hs
    rw [pow_succ', Module.End.mul_apply]
    exact hA ((A ^ n) s) (ih s hs)

/-- Having a scalar bound uniform in all nonnegative powers is a linear
subspace property of the starting vector. -/
def boundedOrbitSubmodule (A : Module.End ℝ V) (f : V →ₗ[ℝ] ℝ) : Submodule ℝ V where
  carrier := {v | ∃ B : ℝ, ∀ n : ℕ, |f ((A ^ n) v)| ≤ B}
  zero_mem' := ⟨0, by intro n; simp⟩
  add_mem' := by
    intro v w hv hw
    obtain ⟨Bv, hv⟩ := hv
    obtain ⟨Bw, hw⟩ := hw
    refine ⟨Bv + Bw, fun n => ?_⟩
    simp only [map_add]
    exact (abs_add_le _ _).trans (add_le_add (hv n) (hw n))
  smul_mem' := by
    intro a v hv
    obtain ⟨Bv, hv⟩ := hv
    refine ⟨|a| * Bv, fun n => ?_⟩
    simp only [map_smul, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hv n) (abs_nonneg a)

/-- Spanning transfers a preparation bound to each individual orbit, with a
single constant for every power of the selected endomorphism. -/
theorem orbit_bound_of_spanning (S : Set V)
    (hspan : Submodule.span ℝ S = ⊤) (f : V →ₗ[ℝ] ℝ)
    (hbounded : ∃ B : ℝ, ∀ s ∈ S, |f s| ≤ B)
    (A : Module.End ℝ V) (hA : ∀ s ∈ S, A s ∈ S) :
    ∀ v : V, ∃ Bv : ℝ, ∀ n : ℕ, |f ((A ^ n) v)| ≤ Bv := by
  obtain ⟨B, hB⟩ := hbounded
  have hle : Submodule.span ℝ S ≤ boundedOrbitSubmodule A f := by
    apply Submodule.span_le.mpr
    intro s hs
    refine ⟨B, fun n => ?_⟩
    exact hB ((A ^ n) s) (powers_preserve_preparations S A hA n s hs)
  intro v
  apply hle
  rw [hspan]
  trivial

namespace Frame

variable (F : FiniteGateFrameDimension.Frame V)

/-- The frame's binary premises supply the bound for every actual linear gate
preserving its preparations. -/
theorem functional_orbit_bound (A : Module.End ℝ V)
    (hA : ∀ s ∈ F.preparations, A s ∈ F.preparations)
    (f : V →ₗ[ℝ] ℝ) (v : V) :
    ∃ B : ℝ, ∀ n : ℕ, |f ((A ^ n) v)| ≤ B :=
  orbit_bound_of_spanning F.preparations F.spanning f
    (functional_preparation_bound F f) A hA v

theorem JxT_orbit_bound (f : V →ₗ[ℝ] ℝ) (v : V) :
    ∃ B : ℝ, ∀ n : ℕ, |f (((F.Jx.comp F.T) ^ n) v)| ≤ B := by
  apply functional_orbit_bound F (F.Jx.comp F.T) _ f v
  intro s hs
  exact F.Jx_available (F.T s) (F.T_available s hs)

end Frame

end

end IDT.QMClosure.FiniteGatePreparationBounds
