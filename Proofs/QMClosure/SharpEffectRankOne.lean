import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Sharp Lorentz effects and rank-one positive maps

The order, effect separation, finite-dimensional real inner-product model, and
calibrated endpoints are explicit hypotheses. The conclusions concern positive
linear maps on those supplied ordered spaces. Physical selection of the model
or of a particular implementation is a separate obligation.
-/

namespace IDT.QMClosure.SharpEffectRankOne

noncomputable section

/-- Positivity of a linear functional on a specified cone carrier. -/
def NonnegativeOn {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : Set V) (f : V →ₗ[ℝ] ℝ) : Prop := ∀ x ∈ K, 0 ≤ f x

/-- Every functional in the order interval from zero to `e` lies on its ray.
Equality is equality of linear functionals on the entire ambient space. -/
def IntervalRay {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : Set V) (e : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ g : V →ₗ[ℝ] ℝ, NonnegativeOn K g → NonnegativeOn K (e - g) →
    ∃ t : ℝ, 0 ≤ t ∧ g = t • e

/-- Bounded positive output effects determine every vector of the output space. -/
def Separating {W : Type*} [AddCommGroup W] [Module ℝ W]
    (F : Set (W →ₗ[ℝ] ℝ)) : Prop :=
  ∀ x y : W, (∀ f ∈ F, f x = f y) → x = y

/-- An extreme interval ray and separating bounded output effects force a
positive map with that total effect to have one-dimensional image. -/
theorem positive_map_rank_one
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (K : Set V) (L : Set W) (M : V →ₗ[ℝ] W) (u : W →ₗ[ℝ] ℝ)
    (F : Set (W →ₗ[ℝ] ℝ))
    (hM : ∀ x ∈ K, M x ∈ L)
    (hF : ∀ f ∈ F, NonnegativeOn L f ∧ NonnegativeOn L (u - f))
    (hsep : Separating F) (hray : IntervalRay K (u.comp M))
    (x₀ : V) (hx₀ : u (M x₀) = 1) :
    ∀ x, M x = u (M x) • M x₀ := by
  intro x
  apply hsep
  intro f hf
  obtain ⟨t, _, ht⟩ := hray (f.comp M)
    (fun v hv => (hF f hf).1 (M v) (hM v hv))
    (fun v hv => (hF f hf).2 (M v) (hM v hv))
  have ht₀ : f (M x₀) = t := by
    have h := LinearMap.congr_fun ht x₀
    simpa [hx₀] using h
  have htx : f (M x) = t * u (M x) := by
    exact LinearMap.congr_fun ht x
  rw [map_smul, smul_eq_mul, ht₀, htx, mul_comm]

section Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lorentz cone carrier for the supplied real inner-product space. -/
def lorentzCone : Set (ℝ × E) := {v | ‖v.2‖ ≤ v.1}

/-- The coefficient representation as an actual real linear functional. -/
def effect (a : ℝ) (b : E) : (ℝ × E) →ₗ[ℝ] ℝ where
  toFun v := a * v.1 + inner ℝ b v.2
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
    ring
  map_smul' t v := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right,
      RingHom.id_apply]
    ring

@[simp] theorem effect_apply (a : ℝ) (b : E) (s : ℝ) (x : E) :
    effect a b (s, x) = a * s + inner ℝ b x := rfl

/-- Cone positivity is exactly the Lorentz coefficient inequality. -/
theorem effect_nonnegative_iff (a : ℝ) (b : E) :
    NonnegativeOn lorentzCone (effect a b) ↔ ‖b‖ ≤ a := by
  constructor
  · intro h
    have ha := h (1, 0) (by simp [lorentzCone])
    have hb := h (‖b‖, -b) (by simp [lorentzCone])
    simp only [effect_apply, inner_zero_right, mul_one, add_zero] at ha
    simp only [effect_apply, inner_neg_right, real_inner_self_eq_norm_sq] at hb
    nlinarith [norm_nonneg b]
  · intro h v hv
    have hs : ‖v.2‖ ≤ v.1 := hv
    have ha : 0 ≤ a := (norm_nonneg b).trans h
    have hbound : ‖b‖ * ‖v.2‖ ≤ a * v.1 :=
      mul_le_mul h hs (norm_nonneg _) ha
    have hinner := neg_le_of_abs_le (abs_real_inner_le_norm b v.2)
    change 0 ≤ a * v.1 + inner ℝ b v.2
    linarith

/-- Equality at a unit direction together with the norm bound fixes a vector. -/
theorem eq_smul_of_inner_eq (n b : E) (a : ℝ) (hn : ‖n‖ = 1)
    (hb : ‖b‖ ≤ a) (hinner : inner ℝ b n = a) : b = a • n := by
  have ha : 0 ≤ a := (norm_nonneg b).trans hb
  have hsq : ‖b‖ ^ 2 ≤ a ^ 2 := by nlinarith [norm_nonneg b]
  have hnorm : ‖a • n‖ = a := by simp [norm_smul, hn, abs_of_nonneg ha]
  have hdiff := norm_sub_sq_real b (a • n)
  rw [real_inner_smul_right, hinner, hnorm] at hdiff
  have hz : ‖b - a • n‖ = 0 := by nlinarith [norm_nonneg (b - a • n)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The normalized sharp effect for a specified unit direction. -/
def sharpEffect (n : E) : (ℝ × E) →ₗ[ℝ] ℝ := effect (1 / 2) ((1 / 2 : ℝ) • n)

/-- The supplied total normalization functional. -/
def totalEffect : (ℝ × E) →ₗ[ℝ] ℝ := effect 1 0

@[simp] theorem totalEffect_apply (v : ℝ × E) : totalEffect v = v.1 := by
  simp [totalEffect, effect]

@[simp] theorem sharpEffect_apply (n : E) (v : ℝ × E) :
    sharpEffect n v = (v.1 + inner ℝ n v.2) / 2 := by
  simp [sharpEffect, effect, real_inner_smul_left]
  ring

/-- Coefficient form of extremality, with a nonnegative ray coefficient. -/
theorem coefficient_interval_ray (n b : E) (a : ℝ) (hn : ‖n‖ = 1)
    (hg : NonnegativeOn lorentzCone (effect a b))
    (heg : NonnegativeOn lorentzCone (sharpEffect n - effect a b)) :
    0 ≤ 2 * a ∧ effect a b = (2 * a) • sharpEffect n := by
  have hb : ‖b‖ ≤ a := (effect_nonnegative_iff a b).mp hg
  have ha : 0 ≤ a := (norm_nonneg b).trans hb
  have hbn : inner ℝ b n ≤ a := by
    have h := real_inner_le_norm b n
    rw [hn, mul_one] at h
    exact h.trans hb
  have hzero := heg (1, -n) (by simp [lorentzCone, hn])
  have hzero' : 0 ≤ -(a - inner ℝ b n) := by
    simpa [sharpEffect_apply, effect_apply, inner_neg_right, real_inner_self_eq_norm_sq,
      hn] using hzero
  have hinner : inner ℝ b n = a := by linarith
  have hvec := eq_smul_of_inner_eq n b a hn hb hinner
  refine ⟨by linarith, ?_⟩
  apply LinearMap.ext
  intro v
  simp only [effect, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    smul_eq_mul, sharpEffect_apply, hvec, real_inner_smul_left]
  ring

/-- In finite dimension every algebraic linear effect has these coefficients.
Finite dimension supplies continuity, and Riesz supplies the vector coefficient. -/
theorem linear_effect_representation [FiniteDimensional ℝ E]
    (f : (ℝ × E) →ₗ[ℝ] ℝ) : ∃ a b, f = effect a b := by
  let l : E →ₗ[ℝ] ℝ := f.comp (LinearMap.inr ℝ ℝ E)
  let b : E := (InnerProductSpace.toDual ℝ E).symm l.toContinuousLinearMap
  refine ⟨f (1, 0), b, ?_⟩
  apply LinearMap.ext
  intro v
  have hv : v = v.1 • (1, (0 : E)) + (0, v.2) := by
    ext <;> simp
  have hinner : inner ℝ b v.2 = f (0, v.2) := by
    exact InnerProductSpace.toDual_symm_apply
  change f v = f (1, 0) * v.1 + inner ℝ b v.2
  rw [hinner]
  calc
    f v = f (v.1 • (1, (0 : E)) + (0, v.2)) := congrArg f hv
    _ = f (1, 0) * v.1 + f (0, v.2) := by
      rw [map_add, map_smul, smul_eq_mul]
      ring

/-- Extremality holds over all real linear effects on a finite-dimensional
Lorentz space, without assuming their coefficient representation. -/
theorem sharp_interval_ray [FiniteDimensional ℝ E] (n : E) (hn : ‖n‖ = 1) :
    IntervalRay lorentzCone (sharpEffect n) := by
  intro g hg heg
  obtain ⟨a, b, rfl⟩ := linear_effect_representation g
  exact ⟨2 * a, coefficient_interval_ray n b a hn hg heg⟩

/-- The sharp effect is a bounded positive effect on the entire cone. -/
theorem sharp_effect_bounded (n : E) (hn : ‖n‖ = 1) :
    NonnegativeOn lorentzCone (sharpEffect n) ∧
      NonnegativeOn lorentzCone (totalEffect - sharpEffect n) := by
  constructor
  · apply (effect_nonnegative_iff _ _).2
    simp [norm_smul, hn]
  · have heq : totalEffect - sharpEffect n = effect (1 / 2) ((-(1 / 2) : ℝ) • n) := by
      apply LinearMap.ext
      intro v
      simp [totalEffect_apply, effect, sharpEffect_apply, real_inner_smul_left]
      ring
    rw [heq]
    apply (effect_nonnegative_iff _ _).2
    simp [norm_smul, hn]

/-- All effects in the order interval from zero to total normalization. -/
def boundedEffects : Set ((ℝ × E) →ₗ[ℝ] ℝ) :=
  {f | NonnegativeOn lorentzCone f ∧ NonnegativeOn lorentzCone (totalEffect - f)}

/-- Bounded Lorentz effects separate the entire ambient vector space. -/
theorem bounded_effects_separate : Separating (boundedEffects (E := E)) := by
  intro x y h
  have htotal : (totalEffect (E := E)) ∈ boundedEffects := by
    constructor
    · exact (effect_nonnegative_iff 1 0).2 (by simp)
    · intro v hv
      simp
  have hs : x.1 = y.1 := by simpa using h totalEffect htotal
  by_cases hd : x.2 - y.2 = 0
  · exact Prod.ext hs (sub_eq_zero.mp hd)
  · let d := x.2 - y.2
    have hdn : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    let n := ‖d‖⁻¹ • d
    have hn : ‖n‖ = 1 := by
      simp [n, norm_smul, hdn]
    have he := h (sharpEffect n) (sharp_effect_bounded n hn)
    have hinner : inner ℝ n d = 0 := by
      simp only [sharpEffect_apply] at he
      dsimp [d]
      rw [inner_sub_right]
      linarith
    have hdiag : inner ℝ n d = ‖d‖ := by
      simp only [n, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    exact (hdn (hdiag.symm.trans hinner)).elim

/-- Endpoint certainty uniquely determines a bounded effect in coefficient form. -/
theorem coefficient_sharp_unique (n b : E) (a : ℝ) (hn : ‖n‖ = 1)
    (hg : NonnegativeOn lorentzCone (effect a b))
    (hplus : effect a b (1, n) = 1) (hminus : effect a b (1, -n) = 0) :
    effect a b = sharpEffect n := by
  have hp : a + inner ℝ b n = 1 := by simpa using hplus
  have hm : a - inner ℝ b n = 0 := by
    simpa [inner_neg_right, sub_eq_add_neg] using hminus
  have ha : a = 1 / 2 := by linarith
  have hinner : inner ℝ b n = a := by linarith
  have hb := eq_smul_of_inner_eq n b a hn ((effect_nonnegative_iff a b).mp hg) hinner
  simp [hb, ha, sharpEffect]

/-- Endpoint certainty determines every positive linear effect in finite dimension. -/
theorem sharp_unique [FiniteDimensional ℝ E] (n : E) (hn : ‖n‖ = 1)
    (g : (ℝ × E) →ₗ[ℝ] ℝ) (hg : NonnegativeOn lorentzCone g)
    (hplus : g (1, n) = 1) (hminus : g (1, -n) = 0) : g = sharpEffect n := by
  obtain ⟨a, b, rfl⟩ := linear_effect_representation g
  exact coefficient_sharp_unique n b a hn hg hplus hminus

/-- A calibrated positive operation has rank one when bounded output effects
separate vectors. The calibration and normalization are supplied explicitly. -/
theorem calibrated_positive_map_rank_one [FiniteDimensional ℝ E]
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (n : E) (hn : ‖n‖ = 1) (L : Set W)
    (M : (ℝ × E) →ₗ[ℝ] W) (u : W →ₗ[ℝ] ℝ)
    (F : Set (W →ₗ[ℝ] ℝ))
    (hM : ∀ x ∈ lorentzCone, M x ∈ L)
    (hu : NonnegativeOn L u)
    (hF : ∀ f ∈ F, NonnegativeOn L f ∧ NonnegativeOn L (u - f))
    (hsep : Separating F)
    (hplus : u (M (1, n)) = 1) (hminus : u (M (1, -n)) = 0) :
    ∀ x, M x = sharpEffect n x • M (1, n) := by
  have he : u.comp M = sharpEffect n :=
    sharp_unique n hn (u.comp M) (fun x hx => hu (M x) (hM x hx)) hplus hminus
  have hray : IntervalRay lorentzCone (u.comp M) := by
    rw [he]
    exact sharp_interval_ray n hn
  intro x
  have h := positive_map_rank_one lorentzCone L M u F hM hF hsep hray (1, n) hplus x
  have hx : u (M x) = sharpEffect n x := LinearMap.congr_fun he x
  rwa [hx] at h

/-- For a Lorentz endomorphism, positivity and fixed/zero endpoint calibration
already imply the explicit measure-and-prepare formula on the whole space. -/
theorem calibrated_lorentz_endomorphism [FiniteDimensional ℝ E]
    (n : E) (hn : ‖n‖ = 1) (M : (ℝ × E) →ₗ[ℝ] (ℝ × E))
    (hM : ∀ x ∈ lorentzCone, M x ∈ lorentzCone)
    (hplus : M (1, n) = (1, n)) (hminus : M (1, -n) = 0) :
    ∀ x, M x = sharpEffect n x • (1, n) := by
  have hu : NonnegativeOn (lorentzCone (E := E)) totalEffect :=
    (effect_nonnegative_iff 1 0).2 (by simp)
  have hp : totalEffect (M (1, n)) = 1 := by simp [hplus]
  have hm : totalEffect (M (1, -n)) = 0 := by simp [hminus]
  intro x
  simpa [hplus] using
    calibrated_positive_map_rank_one n hn lorentzCone M totalEffect boundedEffects
      hM hu (fun f hf => hf) bounded_effects_separate hp hm x

end Lorentz

end

end IDT.QMClosure.SharpEffectRankOne
