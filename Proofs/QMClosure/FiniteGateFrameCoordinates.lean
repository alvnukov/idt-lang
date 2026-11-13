import Proofs.QMClosure.FiniteGateFrameDimension
import Mathlib.LinearAlgebra.Pi

/-!
# Coordinates from the finite gate frame

The four rank-one character spaces furnish real coordinates. The common
coordinate is the supplied normalization functional. The remaining axes are
chosen linear coordinates on the three derived one-dimensional spaces.
-/

namespace IDT.QMClosure.FiniteGateFrameCoordinates

open Module FiniteGateFrameDimension

noncomputable section

abbrev W := Fin 4 → ℝ
abbrev W₂ := Fin 2 → ℝ

def quad (t x y z : ℝ) : W := ![t, x, y, z]
@[simp] theorem quad_zero (t x y z : ℝ) : quad t x y z 0 = t := rfl
@[simp] theorem quad_one (t x y z : ℝ) : quad t x y z 1 = x := rfl
@[simp] theorem quad_two (t x y z : ℝ) : quad t x y z 2 = y := rfl
@[simp] theorem quad_three (t x y z : ℝ) : quad t x y z 3 = z := rfl
@[simp] theorem quad_all_zero : quad 0 0 0 0 = 0 := by
  funext i
  fin_cases i <;> rfl

def axis (j : Fin 4) : W :=
  quad (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)
    (if j = 2 then 1 else 0) (if j = 3 then 1 else 0)

def px (w : W) : W := quad (w 0) (w 1) 0 0
def py (w : W) : W := quad (w 0) 0 (w 2) 0
def pz (w : W) : W := quad (w 0) 0 0 (w 3)
def pc (w : W) : W := quad (w 0) 0 0 0

def block (a b c d : ℝ) : W₂ →ₗ[ℝ] W₂ where
  toFun w := ![a * w 0 + b * w 1, c * w 0 + d * w 1]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r v := by ext i; fin_cases i <;> simp <;> ring

theorem expand (L : W →ₗ[ℝ] W) (w : W) :
    L w = w 0 • L (axis 0) + w 1 • L (axis 1) +
      w 2 • L (axis 2) + w 3 • L (axis 3) := by
  have hw : w = w 0 • axis 0 + w 1 • axis 1 +
      w 2 • axis 2 + w 3 • axis 3 := by
    ext i
    fin_cases i <;> simp [axis]
  conv_lhs => rw [hw]
  simp only [map_add, map_smul]

/-- Coordinate form of a linear involution exchanging the two binary ranges. -/
theorem involution_sparse (K : W →ₗ[ℝ] W)
    (hn : ∀ w, K w 0 = w 0)
    (hx : ∀ w, K (px w) = pz (K w))
    (hz : ∀ w, K (pz w) = px (K w))
    (hi : ∀ w, K (K w) = w) :
    ∃ α β : ℝ, α ≠ 0 ∧ β ^ 2 = 1 ∧
      ∀ w, K w = quad (w 0) (α * w 3) (β * w 2) (α⁻¹ * w 1) := by
  let α := K (axis 3) 1
  let β := K (axis 2) 2
  let γ := K (axis 1) 3
  have he (i j : Fin 4) : K (axis j) i =
      if i = 0 ∧ j = 0 then 1 else
      if i = 1 ∧ j = 3 then α else
      if i = 2 ∧ j = 2 then β else
      if i = 3 ∧ j = 1 then γ else 0 := by
    have hxi := congrFun (hx (axis j)) i
    have hzi := congrFun (hz (axis j)) i
    have hni := hn (axis j)
    fin_cases i <;> fin_cases j <;>
      simp [px, pz, axis, α, β, γ] at hxi hzi hni ⊢ <;>
        first | assumption | exact hxi.symm | exact hzi.symm
  have hshape (w : W) : K w = quad (w 0) (α * w 3) (β * w 2) (γ * w 1) := by
    rw [expand K w]
    ext i
    fin_cases i <;> simp [he] <;> ring
  have hag : α * γ = 1 := by
    have h := hi (axis 1)
    simp only [hshape] at h
    simpa [axis] using congrFun h 1
  have hβ : β ^ 2 = 1 := by
    have h := hi (axis 2)
    simp only [hshape] at h
    have hh := congrFun h 2
    simp [axis] at hh
    nlinarith
  have hα : α ≠ 0 := by intro h; simp [h] at hag
  have hγ : γ = α⁻¹ := by
    field_simp [hα]
    nlinarith [hag]
  refine ⟨α, β, hα, hβ, ?_⟩
  simpa [hγ] using hshape

/-- Coordinate form of a map fixing the common and longitudinal coordinates. -/
theorem transverse_sparse (A : W →ₗ[ℝ] W)
    (hn : ∀ w, A w 0 = w 0)
    (hc : ∀ w, A (pz w) = pz w)
    (hz : ∀ w, pz (A w) = A (pz w))
    (hthree : ∀ w, A (A (A w)) = w)
    (hne : A ≠ LinearMap.id) :
    ∃ a b c d : ℝ,
      (∀ w, A w = quad (w 0) (a * w 1 + b * w 2)
        (c * w 1 + d * w 2) (w 3)) ∧
      (∀ w, block a b c d (block a b c d (block a b c d w)) = w) ∧
      block a b c d ≠ LinearMap.id := by
  let a := A (axis 1) 1
  let b := A (axis 2) 1
  let c := A (axis 1) 2
  let d := A (axis 2) 2
  have he (i j : Fin 4) : A (axis j) i =
      if i = 0 ∧ j = 0 then 1 else
      if i = 1 ∧ j = 1 then a else
      if i = 1 ∧ j = 2 then b else
      if i = 2 ∧ j = 1 then c else
      if i = 2 ∧ j = 2 then d else
      if i = 3 ∧ j = 3 then 1 else 0 := by
    have hci := congrFun (hc (axis j)) i
    have hzi := congrFun (hz (axis j)) i
    have hni := hn (axis j)
    fin_cases i <;> fin_cases j <;>
      simp_all [pz, axis, a, b, c, d]
  have hshape (w : W) : A w = quad (w 0) (a * w 1 + b * w 2)
      (c * w 1 + d * w 2) (w 3) := by
    rw [expand A w]
    ext i
    fin_cases i <;> simp [he] <;> ring
  refine ⟨a, b, c, d, hshape, ?_, ?_⟩
  · intro w
    have h := hthree (quad 0 (w 0) (w 1) 0)
    simp only [hshape] at h
    ext i
    fin_cases i
    · simpa [block] using congrFun h 1
    · simpa [block] using congrFun h 2
  · intro hb
    have h1 := LinearMap.congr_fun hb ![1, 0]
    have h2 := LinearMap.congr_fun hb ![0, 1]
    have ha : a = 1 := by simpa [block] using congrFun h1 0
    have hc0 : c = 0 := by simpa [block] using congrFun h1 1
    have hb0 : b = 0 := by simpa [block] using congrFun h2 0
    have hd : d = 1 := by simpa [block] using congrFun h2 1
    apply hne
    apply LinearMap.ext
    intro w
    funext i
    rw [hshape]
    fin_cases i <;> simp [ha, hb0, hc0, hd]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- All coordinate choices and gate equations constructed from a frame. -/
structure AxisCoordinates (F : Frame V) where
  equiv : V ≃ₗ[ℝ] W
  normalized : ∀ v, equiv v 0 = F.normalization v
  Jx_action : ∀ v, equiv (F.Jx v) =
    quad (equiv v 0) (equiv v 1) (-equiv v 2) (-equiv v 3)
  Jz_action : ∀ v, equiv (F.Jz v) =
    quad (equiv v 0) (-equiv v 1) (-equiv v 2) (equiv v 3)
  Ex_action : ∀ v, equiv (F.Ex v) = px (equiv v)
  Ey_action : ∀ v, equiv (F.Ey v) = py (equiv v)
  Ez_action : ∀ v, equiv (F.Ez v) = pz (equiv v)
  R_action : ∀ v, equiv (F.R v) = pc (equiv v)
  α : ℝ
  β : ℝ
  alpha_ne_zero : α ≠ 0
  beta_sq : β ^ 2 = 1
  H_action : ∀ v, equiv (F.H v) =
    quad (equiv v 0) (α * equiv v 3) (β * equiv v 2) (α⁻¹ * equiv v 1)
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  T_action : ∀ v, equiv (F.T v) =
    quad (equiv v 0) (a * equiv v 1 + b * equiv v 2)
      (c * equiv v 1 + d * equiv v 2) (equiv v 3)
  transverse_cube : ∀ w, block a b c d (block a b c d (block a b c d w)) = w
  transverse_nontrivial : block a b c d ≠ LinearMap.id

section Construction

variable (F : Frame V) [FiniteDimensional ℝ V]

def commonMap : LinearMap.range (F.character 0) →ₗ[ℝ] ℝ :=
  F.normalization.comp (LinearMap.range (F.character 0)).subtype

omit [FiniteDimensional ℝ V] in
theorem commonMap_surjective : Function.Surjective (commonMap F) := by
  obtain ⟨s, hs⟩ := F.nonempty
  intro r
  refine ⟨⟨r • F.R s, ?_⟩, ?_⟩
  · refine ⟨r • s, ?_⟩
    simp
  · change F.normalization (r • F.R s) = r
    simp [F.norm_R, F.normalized s hs]

def commonEquiv : LinearMap.range (F.character 0) ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (commonMap F) ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa [Frame.rank] using F.character_ranks 0)).2 (commonMap_surjective F),
    commonMap_surjective F⟩

def axisEquiv (i : Fin 4) : LinearMap.range (F.character i) ≃ₗ[ℝ] ℝ :=
  if h : i = 0 then by subst i; exact commonEquiv F
  else LinearEquiv.ofFinrankEq _ _ (by simpa [Frame.rank] using F.character_ranks i)

def coordinates : V ≃ₗ[ℝ] W :=
  (characterEquiv F.character F.character_mul F.character_sum).trans
    (LinearEquiv.piCongrRight (axisEquiv F))

theorem coordinates_apply (v : V) (i : Fin 4) :
    coordinates F v i = axisEquiv F i ⟨F.character i v, v, rfl⟩ := rfl

theorem coordinates_normalized (v : V) : coordinates F v 0 = F.normalization v := by
  change axisEquiv F 0 ⟨F.character 0 v, v, rfl⟩ = _
  simp [axisEquiv, commonEquiv, commonMap, F.norm_R]

@[simp] theorem normalization_symm (w : W) :
    F.normalization ((coordinates F).symm w) = w 0 := by
  simpa using (coordinates_normalized F ((coordinates F).symm w)).symm

theorem coordinates_character (j : Fin 4) (v : V) (i : Fin 4) :
    coordinates F (F.character j v) i =
      if i = j then coordinates F v i else 0 := by
  rw [coordinates_apply, coordinates_apply]
  by_cases h : i = j
  · subst j
    simp only
    congr 1
    apply Subtype.ext
    simp [F.character_mul]
  · rw [if_neg h]
    have hh : (⟨F.character i (F.character j v), F.character j v, rfl⟩ :
        LinearMap.range (F.character i)) = 0 := by
      apply Subtype.ext
      simpa [h] using F.character_mul i j v
    rw [hh, map_zero]

theorem coordinates_Ex (v : V) : coordinates F (F.Ex v) = px (coordinates F v) := by
  rw [F.Ex_character]
  ext i
  simp only [LinearMap.add_apply, map_add, Pi.add_apply, coordinates_character]
  fin_cases i <;> simp [px]

theorem coordinates_Ey (v : V) : coordinates F (F.Ey v) = py (coordinates F v) := by
  rw [F.Ey_character]
  ext i
  simp only [LinearMap.add_apply, map_add, Pi.add_apply, coordinates_character]
  fin_cases i <;> simp [py]

theorem coordinates_Ez (v : V) : coordinates F (F.Ez v) = pz (coordinates F v) := by
  rw [F.Ez_character]
  ext i
  simp only [LinearMap.add_apply, map_add, Pi.add_apply, coordinates_character]
  fin_cases i <;> simp [pz]

theorem coordinates_R (v : V) : coordinates F (F.R v) = pc (coordinates F v) := by
  have h := coordinates_character F 0 v
  change coordinates F (F.character 0 v) = _
  ext i
  rw [h i]
  fin_cases i <;> simp [pc]

theorem coordinates_Jx (v : V) : coordinates F (F.Jx v) =
    quad (coordinates F v 0) (coordinates F v 1)
      (-coordinates F v 2) (-coordinates F v 3) := by
  have h : F.Jx v = (2 : ℝ) • F.Ex v - v := by
    simp [Frame.Ex, average, LinearMap.smul_apply, LinearMap.add_apply]
  rw [h, map_sub, map_smul, coordinates_Ex]
  ext i
  fin_cases i <;> simp [px] <;> ring

theorem coordinates_Jz (v : V) : coordinates F (F.Jz v) =
    quad (coordinates F v 0) (-coordinates F v 1)
      (-coordinates F v 2) (coordinates F v 3) := by
  have h : F.Jz v = (2 : ℝ) • F.Ez v - v := by
    simp [Frame.Ez, average, LinearMap.smul_apply, LinearMap.add_apply]
  rw [h, map_sub, map_smul, coordinates_Ez]
  ext i
  fin_cases i <;> simp [pz] <;> ring

def transport (A : V →ₗ[ℝ] V) : W →ₗ[ℝ] W :=
  (coordinates F).toLinearMap.comp (A.comp (coordinates F).symm.toLinearMap)

@[simp] theorem transport_apply (A : V →ₗ[ℝ] V) (v : V) :
    transport F A (coordinates F v) = coordinates F (A v) := by
  simp [transport]

@[simp] theorem transport_symm_apply (A : V →ₗ[ℝ] V) (w : W) :
    transport F A w = coordinates F (A ((coordinates F).symm w)) := rfl

theorem H_sparse :
    ∃ α β : ℝ, α ≠ 0 ∧ β ^ 2 = 1 ∧
      ∀ v, coordinates F (F.H v) = quad (coordinates F v 0)
        (α * coordinates F v 3) (β * coordinates F v 2) (α⁻¹ * coordinates F v 1) := by
  have hx (w : W) : transport F F.H (px w) = pz (transport F F.H w) := by
    have h := congrArg (coordinates F) (F.H_Ex ((coordinates F).symm w))
    have he : (coordinates F).symm (px w) = F.Ex ((coordinates F).symm w) := by
      apply (coordinates F).injective
      simp [coordinates_Ex]
    simpa only [transport_symm_apply, he, coordinates_Ez] using h
  have hz (w : W) : transport F F.H (pz w) = px (transport F F.H w) := by
    have h := congrArg (coordinates F) (F.H_Ez ((coordinates F).symm w))
    have he : (coordinates F).symm (pz w) = F.Ez ((coordinates F).symm w) := by
      apply (coordinates F).injective
      simp [coordinates_Ez]
    simpa only [transport_symm_apply, he, coordinates_Ex] using h
  obtain ⟨α, β, hα, hβ, hK⟩ := involution_sparse (transport F F.H)
    (by intro w; simp [coordinates_normalized, F.norm_H]) hx hz
    (by intro w; simp [F.H_involutive])
  refine ⟨α, β, hα, hβ, ?_⟩
  intro v
  simpa using hK (coordinates F v)

theorem T_sparse :
    ∃ a b c d : ℝ,
      (∀ v, coordinates F (F.T v) = quad (coordinates F v 0)
        (a * coordinates F v 1 + b * coordinates F v 2)
        (c * coordinates F v 1 + d * coordinates F v 2) (coordinates F v 3)) ∧
      (∀ w, block a b c d (block a b c d (block a b c d w)) = w) ∧
      block a b c d ≠ LinearMap.id := by
  have hc (w : W) : transport F F.T (pz w) = pz w := by
    have he : (coordinates F).symm (pz w) = F.Ez ((coordinates F).symm w) := by
      apply (coordinates F).injective
      simp [coordinates_Ez]
    simp only [transport_symm_apply, he, F.T_fixes_Ez, coordinates_Ez,
      LinearEquiv.apply_symm_apply]
  have hz (w : W) : pz (transport F F.T w) = transport F F.T (pz w) := by
    have h := congrArg (coordinates F) (F.T_Ez ((coordinates F).symm w))
    have he : (coordinates F).symm (pz w) = F.Ez ((coordinates F).symm w) := by
      apply (coordinates F).injective
      simp [coordinates_Ez]
    simpa only [transport_symm_apply, he, coordinates_Ez] using h
  have hne : transport F F.T ≠ LinearMap.id := by
    intro h
    apply F.T_nontrivial
    ext v
    apply (coordinates F).injective
    have hh := LinearMap.congr_fun h (coordinates F v)
    simpa using hh
  obtain ⟨a, b, c, d, hA, hcube, hnontrivial⟩ := transverse_sparse
    (transport F F.T)
    (by intro w; simp [coordinates_normalized, F.norm_T]) hc hz
    (by intro w; simp [F.T_cube]) hne
  refine ⟨a, b, c, d, ?_, hcube, hnontrivial⟩
  intro v
  simpa using hA (coordinates F v)

end Construction

end

end IDT.QMClosure.FiniteGateFrameCoordinates

namespace IDT.QMClosure.FiniteGateFrameDimension.Frame

open IDT.QMClosure.FiniteGateFrameCoordinates

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The frame constructs its coordinates without a supplied finite-dimensional
instance, coordinate basis, metric, or inner product. -/
theorem exists_axis_coordinates (F : Frame V) : Nonempty (AxisCoordinates F) := by
  letI : FiniteDimensional ℝ V := F.finite_dimensional
  obtain ⟨α, β, hα, hβ, hH⟩ := H_sparse F
  obtain ⟨a, b, c, d, hT, hcube, hnontrivial⟩ := T_sparse F
  exact ⟨{
    equiv := coordinates F
    normalized := coordinates_normalized F
    Jx_action := coordinates_Jx F
    Jz_action := coordinates_Jz F
    Ex_action := coordinates_Ex F
    Ey_action := coordinates_Ey F
    Ez_action := coordinates_Ez F
    R_action := coordinates_R F
    α := α
    β := β
    alpha_ne_zero := hα
    beta_sq := hβ
    H_action := hH
    a := a
    b := b
    c := c
    d := d
    T_action := hT
    transverse_cube := hcube
    transverse_nontrivial := hnontrivial }⟩

end IDT.QMClosure.FiniteGateFrameDimension.Frame
