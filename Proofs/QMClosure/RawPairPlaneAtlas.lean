import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Tactic

/-!
# Weighted complex pair-plane atlas foundation

This module supplies geometric atlas interfaces and canonical weighted ray fibers.
It constructs neither a complete atlas nor a global pair operation. Each native
chart has its stated weighted quadratic form. No global vector-space structure
or countermodel existence is asserted.
-/

namespace IDT.QMClosure.RawPairPlaneAtlas

universe u

/-- A geometric atlas whose distinct planes share at most one ray. -/
structure PartialAtlas where
  Ray : Type u
  Plane : Type u
  weight : Ray → ℝ
  weight_pos : ∀ r, 0 < weight r
  coord : Plane → (Option ℂ ↪ Ray)
  weight_coord : ∀ p t, weight (coord p (some t)) =
    weight (coord p (some 0)) + weight (coord p none) * Complex.normSq t
  two_points : ∀ p q (s t s' t' : Option ℂ), s ≠ t →
    coord p s = coord q s' → coord p t = coord q t' → p = q

/-- The additional geometric obligations for a complete pair-plane atlas. -/
structure CompleteAtlas extends PartialAtlas where
  ray_nontrivial : Nontrivial Ray
  pair_covered : ∀ r s, r ≠ s → ∃ p u v, coord p u = r ∧ coord p v = s

/-- An injective atlas extension preserving all old weights and coordinates. -/
structure Extension (D E : PartialAtlas.{u}) where
  ray : D.Ray ↪ E.Ray
  plane : D.Plane ↪ E.Plane
  weight_map : ∀ r, E.weight (ray r) = D.weight r
  coord_map : ∀ p t, E.coord (plane p) t = ray (D.coord p t)

namespace Extension

def refl (D : PartialAtlas.{u}) : Extension D D where
  ray := Function.Embedding.refl _
  plane := Function.Embedding.refl _
  weight_map _ := rfl
  coord_map _ _ := rfl

/-- Composition first applies `f`, then `g`. -/
def trans {D E F : PartialAtlas.{u}} (f : Extension D E) (g : Extension E F) :
    Extension D F where
  ray := f.ray.trans g.ray
  plane := f.plane.trans g.plane
  weight_map r := (g.weight_map (f.ray r)).trans (f.weight_map r)
  coord_map p t := by
    change F.coord (g.plane (f.plane p)) t = g.ray (f.ray (D.coord p t))
    rw [g.coord_map, f.coord_map]

end Extension

abbrev NonzeroC := {z : ℂ // z ≠ 0}

/-- All ray fibers share the single zero `none`. -/
abbrev Raw (R : Type u) := Option (R × NonzeroC)

noncomputable section

open Classical

variable {R : Type u}

def point (r : R) (z : ℂ) : Raw R :=
  if h : z = 0 then none else some (r, ⟨z, h⟩)

def scale (c : ℂ) : Raw R → Raw R
  | none => none
  | some (r, z) => point r (c * z.val)

@[simp] theorem point_zero (r : R) : point r 0 = none := by simp [point]

theorem point_eq_point_iff (r s : R) (c d : ℂ) :
    point r c = point s d ↔ c = d ∧ (c = 0 ∨ r = s) := by
  by_cases hc : c = 0 <;> by_cases hd : d = 0 <;>
    simp [point, hc, hd, eq_comm, Prod.ext_iff, and_comm]

@[simp] theorem scale_point (c : ℂ) (r : R) (z : ℂ) :
    scale c (point r z) = point r (c * z) := by
  by_cases hz : z = 0 <;> simp [point, scale, hz]

@[simp] theorem scale_zero (x : Raw R) : scale 0 x = none := by
  cases x with
  | none => rfl
  | some x => rcases x with ⟨r, z⟩; simp [scale]

@[simp] theorem scale_one (x : Raw R) : scale 1 x = x := by
  cases x with
  | none => rfl
  | some x => rcases x with ⟨r, z⟩; simp [scale, point, z.property]

theorem scale_mul (c d : ℂ) (x : Raw R) :
    scale (c * d) x = scale c (scale d x) := by
  cases x with
  | none => rfl
  | some x =>
    rcases x with ⟨r, z⟩
    change point r ((c * d) * z.val) = scale c (point r (d * z.val))
    rw [scale_point, mul_assoc]

def W (D : PartialAtlas.{u}) : Raw D.Ray → ℝ
  | none => 0
  | some (r, z) => D.weight r * Complex.normSq z.val

@[simp] theorem W_point (D : PartialAtlas.{u}) (r : D.Ray) (z : ℂ) :
    W D (point r z) = D.weight r * Complex.normSq z := by
  by_cases hz : z = 0 <;> simp [point, W, hz]

theorem W_nonnegative (D : PartialAtlas.{u}) (x : Raw D.Ray) : 0 ≤ W D x := by
  cases x with
  | none => exact le_refl 0
  | some x => exact mul_nonneg (D.weight_pos x.1).le (Complex.normSq_nonneg x.2.val)

theorem W_eq_zero_iff (D : PartialAtlas.{u}) (x : Raw D.Ray) :
    W D x = 0 ↔ x = none := by
  cases x with
  | none => simp [W]
  | some x =>
    have hw := ne_of_gt (D.weight_pos x.1)
    have hz := x.2.property
    simp [W, mul_eq_zero, hw, Complex.normSq_eq_zero, hz]

def direction : Option ℂ → ℂ × ℂ
  | none => (0, 1)
  | some t => (1, t)

/-- Canonical coordinates with the right axis represented by `none`. -/
def chart (D : PartialAtlas.{u}) (p : D.Plane) (v : ℂ × ℂ) : Raw D.Ray :=
  if v.1 = 0 then point (D.coord p none) v.2
  else point (D.coord p (some (v.2 / v.1))) v.1

@[simp] theorem chart_zero (D : PartialAtlas.{u}) (p : D.Plane) :
    chart D p (0, 0) = none := by simp [chart]

theorem chart_scale (D : PartialAtlas.{u}) (p : D.Plane) (c : ℂ) (v : ℂ × ℂ) :
    chart D p (c * v.1, c * v.2) = scale c (chart D p v) := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hx : v.1 = 0
  · simp [chart, hx, scale_point]
  have hcx : c * v.1 ≠ 0 := mul_ne_zero hc hx
  have hratio : c * v.2 / (c * v.1) = v.2 / v.1 := by
    field_simp
  simp [chart, hx, hcx, hratio, scale_point]

theorem chart_direction (D : PartialAtlas.{u}) (p : D.Plane) (t : Option ℂ) (c : ℂ) :
    chart D p (c * (direction t).1, c * (direction t).2) = point (D.coord p t) c := by
  cases t with
  | none => simp [direction, chart]
  | some t =>
    by_cases hc : c = 0
    · simp [hc]
    · simp [direction, chart, hc]

theorem chart_injective (D : PartialAtlas.{u}) (p : D.Plane) :
    Function.Injective (chart D p) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  by_cases hx : x = 0 <;> by_cases hx' : x' = 0
  · subst x; subst x'
    have hh := (point_eq_point_iff _ _ _ _).mp (by simpa [chart] using h)
    exact Prod.ext rfl hh.1
  · subst x
    have hh := (point_eq_point_iff _ _ _ _).mp (by simpa [chart, hx'] using h)
    have hy : y ≠ 0 := by intro hy; exact hx' (hh.1.symm.trans hy)
    have hr := hh.2.resolve_left hy
    have hi := (D.coord p).injective hr
    cases hi
  · subst x'
    have hh := (point_eq_point_iff _ _ _ _).mp (by simpa [chart, hx] using h)
    have hr := hh.2.resolve_left hx
    have hi := (D.coord p).injective hr
    cases hi
  · have hh := (point_eq_point_iff _ _ _ _).mp (by simpa [chart, hx, hx'] using h)
    have hr := hh.2.resolve_left hx
    have ht := Option.some.inj ((D.coord p).injective hr)
    have hy : y = y' := by
      rw [← hh.1] at ht
      have hm := congrArg (fun z : ℂ => z * x) ht
      simpa [div_mul_cancel₀ _ hx] using hm
    exact Prod.ext hh.1 hy

/-- The local quadratic form has the two axis weights shown explicitly. -/
theorem W_chart (D : PartialAtlas.{u}) (p : D.Plane) (v : ℂ × ℂ) :
    W D (chart D p v) =
      D.weight (D.coord p (some 0)) * Complex.normSq v.1 +
      D.weight (D.coord p none) * Complex.normSq v.2 := by
  by_cases hx : v.1 = 0
  · simp [chart, hx]
  · rw [chart, if_neg hx, W_point, D.weight_coord, Complex.normSq_div]
    have hn : Complex.normSq v.1 ≠ 0 := mt Complex.normSq_eq_zero.mp hx
    field_simp
    <;> ring

/-- A nonzero point in a chart belongs to one of that plane's rays. -/
theorem chart_nonzero_ray (D : PartialAtlas.{u}) (p : D.Plane) (v : ℂ × ℂ)
    (r : D.Ray) (c : ℂ) (hc : c ≠ 0) (h : chart D p v = point r c) :
    ∃ t, D.coord p t = r := by
  by_cases hx : v.1 = 0
  · have hh := (point_eq_point_iff _ _ _ _).mp (by simpa [chart, hx] using h)
    exact ⟨none, hh.2.resolve_left (fun hz => hc (hh.1.symm.trans hz))⟩
  · have hh := (point_eq_point_iff _ _ _ _).mp (by simpa [chart, hx] using h)
    exact ⟨some (v.2 / v.1), hh.2.resolve_left hx⟩

theorem point_mem_range_chart_iff (D : PartialAtlas.{u}) (p : D.Plane)
    (r : D.Ray) (c : ℂ) (hc : c ≠ 0) :
    point r c ∈ Set.range (chart D p) ↔ ∃ t, D.coord p t = r := by
  constructor
  · rintro ⟨v, hv⟩
    exact chart_nonzero_ray D p v r c hc hv
  · rintro ⟨t, rfl⟩
    exact ⟨_, chart_direction D p t c⟩

namespace Extension

variable {D E F : PartialAtlas.{u}}

/-- Extend the ray label and preserve the nonzero complex coefficient. -/
def rawMap (f : Extension D E) : Raw D.Ray → Raw E.Ray :=
  Option.map (fun x => (f.ray x.1, x.2))

@[simp] theorem rawMap_point (f : Extension D E) (r : D.Ray) (c : ℂ) :
    rawMap f (point r c) = point (f.ray r) c := by
  by_cases hc : c = 0 <;> simp [rawMap, point, hc]

theorem rawMap_injective (f : Extension D E) : Function.Injective (rawMap f) := by
  intro x y h
  cases x with
  | none => cases y <;> simpa [rawMap] using h
  | some x =>
    cases y with
    | none => simpa [rawMap] using h
    | some y =>
      have hp : (f.ray x.1, x.2) = (f.ray y.1, y.2) := Option.some.inj h
      have hr : x.1 = y.1 := f.ray.injective (congrArg Prod.fst hp)
      have hz : x.2 = y.2 := congrArg (fun z : E.Ray × NonzeroC => z.2) hp
      exact congrArg some (Prod.ext hr hz)

theorem W_rawMap (f : Extension D E) (x : Raw D.Ray) : W E (rawMap f x) = W D x := by
  cases x with
  | none => rfl
  | some x => simp [rawMap, W, f.weight_map]

theorem rawMap_scale (f : Extension D E) (c : ℂ) (x : Raw D.Ray) :
    rawMap f (scale c x) = scale c (rawMap f x) := by
  cases x with
  | none => rfl
  | some x =>
    change rawMap f (point x.1 (c * x.2.val)) = point (f.ray x.1) (c * x.2.val)
    exact rawMap_point f x.1 (c * x.2.val)

theorem chart_map (f : Extension D E) (p : D.Plane) (v : ℂ × ℂ) :
    rawMap f (chart D p v) = chart E (f.plane p) v := by
  by_cases hx : v.1 = 0 <;> simp [chart, hx, rawMap_point, f.coord_map]

end Extension

end

end IDT.QMClosure.RawPairPlaneAtlas
