import Proofs.QMClosure.RawMidpointGramGeometry

/-!
# Bounded three-ray midpoint countercontrol

Every radius is in the closed unit interval. Positive half attenuation commutes
with the midpoint, and the squared-distance kernel satisfies the strong
midpoint inequality at all triples. Its three-tip Gram quadratic is negative,
and a coherent global row-negating map does not exist.

The carrier keeps three distinct zero representatives. The results below
concern a kernel and its squared-distance expression. They include no checked
metric faithfulness, zero quotient, square-swap mixer, or complex-plane model.
-/

namespace IDT.QMClosure.RawTripodMidpointControl

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

/-- Three bounded rays, with their zero representatives retained. -/
abbrev V := Fin 3 × Set.Icc (0 : ℝ) 1

def G (x y : V) : ℝ :=
  if x.1 = y.1 then x.2.1 * y.2.1 else -(x.2.1 * y.2.1)

def Q (x y : V) : ℝ := RawMidpointGramGeometry.squaredDistance G x y

def half (x : V) : V :=
  (x.1, ⟨x.2.1 / 2, by
    constructor <;> linarith [x.2.2.1, x.2.2.2]⟩)

/-- On distinct rays, the longer endpoint determines the output ray.
Equal radii select the first endpoint's zero representative. -/
def mid (x y : V) : V :=
  if x.1 = y.1 then
    (x.1, ⟨(x.2.1 + y.2.1) / 2, by
      constructor <;> linarith [x.2.2.1, x.2.2.2, y.2.2.1, y.2.2.2]⟩)
  else if h : y.2.1 ≤ x.2.1 then
    (x.1, ⟨(x.2.1 - y.2.1) / 2, by
      constructor <;> linarith [x.2.2.1, x.2.2.2, y.2.2.1, y.2.2.2]⟩)
  else
    (y.1, ⟨(y.2.1 - x.2.1) / 2, by
      constructor <;> linarith [x.2.2.1, x.2.2.2, y.2.2.1, y.2.2.2]⟩)

theorem G_symmetric (x y : V) : G x y = G y x := by
  by_cases h : x.1 = y.1
  · rw [G, G, if_pos h, if_pos h.symm]
    ring
  · rw [G, G, if_neg h, if_neg (Ne.symm h)]
    ring

theorem radius_bounds (x : V) : 0 ≤ x.2.1 ∧ x.2.1 ≤ 1 := x.2.2

/-- Every kernel row has the exact positive half-scaling law. -/
theorem G_half_left (x z : V) : G (half x) z = G x z / 2 := by
  by_cases h : x.1 = z.1 <;> simp [G, half, h] <;> ring

/-- Positive half attenuation commutes with the specified raw midpoint. -/
theorem mid_half (x y : V) : mid (half x) (half y) = half (mid x y) := by
  rcases x with ⟨i, ⟨r, hr⟩⟩
  rcases y with ⟨j, ⟨s, hs⟩⟩
  by_cases hij : i = j
  · subst j
    apply Prod.ext
    · simp [mid, half]
    · apply Subtype.ext
      simp [mid, half]
      ring
  · by_cases hsr : s ≤ r
    · have hhalf : s / 2 ≤ r / 2 := by linarith
      apply Prod.ext
      · simp [mid, half, hij, hsr, hhalf]
      · apply Subtype.ext
        simp [mid, half, hij, hsr, hhalf]
        ring
    · have hhalf : ¬ s / 2 ≤ r / 2 := by linarith
      apply Prod.ext
      · simp [mid, half, hij, hsr, hhalf]
      · apply Subtype.ext
        simp [mid, half, hij, hsr, hhalf]
        ring

theorem nonnegativeSquaredDistances :
    RawMidpointGramGeometry.NonnegativeSquaredDistances G := by
  intro x y
  by_cases h : x.1 = y.1
  · simp [RawMidpointGramGeometry.squaredDistance, G, h]
    nlinarith [sq_nonneg (x.2.1 - y.2.1)]
  · simp [RawMidpointGramGeometry.squaredDistance, G, h]
    nlinarith [sq_nonneg (x.2.1 + y.2.1)]

/-- Strong squared midpoint convexity holds on the complete bounded carrier. -/
def StrongSquaredMidpointConvex : Prop :=
  ∀ z x y : V, Q z (mid x y) ≤ (Q z x + Q z y) / 2 - Q x y / 4

/-- Finite ray cases reduce to exact quadratic arithmetic. The third-ray
cases use the nonnegative products of the reference and endpoint radii. -/
theorem strongSquaredMidpointConvex : StrongSquaredMidpointConvex := by
  intro z x y
  rcases z with ⟨k, ⟨t, ht⟩⟩
  rcases x with ⟨i, ⟨r, hr⟩⟩
  rcases y with ⟨j, ⟨s, hs⟩⟩
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    dsimp [mid] <;>
    (try split_ifs) <;>
    norm_num [Q, RawMidpointGramGeometry.squaredDistance, G, Fin.ext_iff] <;>
    nlinarith [mul_nonneg ht.1 hr.1, mul_nonneg ht.1 hs.1]

theorem squaredMidpointConvex :
    RawMidpointGramGeometry.SquaredMidpointConvex G mid := by
  intro z x y
  have hs := strongSquaredMidpointConvex z x y
  have hn := nonnegativeSquaredDistances x y
  change Q z (mid x y) ≤ (Q z x + Q z y) / 2
  change 0 ≤ Q x y at hn
  linarith

def tip (i : Fin 3) : V := (i, ⟨1, by norm_num⟩)

/-- The actual three-tip kernel matrix has diagonal one and off-diagonal
minus one, giving a negative quadratic at the all-ones coefficient vector. -/
theorem tips_quadratic :
    RawGramGeometry.quadratic G tip (fun _ => 1) = -3 := by
  rw [RawGramGeometry.quadratic_three G_symmetric]
  norm_num [tip, G, Fin.ext_iff]

theorem not_three_point_positive : ¬ RawGramGeometry.GramNonnegative G 3 := by
  intro h
  have hh := h tip (fun _ => 1)
  rw [tips_quadratic] at hh
  norm_num at hh

/-- Even a completely unconstrained carrier map cannot negate all rows. -/
theorem no_coherent_antipode :
    ¬ ∃ N : V → V, ∀ x z, G (N x) z = -G x z := by
  rintro ⟨N, hN⟩
  have h0 := hN (tip 0) (tip 0)
  have h1 := hN (tip 0) (tip 1)
  have h2 := hN (tip 0) (tip 2)
  rcases hn : N (tip 0) with ⟨i, ⟨r, hr⟩⟩
  rw [hn] at h0 h1 h2
  fin_cases i <;> norm_num [G, tip, Fin.ext_iff] at h0 h1 h2 <;> linarith [hr.1]

/-- The midpoint of two distinct tips is a zero row, while averaging their
rows at the third tip gives minus one. -/
theorem not_midpointRowAverage :
    ¬ RawMidpointGramGeometry.MidpointRowAverage G mid := by
  intro h
  have hh := h (tip 0) (tip 1) (tip 2)
  norm_num [mid, tip, G, Fin.ext_iff] at hh

/-- An all-pair bounded omission control for the coherent-antipode hypothesis. -/
theorem bounded_half_midpoint_countercontrol :
    (∀ x : V, 0 ≤ x.2.1 ∧ x.2.1 ≤ 1) ∧
    (∀ x y, G x y = G y x) ∧
    (∀ x z, G (half x) z = G x z / 2) ∧
    (∀ x y, mid (half x) (half y) = half (mid x y)) ∧
    RawMidpointGramGeometry.NonnegativeSquaredDistances G ∧
    StrongSquaredMidpointConvex ∧
    RawMidpointGramGeometry.SquaredMidpointConvex G mid ∧
    ¬ RawGramGeometry.GramNonnegative G 3 ∧
    (¬ ∃ N : V → V, ∀ x z, G (N x) z = -G x z) ∧
    ¬ RawMidpointGramGeometry.MidpointRowAverage G mid := by
  exact ⟨radius_bounds, G_symmetric, G_half_left, mid_half,
    nonnegativeSquaredDistances, strongSquaredMidpointConvex, squaredMidpointConvex,
    not_three_point_positive, no_coherent_antipode, not_midpointRowAverage⟩

end
end IDT.QMClosure.RawTripodMidpointControl
