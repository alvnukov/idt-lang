import Proofs.QMClosure.RawGramGeometry

/-!
# Midpoint compatibility and finite Gram positivity

A symmetric real kernel on an arbitrary carrier has closure under real kernel
scalings. Squared-distance midpoint convexity is equivalent to averaging complete
kernel rows. Pairwise nonnegative squared distances and this averaging law then
give every finite Gram positivity inequality by exact finite row synthesis.

The scaling map has only a kernel homogeneity law. The midpoint operation has
only the stated convexity or row law. No scalar-action laws, global addition,
separation, topology, or representation are assumed.
-/

namespace IDT.QMClosure.RawMidpointGramGeometry

open scoped BigOperators

noncomputable section

variable {V : Type*} {G : V → V → ℝ}

def squaredDistance (G : V → V → ℝ) (x y : V) : ℝ :=
  G x x + G y y - 2 * G x y

def NonnegativeSquaredDistances (G : V → V → ℝ) : Prop :=
  ∀ x y, 0 ≤ squaredDistance G x y

def SquaredMidpointConvex (G : V → V → ℝ) (mid : V → V → V) : Prop :=
  ∀ z x y, squaredDistance G z (mid x y) ≤
    (squaredDistance G z x + squaredDistance G z y) / 2

def MidpointRowAverage (G : V → V → ℝ) (mid : V → V → V) : Prop :=
  ∀ x y z, G (mid x y) z = (G x z + G y z) / 2

def DistanceMidpointConvex (d : V → V → ℝ) (mid : V → V → V) : Prop :=
  ∀ z x y, d z (mid x y) ≤ (d z x + d z y) / 2

theorem affine_slope_eq_zero {C a : ℝ} (h : ∀ t : ℝ, 0 ≤ C + t * a) :
    a = 0 := by
  have hp (t : ℝ) : 0 ≤ (0 : ℝ) * (t * t) + a * t + C := by
    nlinarith [h t]
  have hd := discrim_le_zero hp
  dsimp [discrim] at hd
  nlinarith [sq_nonneg a]

/-- Reference scaling turns the midpoint inequality into a nonnegative affine
function on all real scalars, forcing the complete-row averaging law. -/
theorem midpointRowAverage_of_squaredMidpointConvex
    (hsym : ∀ x y, G x y = G y x) (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (mid : V → V → V) (hconv : SquaredMidpointConvex G mid) :
    MidpointRowAverage G mid := by
  intro x y z
  have hp (t : ℝ) : 0 ≤ (G x x + G y y) / 2 - G (mid x y) (mid x y) +
      t * (2 * G z (mid x y) - G z x - G z y) := by
    have ht := hconv (scale t z) x y
    dsimp [squaredDistance] at ht
    rw [hscale t z (mid x y), hscale t z x, hscale t z y] at ht
    linarith
  have hz := affine_slope_eq_zero hp
  rw [hsym z (mid x y), hsym z x, hsym z y] at hz
  linarith

theorem squaredDistance_midpoint (hsym : ∀ x y, G x y = G y x)
    (mid : V → V → V) (hrow : MidpointRowAverage G mid) (z x y : V) :
    squaredDistance G z (mid x y) =
      (squaredDistance G z x + squaredDistance G z y) / 2 -
        squaredDistance G x y / 4 := by
  have hx := hrow x y x
  have hy := hrow x y y
  have hh := hrow x y (mid x y)
  rw [hsym y x] at hx
  rw [hsym x (mid x y), hsym y (mid x y)] at hh
  have hdiag : G (mid x y) (mid x y) = (G x x + G y y + 2 * G x y) / 4 := by
    linarith
  have hz : G z (mid x y) = (G z x + G z y) / 2 := by
    rw [hsym z (mid x y), hrow, hsym x z, hsym y z]
  dsimp [squaredDistance]
  rw [hdiag, hz]
  ring

theorem squaredMidpointConvex_of_midpointRowAverage
    (hsym : ∀ x y, G x y = G y x)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hrow : MidpointRowAverage G mid) : SquaredMidpointConvex G mid := by
  intro z x y
  rw [squaredDistance_midpoint hsym mid hrow]
  linarith [hnonneg x y]

/-- The equivalence uses pairwise nonnegative squares in the reverse direction.
The forward implication needs only symmetry and complete real row scaling. -/
theorem squaredMidpointConvex_iff_midpointRowAverage
    (hsym : ∀ x y, G x y = G y x) (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V) :
    SquaredMidpointConvex G mid ↔ MidpointRowAverage G mid :=
  ⟨midpointRowAverage_of_squaredMidpointConvex hsym scale hscale mid,
    squaredMidpointConvex_of_midpointRowAverage hsym hnonneg mid⟩

theorem diagonal_nonnegative
    (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (hnonneg : NonnegativeSquaredDistances G) (x : V) : 0 ≤ G x x := by
  have hz (y : V) : G (scale 0 x) y = 0 := by simp only [hscale, zero_mul]
  have hp := hnonneg (scale 0 x) x
  simpa only [squaredDistance, hz, zero_add, mul_zero, sub_zero] using hp

/-- A doubled midpoint synthesizes a sum of complete kernel rows. -/
theorem scaled_midpoint_row_sum (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (mid : V → V → V) (hrow : MidpointRowAverage G mid) (x y z : V) :
    G (scale 2 (mid x y)) z = G x z + G y z := by
  rw [hscale, hrow]
  ring

/-- An anchor supplies a zero row for the empty sum. No global inhabited-carrier
assumption or raw addition operation is needed. -/
theorem exists_finite_row_sum (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (mid : V → V → V) (hrow : MidpointRowAverage G mid) (anchor : V) :
    ∀ (n : ℕ) (p : Fin n → V) (c : Fin n → ℝ),
      ∃ v : V, ∀ z, G v z = ∑ i, c i * G (p i) z := by
  intro n
  induction n with
  | zero =>
      intro p c
      exact ⟨scale 0 anchor, by intro z; simp [hscale]⟩
  | succ n ih =>
      intro p c
      obtain ⟨v, hv⟩ := ih (fun i => p i.succ) (fun i => c i.succ)
      refine ⟨scale 2 (mid (scale (c 0) (p 0)) v), ?_⟩
      intro z
      rw [scaled_midpoint_row_sum scale hscale mid hrow, hscale, hv]
      exact (Fin.sum_univ_succ (fun i => c i * G (p i) z)).symm

/-- Exact finite row synthesis identifies every Gram quadratic form with a
nonnegative kernel diagonal. The empty tuple is handled independently. -/
theorem gramNonnegative_of_midpointRowAverage
    (hsym : ∀ x y, G x y = G y x) (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hrow : MidpointRowAverage G mid) : ∀ n, RawGramGeometry.GramNonnegative G n := by
  intro n
  cases n with
  | zero =>
      intro p c
      simp [RawGramGeometry.quadratic]
  | succ n =>
      intro p c
      obtain ⟨v, hv⟩ := exists_finite_row_sum scale hscale mid hrow (p 0) (n + 1) p c
      have he : G v v = RawGramGeometry.quadratic G p c := by
        rw [hv v]
        unfold RawGramGeometry.quadratic
        apply Finset.sum_congr rfl
        intro i _
        rw [hsym (p i) v, hv (p i), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym (p j) (p i)]
        ring
      exact he ▸ diagonal_nonnegative scale hscale hnonneg v

theorem gramNonnegative_of_squaredMidpointConvex
    (hsym : ∀ x y, G x y = G y x) (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hconv : SquaredMidpointConvex G mid) : ∀ n, RawGramGeometry.GramNonnegative G n :=
  gramNonnegative_of_midpointRowAverage hsym scale hscale hnonneg mid
    (midpointRowAverage_of_squaredMidpointConvex hsym scale hscale mid hconv)

theorem nonnegativeSquaredDistances_of_distance (d : V → V → ℝ)
    (dsquare : ∀ x y, (d x y) ^ 2 = squaredDistance G x y) :
    NonnegativeSquaredDistances G := by
  intro x y
  rw [← dsquare]
  exact sq_nonneg _

/-- Ordinary nonnegative-distance midpoint convexity implies the squared
inequality. -/
theorem squaredMidpointConvex_of_distanceMidpointConvex
    (d : V → V → ℝ) (dnonneg : ∀ x y, 0 ≤ d x y)
    (dsquare : ∀ x y, (d x y) ^ 2 = squaredDistance G x y)
    (mid : V → V → V) (hconv : DistanceMidpointConvex d mid) :
    SquaredMidpointConvex G mid := by
  intro z x y
  rw [← dsquare, ← dsquare, ← dsquare]
  have hs : (d z (mid x y)) ^ 2 ≤ ((d z x + d z y) / 2) ^ 2 :=
    (sq_le_sq₀ (dnonneg z (mid x y))
      (by linarith [dnonneg z x, dnonneg z y])).2 (hconv z x y)
  nlinarith [sq_nonneg (d z x - d z y)]

theorem gramNonnegative_of_distanceMidpointConvex
    (hsym : ∀ x y, G x y = G y x) (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (d : V → V → ℝ) (dnonneg : ∀ x y, 0 ≤ d x y)
    (dsquare : ∀ x y, (d x y) ^ 2 = squaredDistance G x y)
    (mid : V → V → V) (hconv : DistanceMidpointConvex d mid) :
    ∀ n, RawGramGeometry.GramNonnegative G n :=
  gramNonnegative_of_squaredMidpointConvex hsym scale hscale
    (nonnegativeSquaredDistances_of_distance d dsquare) mid
    (squaredMidpointConvex_of_distanceMidpointConvex d dnonneg dsquare mid hconv)

/-- Finite Gram positivity supplies the triangle inequality. Together with the
exact midpoint variance identity, its reverse form yields distance convexity. -/
theorem distanceMidpointConvex_of_midpointRowAverage
    (hsym : ∀ x y, G x y = G y x) (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (d : V → V → ℝ) (dnonneg : ∀ x y, 0 ≤ d x y)
    (dsquare : ∀ x y, (d x y) ^ 2 = squaredDistance G x y)
    (mid : V → V → V) (hrow : MidpointRowAverage G mid) :
    DistanceMidpointConvex d mid := by
  have hgram := gramNonnegative_of_midpointRowAverage hsym scale hscale
    (nonnegativeSquaredDistances_of_distance d dsquare) mid hrow
  have htri := (RawGramGeometry.triangle_iff_three_point hsym scale hscale d
    dnonneg dsquare).2 (hgram 3)
  have hdsym (x y : V) : d x y = d y x := by
    have hxy := dsquare x y
    have hyx := dsquare y x
    dsimp [squaredDistance] at hxy hyx
    rw [hsym y x] at hyx
    nlinarith [dnonneg x y, dnonneg y x]
  intro z x y
  have hleft := htri z y x
  rw [hdsym y x] at hleft
  have hright := htri z x y
  have hdiff : (d z x - d z y) ^ 2 ≤ (d x y) ^ 2 := by
    have hp := mul_nonneg
      (by linarith : 0 ≤ d x y - (d z x - d z y))
      (by linarith : 0 ≤ d x y + (d z x - d z y))
    nlinarith
  have he := squaredDistance_midpoint hsym mid hrow z x y
  rw [← dsquare, ← dsquare, ← dsquare, ← dsquare] at he
  have hs : (d z (mid x y)) ^ 2 ≤ ((d z x + d z y) / 2) ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ (dnonneg z (mid x y))
    (by linarith [dnonneg z x, dnonneg z y])).1 hs

theorem distanceMidpointConvex_iff_midpointRowAverage
    (hsym : ∀ x y, G x y = G y x) (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (d : V → V → ℝ) (dnonneg : ∀ x y, 0 ≤ d x y)
    (dsquare : ∀ x y, (d x y) ^ 2 = squaredDistance G x y)
    (mid : V → V → V) :
    DistanceMidpointConvex d mid ↔ MidpointRowAverage G mid :=
  ⟨fun hconv => midpointRowAverage_of_squaredMidpointConvex hsym scale hscale mid
      (squaredMidpointConvex_of_distanceMidpointConvex d dnonneg dsquare mid hconv),
    distanceMidpointConvex_of_midpointRowAverage hsym scale hscale d dnonneg dsquare mid⟩

end

end IDT.QMClosure.RawMidpointGramGeometry
