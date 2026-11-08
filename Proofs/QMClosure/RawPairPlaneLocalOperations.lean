import Proofs.QMClosure.RawPairPlaneAtlas
import Proofs.QMClosure.RawSparseConservationTests

/-!
# Pair-plane operations and weighted local sparse identities

A supplied complete weighted atlas gives a well-defined raw pair operation.
The construction uses pair charts and their one-ray intersections. All sparse
identities below are local to a single chart or to the displayed universal
families. No global vector-space structure or atlas existence is asserted.
-/

namespace IDT.QMClosure.RawPairPlaneLocalOperations

noncomputable section
open Classical RawPairPlaneAtlas
universe u

def a : ℂ := (1 + Complex.I) / 2
def b : ℂ := (1 - Complex.I) / 2

def mix₂ (X Y : ℂ × ℂ) : ℂ × ℂ :=
  (a * X.1 + b * Y.1, a * X.2 + b * Y.2)

def scalarMix (x y : ℂ) : ℂ := a * x + b * y

private theorem mix₂_diagonal (X : ℂ × ℂ) : mix₂ X X = X := by
  apply Prod.ext <;> apply Complex.ext <;>
    norm_num [mix₂, a, b, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

private theorem mix₂_square (X Y : ℂ × ℂ) :
    mix₂ (mix₂ X Y) (mix₂ Y X) = Y := by
  apply Prod.ext <;> apply Complex.ext <;>
    norm_num [mix₂, a, b, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

private theorem mix₂_scale (c : ℂ) (X Y : ℂ × ℂ) :
    mix₂ (c * X.1, c * X.2) (c * Y.1, c * Y.2) =
      (c * (mix₂ X Y).1, c * (mix₂ X Y).2) := by
  apply Prod.ext <;> simp only [mix₂] <;> ring

private theorem mix₂_direction (t : Option ℂ) (c d : ℂ) :
    mix₂ (c * (direction t).1, c * (direction t).2)
      (d * (direction t).1, d * (direction t).2) =
    ((a*c+b*d) * (direction t).1, (a*c+b*d) * (direction t).2) := by
  apply Prod.ext <;> simp only [mix₂] <;> ring

private theorem chart_mix_fiber (D : PartialAtlas.{u}) (p : D.Plane)
    (r : D.Ray) (c d : ℂ) (X Y : ℂ × ℂ)
    (hr : ∃ t, D.coord p t = r)
    (hX : chart D p X = point r c) (hY : chart D p Y = point r d) :
    chart D p (mix₂ X Y) = point r (a*c+b*d) := by
  rcases hr with ⟨t, rfl⟩
  have hx := chart_injective D p (hX.trans (chart_direction D p t c).symm)
  have hy := chart_injective D p (hY.trans (chart_direction D p t d).symm)
  rw [hx, hy, mix₂_direction, chart_direction]

private theorem chart_mix_zero_right (D : PartialAtlas.{u}) (p : D.Plane)
    (X Y : ℂ × ℂ) (hY : chart D p Y = none) :
    chart D p (mix₂ X Y) = scale a (chart D p X) := by
  have hy := chart_injective D p (hY.trans (chart_zero D p).symm)
  rw [hy]
  simpa [mix₂] using chart_scale D p a X

private theorem chart_mix_zero_left (D : PartialAtlas.{u}) (p : D.Plane)
    (X Y : ℂ × ℂ) (hX : chart D p X = none) :
    chart D p (mix₂ X Y) = scale b (chart D p Y) := by
  have hx := chart_injective D p (hX.trans (chart_zero D p).symm)
  rw [hx]
  simpa [mix₂] using chart_scale D p b Y

/-- Chart choices agree on the actual mixed raw point, including shared fibers. -/
theorem chart_mix_gluing (D : PartialAtlas.{u}) (p q : D.Plane)
    (X Y U V : ℂ × ℂ)
    (hx : chart D p X = chart D q U) (hy : chart D p Y = chart D q V) :
    chart D p (mix₂ X Y) = chart D q (mix₂ U V) := by
  generalize he : chart D p X = x at hx
  generalize hf : chart D p Y = y at hy
  cases x with
  | none =>
    rw [chart_mix_zero_left D p X Y he,
      chart_mix_zero_left D q U V hx.symm, hf, hy]
  | some x =>
    cases y with
    | none =>
      rw [chart_mix_zero_right D p X Y hf,
        chart_mix_zero_right D q U V hy.symm, he, hx]
    | some y =>
      rcases x with ⟨r, c⟩
      rcases y with ⟨s, d⟩
      have hrc : point r c.val = some (r, c) := by simp [point, c.property]
      have hsd : point s d.val = some (s, d) := by simp [point, d.property]
      have hp := chart_nonzero_ray D p X r c.val c.property (he.trans hrc.symm)
      have hq := chart_nonzero_ray D q U r c.val c.property (hx.symm.trans hrc.symm)
      by_cases hrs : r = s
      · subst s
        rw [chart_mix_fiber D p r c.val d.val X Y hp
            (he.trans hrc.symm) (hf.trans hsd.symm),
          chart_mix_fiber D q r c.val d.val U V hq
            (hx.symm.trans hrc.symm) (hy.symm.trans hsd.symm)]
      · obtain ⟨t, ht⟩ := hp
        obtain ⟨v, hv⟩ := hq
        obtain ⟨w, hw⟩ := chart_nonzero_ray D p Y s d.val d.property (hf.trans hsd.symm)
        obtain ⟨z, hz⟩ := chart_nonzero_ray D q V s d.val d.property (hy.symm.trans hsd.symm)
        have htw : t ≠ w := by intro h; apply hrs; rw [← ht, ← hw, h]
        have hpq := D.two_points p q t w v z htw (ht.trans hv.symm) (hw.trans hz.symm)
        subst q
        have hX := chart_injective D p (he.trans hx)
        have hY := chart_injective D p (hf.trans hy)
        rw [hX, hY]

private theorem ray_in_plane (D : CompleteAtlas.{u}) (r : D.Ray) :
    ∃ p t, D.coord p t = r := by
  letI := D.ray_nontrivial
  obtain ⟨s, hs⟩ := exists_ne r
  obtain ⟨p, t, v, ht, hv⟩ := D.pair_covered r s hs.symm
  exact ⟨p, t, ht⟩

/-- Every raw pair, including zero and equal-ray inputs, has a common chart. -/
theorem pair_in_chart (D : CompleteAtlas.{u}) (x y : Raw D.Ray) :
    ∃ p X Y, chart D.toPartialAtlas p X = x ∧ chart D.toPartialAtlas p Y = y := by
  letI := D.ray_nontrivial
  cases x with
  | none =>
    cases y with
    | none =>
      obtain ⟨r⟩ := (inferInstance : Nonempty D.Ray)
      obtain ⟨p, t, ht⟩ := ray_in_plane D r
      exact ⟨p, (0,0), (0,0), chart_zero _ _, chart_zero _ _⟩
    | some y =>
      obtain ⟨p, t, ht⟩ := ray_in_plane D y.1
      refine ⟨p, (0,0), (y.2.val*(direction t).1, y.2.val*(direction t).2), chart_zero _ _, ?_⟩
      rw [chart_direction, ht]
      simp [point, y.2.property]
  | some x =>
    cases y with
    | none =>
      obtain ⟨p, t, ht⟩ := ray_in_plane D x.1
      refine ⟨p, (x.2.val*(direction t).1, x.2.val*(direction t).2), (0,0), ?_, chart_zero _ _⟩
      rw [chart_direction, ht]
      simp [point, x.2.property]
    | some y =>
      have hc : ∃ p t v, D.coord p t = x.1 ∧ D.coord p v = y.1 := by
        by_cases h : x.1 = y.1
        · obtain ⟨p, t, ht⟩ := ray_in_plane D x.1
          exact ⟨p,t,t,ht,ht.trans h⟩
        · exact D.pair_covered x.1 y.1 h
      obtain ⟨p,t,v,ht,hv⟩ := hc
      refine ⟨p, (x.2.val*(direction t).1, x.2.val*(direction t).2),
        (y.2.val*(direction v).1, y.2.val*(direction v).2), ?_, ?_⟩
      · rw [chart_direction, ht]; simp [point, x.2.property]
      · rw [chart_direction, hv]; simp [point, y.2.property]

private def chosenChart (D : CompleteAtlas.{u}) (x y : Raw D.Ray) :=
  Classical.choose (pair_in_chart D x y)

private def chosenLeft (D : CompleteAtlas.{u}) (x y : Raw D.Ray) :=
  Classical.choose (Classical.choose_spec (pair_in_chart D x y))

private def chosenRight (D : CompleteAtlas.{u}) (x y : Raw D.Ray) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (pair_in_chart D x y)))

private theorem chosen_reps (D : CompleteAtlas.{u}) (x y : Raw D.Ray) :
    chart D.toPartialAtlas (chosenChart D x y) (chosenLeft D x y) = x ∧
    chart D.toPartialAtlas (chosenChart D x y) (chosenRight D x y) = y :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (pair_in_chart D x y)))

/-- The global operation is independent of the chosen common chart. -/
def m (D : CompleteAtlas.{u}) (x y : Raw D.Ray) : Raw D.Ray :=
  chart D.toPartialAtlas (chosenChart D x y) (mix₂ (chosenLeft D x y) (chosenRight D x y))

/-- The decisive exact local operation law. -/
@[simp] theorem m_chart (D : CompleteAtlas.{u}) (p : D.Plane) (X Y : ℂ × ℂ) :
    m D (chart D.toPartialAtlas p X) (chart D.toPartialAtlas p Y) =
      chart D.toPartialAtlas p (mix₂ X Y) := by
  exact chart_mix_gluing _ _ _ _ _ _ _ (chosen_reps D _ _).1 (chosen_reps D _ _).2

/-- Raw pair operation with reverse mixing as the second output. -/
def operation (D : CompleteAtlas.{u}) (xy : Raw D.Ray × Raw D.Ray) :=
  (m D xy.1 xy.2, m D xy.2 xy.1)

theorem operation_square (D : CompleteAtlas.{u}) (xy : Raw D.Ray × Raw D.Ray) :
    operation D (operation D xy) = xy.swap := by
  obtain ⟨p,X,Y,hX,hY⟩ := pair_in_chart D xy.1 xy.2
  rcases xy with ⟨x,y⟩
  dsimp at hX hY
  rw [← hX, ← hY]
  simp [operation, mix₂_square]

theorem operation_transparent (D : CompleteAtlas.{u}) (x : Raw D.Ray) :
    operation D (x,x) = (x,x) := by
  obtain ⟨p,X,Y,hX,hY⟩ := pair_in_chart D x x
  rw [← hX]
  simp [operation, mix₂_diagonal]

/-- The existing set-level contract, without a global sparse law field. -/
def contract (D : CompleteAtlas.{u}) : RawSparseConservationSelection.Contract (Raw D.Ray) where
  chosenZero := none
  operation := operation D
  weight := W D.toPartialAtlas
  vacuum := rfl
  square := operation_square D
  transparent := operation_transparent D

@[simp] theorem contract_m (D : CompleteAtlas.{u}) (x y : Raw D.Ray) :
    RawSparseConservationSelection.m (contract D) x y = m D x y := rfl

@[simp] theorem contract_A_chart (D : CompleteAtlas.{u}) (p : D.Plane) (X : ℂ × ℂ) :
    RawSparseConservationSelection.A (contract D) (chart D.toPartialAtlas p X) =
      chart D.toPartialAtlas p (mix₂ X (0,0)) := by
  change m D (chart _ p X) none = _
  rw [← chart_zero D.toPartialAtlas p, m_chart]

@[simp] theorem contract_B_chart (D : CompleteAtlas.{u}) (p : D.Plane) (X : ℂ × ℂ) :
    RawSparseConservationSelection.B (contract D) (chart D.toPartialAtlas p X) =
      chart D.toPartialAtlas p (mix₂ (0,0) X) := by
  change m D none (chart _ p X) = _
  rw [← chart_zero D.toPartialAtlas p, m_chart]

/-- Joint complex homogeneity uses raw fiber scaling, including its zero. -/
theorem m_scale (D : CompleteAtlas.{u}) (c : ℂ) (x y : Raw D.Ray) :
    m D (scale c x) (scale c y) = scale c (m D x y) := by
  obtain ⟨p,X,Y,hX,hY⟩ := pair_in_chart D x y
  rw [← hX, ← hY, ← chart_scale, ← chart_scale, m_chart, m_chart, mix₂_scale, chart_scale]

/-- Both ordered output ports respect joint complex fiber scaling. -/
theorem operation_scale (D : CompleteAtlas.{u}) (c : ℂ)
    (xy : Raw D.Ray × Raw D.Ray) :
    operation D (scale c xy.1, scale c xy.2) =
      (scale c (operation D xy).1, scale c (operation D xy).2) := by
  simp only [operation, m_scale]

/-- Mixing points on one ray is intrinsic complex-fiber mixing. -/
theorem m_point_same_ray (D : CompleteAtlas.{u}) (r : D.Ray) (c d : ℂ) :
    m D (point r c) (point r d) = point r (a*c+b*d) := by
  obtain ⟨p,t,ht⟩ := ray_in_plane D r
  rw [← ht, ← chart_direction D.toPartialAtlas p t c,
    ← chart_direction D.toPartialAtlas p t d, m_chart,
    mix₂_direction, chart_direction]

@[simp] theorem A_point (D : CompleteAtlas.{u}) (r : D.Ray) (c : ℂ) :
    RawSparseConservationSelection.A (contract D) (point r c) = point r (a*c) := by
  change m D (point r c) none = _
  rw [← point_zero r, m_point_same_ray]
  simp

@[simp] theorem B_point (D : CompleteAtlas.{u}) (r : D.Ray) (c : ℂ) :
    RawSparseConservationSelection.B (contract D) (point r c) = point r (b*c) := by
  change m D none (point r c) = _
  rw [← point_zero r, m_point_same_ray]
  simp

/-- An axis pair has half its total weight at the first mixed output. -/
theorem axis_mixed_weight (D : CompleteAtlas.{u}) (p : D.Plane) (c d : ℂ) :
    W D.toPartialAtlas (m D (point (D.coord p (some 0)) c)
      (point (D.coord p none) d)) =
    (D.weight (D.coord p (some 0))*Complex.normSq c +
      D.weight (D.coord p none)*Complex.normSq d)/2 := by
  have hc : chart D.toPartialAtlas p (c,0) = point (D.coord p (some 0)) c := by
    simpa [direction] using chart_direction D.toPartialAtlas p (some 0) c
  have hd : chart D.toPartialAtlas p (0,d) = point (D.coord p none) d := by
    simpa [direction] using chart_direction D.toPartialAtlas p none d
  rw [← hc, ← hd, m_chart, W_chart]
  norm_num [mix₂, a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

/-- Reversing the two native axes has the same first-output weight. -/
theorem axis_mixed_weight_reverse (D : CompleteAtlas.{u}) (p : D.Plane) (c d : ℂ) :
    W D.toPartialAtlas (m D (point (D.coord p none) d)
      (point (D.coord p (some 0)) c)) =
    (D.weight (D.coord p (some 0))*Complex.normSq c +
      D.weight (D.coord p none)*Complex.normSq d)/2 := by
  have hc : chart D.toPartialAtlas p (c,0) = point (D.coord p (some 0)) c := by
    simpa [direction] using chart_direction D.toPartialAtlas p (some 0) c
  have hd : chart D.toPartialAtlas p (0,d) = point (D.coord p none) d := by
    simpa [direction] using chart_direction D.toPartialAtlas p none d
  rw [← hc, ← hd, m_chart, W_chart]
  norm_num [mix₂, a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

private theorem scalar_sparse (x y z : ℂ) :
    Complex.normSq (scalarMix (scalarMix x y) (scalarMix z 0)) +
      Complex.normSq (scalarMix (scalarMix y x) (scalarMix 0 z)) =
    Complex.normSq (scalarMix x z) + Complex.normSq (scalarMix y 0) := by
  norm_num [scalarMix, a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

/-- The actual full sparse identity for triples lying in one weighted chart. -/
theorem sparse_in_chart (D : CompleteAtlas.{u}) (p : D.Plane) (X Y Z : ℂ × ℂ) :
    RawSparseConservationTests.SparseAt (contract D)
      (chart D.toPartialAtlas p X) (chart D.toPartialAtlas p Y) (chart D.toPartialAtlas p Z) := by
  unfold RawSparseConservationTests.SparseAt
  simp only [contract_m, contract_A_chart, contract_B_chart, m_chart]
  change W D.toPartialAtlas _ + W D.toPartialAtlas _ =
    W D.toPartialAtlas _ + W D.toPartialAtlas _
  simp only [W_chart, mix₂]
  have h1 := scalar_sparse X.1 Y.1 Z.1
  have h2 := scalar_sparse X.2 Y.2 Z.2
  unfold scalarMix at h1 h2
  linear_combination D.weight (D.coord p (some 0)) * h1 +
    D.weight (D.coord p none) * h2

/-- Six universal test families, each certified in a common pair chart. -/
theorem tests (D : CompleteAtlas.{u}) : RawSparseConservationTests.Tests (contract D) where
  vacuum_diagonal t := by
    obtain ⟨p,X,Y,hX,hY⟩ := pair_in_chart D t t
    change RawSparseConservationTests.SparseAt (contract D) none t t
    rw [← hX, ← chart_zero D.toPartialAtlas p]
    exact sparse_in_chart D p (0,0) X X
  vacuum_reference x y := by
    obtain ⟨p,X,Y,hX,hY⟩ := pair_in_chart D x y
    change RawSparseConservationTests.SparseAt (contract D) x y none
    rw [← hX, ← hY, ← chart_zero D.toPartialAtlas p]
    exact sparse_in_chart D p X Y (0,0)
  diagonal t z := by
    obtain ⟨p,X,Z,hX,hZ⟩ := pair_in_chart D t z
    rw [← hX, ← hZ]
    exact sparse_in_chart D p X X Z
  split_forward t z := by
    obtain ⟨p,X,Z,hX,hZ⟩ := pair_in_chart D t z
    rw [← hX, ← hZ, contract_A_chart, contract_B_chart]
    exact sparse_in_chart D p (mix₂ X (0,0)) (mix₂ (0,0) X) Z
  split_reverse t z := by
    obtain ⟨p,X,Z,hX,hZ⟩ := pair_in_chart D t z
    rw [← hX, ← hZ, contract_A_chart, contract_B_chart]
    exact sparse_in_chart D p (mix₂ (0,0) X) (mix₂ X (0,0)) Z
  vacuum_second t z := by
    obtain ⟨p,X,Z,hX,hZ⟩ := pair_in_chart D t z
    change RawSparseConservationTests.SparseAt (contract D) t none z
    rw [← hX, ← hZ, ← chart_zero D.toPartialAtlas p]
    exact sparse_in_chart D p X (0,0) Z

/-- The self-reference family also lies in the pair chart of its two inputs. -/
theorem self_sparse (D : CompleteAtlas.{u}) (x y : Raw D.Ray) :
    RawSparseConservationTests.SparseAt (contract D) x y
      (RawSparseConservationSelection.A (contract D) x) := by
  obtain ⟨p,X,Y,hX,hY⟩ := pair_in_chart D x y
  rw [← hX, ← hY, contract_A_chart]
  exact sparse_in_chart D p X Y (mix₂ X (0,0))

theorem weight_nonnegative (D : CompleteAtlas.{u}) (x : Raw D.Ray) :
    0 ≤ (contract D).weight x := W_nonnegative _ x

theorem weight_faithful (D : CompleteAtlas.{u}) (x : Raw D.Ray) :
    (contract D).weight x = 0 ↔ x = (contract D).chosenZero := W_eq_zero_iff _ x

theorem pair_conserved (D : CompleteAtlas.{u}) :
    RawSparseConservationSelection.PairConserved (contract D) :=
  RawSparseConservationTests.pair_conserved_of_tests _ (tests D) (weight_nonnegative D)

end
end IDT.QMClosure.RawPairPlaneLocalOperations
