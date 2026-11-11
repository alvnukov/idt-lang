import Mathlib

/-!
Finite grid identities and a conditional rigidity criterion.
All conclusions here concern an arbitrary real-valued natural grid.
-/

noncomputable section

namespace IDT.QMClosure.CountCrossIncrementRigidity

open scoped BigOperators

abbrev Grid := ℕ → ℕ → ℝ

def mixed (f : Grid) (n m : ℕ) : ℝ :=
  f (n + 1) (m + 1) - f (n + 1) m - f n (m + 1) + f n m

def SaturatedSquares (f : Grid) : Prop :=
  ∀ N, f N N - f N 0 - f 0 N + f 0 0 = 0

def Dyadic (f : Grid) : Prop := ∀ n m, f (2 * n) (2 * m) = 4 * f n m

def Refines (d : Grid) : Prop := ∀ n m,
  d (2 * n) (2 * m) + d (2 * n + 1) (2 * m) +
    d (2 * n) (2 * m + 1) + d (2 * n + 1) (2 * m + 1) = 4 * d n m

def EventuallyNonnegative (d : Grid) : Prop := ∃ D : ℕ, ∀ n m, D < n + m → 0 ≤ d n m

def EventuallyNonpositive (d : Grid) : Prop := ∃ D : ℕ, ∀ n m, D < n + m → d n m ≤ 0

theorem row_telescope (f : Grid) (n M : ℕ) :
    (∑ m ∈ Finset.range M, mixed f n m) =
      f (n + 1) M - f (n + 1) 0 - f n M + f n 0 := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, ih]; dsimp [mixed]; ring

theorem rectangle_telescope (f : Grid) (N M : ℕ) :
    (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range M, mixed f n m) =
      f N M - f N 0 - f 0 M + f 0 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, row_telescope]; ring

theorem mixed_neg (f : Grid) (n m : ℕ) :
    mixed (fun i j => -f i j) n m = -mixed f n m := by
  dsimp [mixed]
  ring

theorem saturated_neg {f : Grid} (h : SaturatedSquares f) :
    SaturatedSquares (fun n m => -f n m) := by
  intro N
  have hN := h N
  dsimp
  linarith

theorem mixed_zero_of_nonnegative {f : Grid} (h : SaturatedSquares f)
    (hs : ∀ n m, 0 ≤ mixed f n m) : ∀ n m, mixed f n m = 0 := by
  intro n m
  let N := max n m + 1
  have hn : n ∈ Finset.range N := Finset.mem_range.mpr (by dsimp [N]; omega)
  have hm : m ∈ Finset.range N := Finset.mem_range.mpr (by dsimp [N]; omega)
  have hsum : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, mixed f i j) = 0 := by
    rw [rectangle_telescope]
    exact h N
  have hrows := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.range N) => Finset.sum_nonneg
      (fun j (_ : j ∈ Finset.range N) => hs i j))).mp hsum
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.range N) => hs n j)).mp (hrows n hn) m hm

theorem mixed_zero_of_nonpositive {f : Grid} (h : SaturatedSquares f)
    (hs : ∀ n m, mixed f n m ≤ 0) : ∀ n m, mixed f n m = 0 := by
  have hz := mixed_zero_of_nonnegative (saturated_neg h) (by
    intro n m
    rw [mixed_neg]
    exact neg_nonneg.mpr (hs n m))
  intro n m
  have hh := hz n m
  rw [mixed_neg] at hh
  linarith

theorem separable_of_mixed_zero {f : Grid} (h : ∀ n m, mixed f n m = 0)
    (n m : ℕ) : f n m = f n 0 + f 0 m - f 0 0 := by
  have ht := rectangle_telescope f n m
  have hz : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, mixed f i j) = 0 := by
    simp [h]
  rw [hz] at ht
  linarith

theorem mixed_refines {f : Grid} (h : Dyadic f) : Refines (mixed f) := by
  intro n m
  have h00 := h n m
  have h10 := h (n + 1) m
  have h01 := h n (m + 1)
  have h11 := h (n + 1) (m + 1)
  simp only [Nat.mul_add, Nat.mul_one] at h10 h01 h11
  dsimp [mixed]
  simp only [Nat.add_assoc]
  linear_combination h11 - h10 - h01 + h00

/-- One child preserves or increases a parent's reading. No sign is required. -/
theorem large_child {d : Grid} (h : Refines d) (n m : ℕ) :
    ∃ r s, 2 * n ≤ r ∧ 2 * m ≤ s ∧ d n m ≤ d r s := by
  by_cases h00 : d n m ≤ d (2 * n) (2 * m)
  · exact ⟨2 * n, 2 * m, le_rfl, le_rfl, h00⟩
  by_cases h10 : d n m ≤ d (2 * n + 1) (2 * m)
  · exact ⟨2 * n + 1, 2 * m, by omega, le_rfl, h10⟩
  by_cases h01 : d n m ≤ d (2 * n) (2 * m + 1)
  · exact ⟨2 * n, 2 * m + 1, le_rfl, by omega, h01⟩
  refine ⟨2 * n + 1, 2 * m + 1, by omega, by omega, ?_⟩
  have hh := h n m
  push_neg at h00 h10 h01
  linarith

theorem refines_neg {d : Grid} (h : Refines d) : Refines (fun n m => -d n m) := by
  intro n m
  have hh := h n m
  dsimp
  linarith

theorem positive_escape {d : Grid} (h : Refines d) (h00 : d 0 0 = 0)
    {n m : ℕ} (hp : 0 < d n m) (D : ℕ) :
    ∃ r s, D < r + s ∧ d n m ≤ d r s := by
  induction D with
  | zero =>
      refine ⟨n, m, ?_, le_rfl⟩
      by_contra hh
      have hn : n = 0 := by omega
      have hm : m = 0 := by omega
      subst n; subst m
      linarith
  | succ D ih =>
      obtain ⟨r, s, hsum, hv⟩ := ih
      obtain ⟨u, v, hu, hv', hval⟩ := large_child h r s
      exact ⟨u, v, by omega, hv.trans hval⟩

theorem negative_escape {d : Grid} (h : Refines d) (h00 : d 0 0 = 0)
    {n m : ℕ} (hp : d n m < 0) (D : ℕ) :
    ∃ r s, D < r + s ∧ d r s ≤ d n m := by
  obtain ⟨r, s, hsum, hval⟩ := positive_escape (refines_neg h)
    (by simpa using congrArg Neg.neg h00) (neg_pos.mpr hp) D
  exact ⟨r, s, hsum, by simpa using hval⟩

theorem mixed_zero_of_eventual_nonnegative {f : Grid}
    (hs : SaturatedSquares f) (hd : Dyadic f) (h00 : mixed f 0 0 = 0)
    (ht : EventuallyNonnegative (mixed f)) : ∀ n m, mixed f n m = 0 := by
  apply mixed_zero_of_nonnegative hs
  intro n m
  by_contra hh
  have hn : mixed f n m < 0 := lt_of_not_ge hh
  obtain ⟨D, hD⟩ := ht
  obtain ⟨r, s, hsum, hval⟩ := negative_escape (mixed_refines hd) h00 hn D
  have htail := hD r s hsum
  linarith

theorem mixed_zero_of_eventual_nonpositive {f : Grid}
    (hs : SaturatedSquares f) (hd : Dyadic f) (h00 : mixed f 0 0 = 0)
    (ht : EventuallyNonpositive (mixed f)) : ∀ n m, mixed f n m = 0 := by
  apply mixed_zero_of_nonpositive hs
  intro n m
  by_contra hh
  have hp : 0 < mixed f n m := lt_of_not_ge hh
  obtain ⟨D, hD⟩ := ht
  obtain ⟨r, s, hsum, hval⟩ := positive_escape (mixed_refines hd) h00 hp D
  have htail := hD r s hsum
  linarith

/-- A nonseparable saturated grid has both signs, with one fixed magnitude
persisting beyond every count threshold. No fixed ray is asserted. -/
theorem both_signs_arbitrarily_far {f : Grid}
    (hs : SaturatedSquares f) (hd : Dyadic f) (h00 : mixed f 0 0 = 0)
    (hnz : ¬ ∀ n m, mixed f n m = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ D : ℕ, ∃ n m r s,
      D < n + m ∧ D < r + s ∧ ε ≤ mixed f n m ∧ mixed f r s ≤ -ε := by
  have hp : ∃ n m, 0 < mixed f n m := by
    by_contra hh
    push_neg at hh
    exact hnz (mixed_zero_of_nonpositive hs hh)
  have hn : ∃ n m, mixed f n m < 0 := by
    by_contra hh
    push_neg at hh
    exact hnz (mixed_zero_of_nonnegative hs hh)
  obtain ⟨n, m, hp⟩ := hp
  obtain ⟨r, s, hn⟩ := hn
  refine ⟨min (mixed f n m) (-mixed f r s), lt_min hp (neg_pos.mpr hn), ?_⟩
  intro D
  obtain ⟨u, v, huv, hpos⟩ := positive_escape (mixed_refines hd) h00 hp D
  obtain ⟨w, z, hwz, hneg⟩ := negative_escape (mixed_refines hd) h00 hn D
  refine ⟨u, v, w, z, huv, hwz, (min_le_left _ _).trans hpos, ?_⟩
  have hmin := min_le_right (mixed f n m) (-mixed f r s)
  linarith

end IDT.QMClosure.CountCrossIncrementRigidity
