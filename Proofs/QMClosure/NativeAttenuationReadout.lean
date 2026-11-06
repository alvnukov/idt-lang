import Proofs.QMClosure.NativeWireEffectSpan
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Conditional basis-calibrated selection by rational attenuation events

The four coordinate families below are definitions, not an assertion of native
event availability. Domain membership, midpoint accounting, positivity, total
normalization and basis calibration are explicit hypotheses. A circuit adapter
may identify these coordinates with finite native circuit selected readouts;
membership in the supplied event domain remains an explicit bridge. The only limiting argument is the
scalar geometric fact `(1/16)^m → 0`; no continuity of the readout is assumed.

The conclusion concerns one basis-calibrated rational coordinate readout. It
does not construct outcomes, select arbitrary prepared vectors, establish a
density-matrix representation, or close the original Born or full QM problem.
-/

namespace IDT.QMClosure.NativeAttenuationReadout

noncomputable section

open scoped BigOperators
open NativeWireEffectSpan Filter Topology

def t (m : ℕ) : ℚ := (1 / 16 : ℚ) ^ m

def E0 {n : ℕ} (q : UpperPair n) (m : ℕ) : V n :=
  (t m ^ 2 / 2) • P q.val.1 + (1 / 2 : ℚ) • P q.val.2 + (t m / 2) • Y q

def E2 {n : ℕ} (q : UpperPair n) (m : ℕ) : V n :=
  (t m ^ 2 / 8) • P q.val.1 + (1 / 2 : ℚ) • P q.val.2 + (t m / 4) • X q

def E4 {n : ℕ} (q : UpperPair n) (m : ℕ) : V n :=
  (t m ^ 2 / 32) • P q.val.1 + (1 / 2 : ℚ) • P q.val.2 - (t m / 8) • Y q

def E6 {n : ℕ} (q : UpperPair n) (m : ℕ) : V n :=
  (t m ^ 2 / 128) • P q.val.1 + (1 / 2 : ℚ) • P q.val.2 - (t m / 16) • X q

def identity (n : ℕ) : V n := ∑ i, P i

theorem t_pos (m : ℕ) : 0 < t m := pow_pos (by norm_num) _

/-- A scalar limit, with no probability/readout continuity hypothesis. -/
theorem t_tendsto_zero : Tendsto (fun m => (t m : ℝ)) atTop (𝓝 0) := by
  simpa [t] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by norm_num : (1 / 16 : ℝ) < 1))

theorem four_bounds (a x y s : ℝ) (hs : 0 < s)
    (h0 : 0 ≤ s ^ 2 / 2 * a + s / 2 * y)
    (h2 : 0 ≤ s ^ 2 / 8 * a + s / 4 * x)
    (h4 : 0 ≤ s ^ 2 / 32 * a - s / 8 * y)
    (h6 : 0 ≤ s ^ 2 / 128 * a - s / 16 * x) :
    (-a * s ≤ y ∧ y ≤ a * s / 4) ∧
      (-a * s / 2 ≤ x ∧ x ≤ a * s / 8) := by
  have hyl : 0 ≤ s * (a * s + y) := by nlinarith [h0]
  have hyu : 0 ≤ s * (a * s / 4 - y) := by nlinarith [h4]
  have hxl : 0 ≤ s * (a * s / 2 + x) := by nlinarith [h2]
  have hxu : 0 ≤ s * (a * s / 8 - x) := by nlinarith [h6]
  have := (mul_nonneg_iff_of_pos_left hs).mp hyl
  have := (mul_nonneg_iff_of_pos_left hs).mp hyu
  have := (mul_nonneg_iff_of_pos_left hs).mp hxl
  have := (mul_nonneg_iff_of_pos_left hs).mp hxu
  constructor <;> constructor <;> linarith

theorem scalar_geometric_squeeze (a x y : ℝ)
    (h : ∀ m, (-a * (t m : ℝ) ≤ y ∧ y ≤ a * (t m : ℝ) / 4) ∧
      (-a * (t m : ℝ) / 2 ≤ x ∧ x ≤ a * (t m : ℝ) / 8)) :
    x = 0 ∧ y = 0 := by
  have hyl : 0 ≤ y := le_of_tendsto'
    (by simpa using t_tendsto_zero.const_mul (-a)) (fun m => (h m).1.1)
  have hyu : y ≤ 0 := ge_of_tendsto'
    (by simpa using (t_tendsto_zero.const_mul a).div_const 4) (fun m => (h m).1.2)
  have hxl : 0 ≤ x := le_of_tendsto'
    (by simpa using (t_tendsto_zero.const_mul (-a)).div_const 2) (fun m => (h m).2.1)
  have hxu : x ≤ 0 := ge_of_tendsto'
    (by simpa using (t_tendsto_zero.const_mul a).div_const 8) (fun m => (h m).2.2)
  exact ⟨le_antisymm hxu hxl, le_antisymm hyu hyl⟩

theorem pair_bounds {n : ℕ} (ell : V n →ₗ[ℚ] ℝ) (q : UpperPair n)
    (hz : ell (P q.val.2) = 0) (m : ℕ)
    (h0 : 0 ≤ ell (E0 q m)) (h2 : 0 ≤ ell (E2 q m))
    (h4 : 0 ≤ ell (E4 q m)) (h6 : 0 ≤ ell (E6 q m)) :
    (-ell (P q.val.1) * (t m : ℝ) ≤ ell (Y q) ∧
      ell (Y q) ≤ ell (P q.val.1) * (t m : ℝ) / 4) ∧
    (-ell (P q.val.1) * (t m : ℝ) / 2 ≤ ell (X q) ∧
      ell (X q) ≤ ell (P q.val.1) * (t m : ℝ) / 8) := by
  simp only [E0, E2, E4, E6, map_add, map_sub, map_smul, Rat.smul_def,
    Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, hz, mul_zero, add_zero] at h0 h2 h4 h6
  exact four_bounds _ _ _ _ (by exact_mod_cast t_pos m) h0 h2 h4 h6

/-- Positivity on the explicitly supplied countable family kills both cross
coordinates against a zero-calibrated second basis direction. -/
theorem pair_vanish {n : ℕ} (ell : V n →ₗ[ℚ] ℝ) (q : UpperPair n)
    (hz : ell (P q.val.2) = 0)
    (h0 : ∀ m, 0 ≤ ell (E0 q m)) (h2 : ∀ m, 0 ≤ ell (E2 q m))
    (h4 : ∀ m, 0 ≤ ell (E4 q m)) (h6 : ∀ m, 0 ≤ ell (E6 q m)) :
    ell (X q) = 0 ∧ ell (Y q) = 0 :=
  scalar_geometric_squeeze _ _ _ fun m =>
    pair_bounds ell q hz m (h0 m) (h2 m) (h4 m) (h6 m)

theorem recover_Y {n : ℕ} (q : UpperPair n) :
    Y q = (2 : ℚ) • E0 q 0 - P q.val.1 - P q.val.2 := by
  ext c
  simp only [E0, t, pow_zero, one_pow, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem recover_X {n : ℕ} (q : UpperPair n) :
    X q = (4 : ℚ) • E2 q 0 - (1 / 2 : ℚ) • P q.val.1 - (2 : ℚ) • P q.val.2 := by
  ext c
  simp only [E2, t, pow_zero, one_pow, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem native_attenuation_span_eq_top {n : ℕ} (D : Set (V n))
    (hP : ∀ i, P i ∈ D) (h0 : ∀ q, E0 q 0 ∈ D) (h2 : ∀ q, E2 q 0 ∈ D) :
    Submodule.span ℚ D = ⊤ := by
  classical
  let S := Submodule.span ℚ D
  have hp (i : Fin n) : P i ∈ S := Submodule.subset_span (hP i)
  have hy (q : UpperPair n) : Y q ∈ S := by
    rw [recover_Y]
    exact S.sub_mem (S.sub_mem (S.smul_mem 2 (Submodule.subset_span (h0 q))) (hp _)) (hp _)
  have hx (q : UpperPair n) : X q ∈ S := by
    rw [recover_X]
    exact S.sub_mem (S.sub_mem (S.smul_mem 4 (Submodule.subset_span (h2 q)))
      (S.smul_mem _ (hp _))) (S.smul_mem _ (hp _))
  have hb (c : Coord n) : Pi.single c (1 : ℚ) ∈ S := by
    rcases c with i | ⟨q, b⟩
    · exact hp i
    · cases b
      · exact hx q
      · exact hy q
  apply top_unique
  intro v _
  have hv : v = ∑ c, v c • (Pi.single c (1 : ℚ) : V n) := by
    ext c
    simp [Pi.single_apply, apply_ite]
  rw [hv]
  exact S.sum_mem fun c _ => S.smul_mem _ (hb c)

theorem basis_calibrated_selection {n : ℕ} (ell : V (n + 1) →ₗ[ℚ] ℝ)
    (hnorm : ell (identity (n + 1)) = 1) (hcal : ell (P 0) = 1)
    (hdiag : ∀ i, 0 ≤ ell (P i))
    (h0 : ∀ q m, 0 ≤ ell (E0 q m)) (h2 : ∀ q m, 0 ≤ ell (E2 q m))
    (h4 : ∀ q m, 0 ≤ ell (E4 q m)) (h6 : ∀ q m, 0 ≤ ell (E6 q m)) :
    ∀ v, ell v = (v (.inl 0) : ℝ) := by
  classical
  have hsum : ∑ i, ell (P i) = 1 := by simpa [identity] using hnorm
  have herase : ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), ell (P i) = 0 := by
    have he := Finset.sum_erase_add Finset.univ (fun i => ell (P i))
      (Finset.mem_univ (0 : Fin (n + 1)))
    change (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), ell (P i)) + ell (P 0) =
      ∑ i, ell (P i) at he
    rw [hsum, hcal] at he
    linarith
  have hd (i : Fin (n + 1)) (hi : i ≠ 0) : ell (P i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hdiag j)).mp herase i
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
  have hxy (q : UpperPair (n + 1)) : ell (X q) = 0 ∧ ell (Y q) = 0 := by
    have hj : q.val.2 ≠ 0 := by
      intro hz
      have hlt := q.property
      rw [hz] at hlt
      exact (not_lt_of_ge (Fin.zero_le _)) hlt
    exact pair_vanish ell q (hd _ hj) (h0 q) (h2 q) (h4 q) (h6 q)
  have hb (c : Coord (n + 1)) :
      ell (Pi.single c (1 : ℚ)) = if c = .inl 0 then 1 else 0 := by
    rcases c with i | ⟨q, b⟩
    · by_cases hi : i = 0
      · simpa [hi, P] using hcal
      · simpa [P, hi] using hd i hi
    · cases b
      · simpa [X] using (hxy q).1
      · simpa [Y] using (hxy q).2
  intro v
  have hv : v = ∑ c, v c • (Pi.single c (1 : ℚ) : V (n + 1)) := by
    ext c
    simp [Pi.single_apply, apply_ite]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, hb]
  simp

/-- Conditional selection on the midpoint domain. All attenuation-event
availability and readout-accounting laws remain explicit supplied premises. -/
theorem domain_basis_calibrated_selection {n : ℕ}
    (D : Set (V (n + 1))) (p : V (n + 1) → ℝ)
    (hzero : (0 : V (n + 1)) ∈ D) (hpzero : p 0 = 0)
    (hclosed : ∀ x ∈ D, ∀ y ∈ D, (1 / 2 : ℚ) • (x + y) ∈ D)
    (hpres : ∀ x ∈ D, ∀ y ∈ D,
      p ((1 / 2 : ℚ) • (x + y)) = (p x + p y) / 2)
    (hP : ∀ i, P i ∈ D)
    (h0 : ∀ q m, E0 q m ∈ D) (h2 : ∀ q m, E2 q m ∈ D)
    (h4 : ∀ q m, E4 q m ∈ D) (h6 : ∀ q m, E6 q m ∈ D)
    (hId : identity (n + 1) ∈ D) (hnorm : p (identity (n + 1)) = 1)
    (hcal : p (P 0) = 1) (hpos : ∀ v ∈ D, 0 ≤ p v) :
    ∀ v ∈ D, p v = (v (.inl 0) : ℝ) := by
  obtain ⟨ell, hagree, _⟩ :=
    DyadicMixtureLinearization.exists_unique_rational_linear_extension D p hzero hpzero
      hclosed hpres (native_attenuation_span_eq_top D hP (fun q => h0 q 0) (fun q => h2 q 0))
  have hselect := basis_calibrated_selection ell
    (by rw [hagree _ hId]; exact hnorm)
    (by rw [hagree _ (hP 0)]; exact hcal)
    (fun i => by rw [hagree _ (hP i)]; exact hpos _ (hP i))
    (fun q m => by rw [hagree _ (h0 q m)]; exact hpos _ (h0 q m))
    (fun q m => by rw [hagree _ (h2 q m)]; exact hpos _ (h2 q m))
    (fun q m => by rw [hagree _ (h4 q m)]; exact hpos _ (h4 q m))
    (fun q m => by rw [hagree _ (h6 q m)]; exact hpos _ (h6 q m))
  intro v hv
  rw [← hagree v hv]
  exact hselect v

end

end IDT.QMClosure.NativeAttenuationReadout
