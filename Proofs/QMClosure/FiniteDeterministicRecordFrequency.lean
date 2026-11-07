import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Frequencies of records from a finite deterministic complete state

A fixed map on a finite state space has an eventually periodic orbit. Boolean
records along a single orbit therefore have a limiting empirical frequency
`k / ell`, with `k ≤ ell` and `0 < ell ≤ card S`.

The state is the complete recurrent memory: no external input stream or changing
transition rule is an argument of this model. The result concerns an exact
asymptotic frequency on one trajectory, not finite samples, stochastic dynamics,
or averages over an ensemble of initial states. It makes no physical claim.
-/

namespace IDT.QMClosure.FiniteDeterministicRecordFrequency

open Function Filter Finset
open scoped Topology

variable {S : Type*}

/-- Number of true records in the first `N` states, including the initial state. -/
def recordCount (step : S → S) (record : S → Bool) (N : ℕ) (s : S) : ℕ :=
  birkhoffSum step (fun x => if record x then 1 else 0) N s

/-- Empirical frequency; the value at `N = 0` is zero by real division conventions. -/
noncomputable def recordFrequency (step : S → S) (record : S → Bool)
    (s : S) (N : ℕ) : ℝ :=
  (recordCount step record N s : ℝ) / (N : ℝ)

theorem recordCount_le (step : S → S) (record : S → Bool) (N : ℕ) (s : S) :
    recordCount step record N s ≤ N := by
  unfold recordCount birkhoffSum
  calc
    _ ≤ ∑ _t ∈ range N, (1 : ℕ) := by
      apply sum_le_sum
      intro t ht
      dsimp only
      split <;> omega
    _ = N := by simp

theorem recordCount_add (step : S → S) (record : S → Bool) (m n : ℕ) (s : S) :
    recordCount step record (m + n) s =
      recordCount step record m s + recordCount step record n (step^[m] s) :=
  birkhoffSum_add step _ m n s

private theorem recordCount_mul_of_periodic (step : S → S) (record : S → Bool)
    {ell : ℕ} {s : S} (hp : IsPeriodicPt step ell s) (q : ℕ) :
    recordCount step record (q * ell) s = q * recordCount step record ell s := by
  induction q with
  | zero => simp [recordCount, birkhoffSum]
  | succ q ih =>
    rw [Nat.succ_mul, recordCount_add, (hp.const_mul q).eq, ih]
    ring

private theorem recordCount_div_mod_of_periodic (step : S → S) (record : S → Bool)
    {ell : ℕ} {s : S} (hp : IsPeriodicPt step ell s) (N : ℕ) :
    recordCount step record N s =
      (N / ell) * recordCount step record ell s + recordCount step record (N % ell) s := by
  conv_lhs => rw [← Nat.div_add_mod N ell, Nat.mul_comm ell (N / ell)]
  rw [recordCount_add, recordCount_mul_of_periodic step record hp,
    (hp.const_mul (N / ell)).eq]

/-- Complete-cycle counting proves convergence for a periodic initial state. -/
theorem tendsto_recordFrequency_of_periodic (step : S → S) (record : S → Bool)
    {ell : ℕ} {s : S} (hell : 0 < ell) (hp : IsPeriodicPt step ell s) :
    Tendsto (recordFrequency step record s) atTop
      (𝓝 ((recordCount step record ell s : ℝ) / (ell : ℝ))) := by
  have hellR : (ell : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hell)
  have hrem : Tendsto (fun N : ℕ => ((N % ell : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 0) := tendsto_mod_div_atTop_nhds_zero_nat hell
  have hquot : Tendsto (fun N : ℕ => ((N / ell : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 (1 / (ell : ℝ))) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hrem).div_const (ell : ℝ)
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hdivision : ((N / ell : ℕ) : ℝ) * (ell : ℝ) +
        ((N % ell : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast (show (N / ell) * ell + N % ell = N by
        simpa only [Nat.mul_comm] using Nat.div_add_mod N ell)
    field_simp [hNR, hellR]
    nlinarith
  have htail : Tendsto (fun N : ℕ => (recordCount step record (N % ell) s : ℝ) /
      (N : ℝ)) atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
      (b := (0 : ℝ)) (B := (ell : ℝ))
    · exact Eventually.of_forall fun N => Nat.cast_nonneg _
    · exact Eventually.of_forall fun N => by
        exact_mod_cast (recordCount_le step record (N % ell) s).trans
          (Nat.mod_lt N hell).le
    · exact tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds (x := (recordCount step record ell s : ℝ))).mul
    hquot).add htail
  simp only [mul_one_div, add_zero] at h
  apply h.congr
  intro N
  unfold recordFrequency
  rw [recordCount_div_mod_of_periodic step record hp N]
  push_cast
  ring

/-- Removing a fixed finite prefix preserves a limiting record frequency. -/
theorem tendsto_recordFrequency_of_shift (step : S → S) (record : S → Bool)
    (s : S) (T : ℕ) {p : ℝ}
    (h : Tendsto (recordFrequency step record (step^[T] s)) atTop (𝓝 p)) :
    Tendsto (recordFrequency step record s) atTop (𝓝 p) := by
  have hprefix : Tendsto (fun N : ℕ => (recordCount step record T s : ℝ) /
      ((N : ℝ) + (T : ℝ))) atTop (𝓝 0) := by
    have h0 := (tendsto_add_atTop_iff_nat T).2
      (tendsto_const_div_atTop_nhds_zero_nat (recordCount step record T s : ℝ))
    simpa only [Nat.cast_add] using h0
  have hratio : Tendsto (fun N : ℕ => (N : ℝ) / ((N : ℝ) + (T : ℝ)))
      atTop (𝓝 1) := tendsto_natCast_div_add_atTop (T : ℝ)
  have htotal := hprefix.add (h.mul hratio)
  simp only [mul_one, zero_add] at htotal
  apply (tendsto_add_atTop_iff_nat T).1
  apply htotal.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hden : (N : ℝ) + (T : ℝ) ≠ 0 := by positivity
  unfold recordFrequency
  rw [Nat.add_comm N T, recordCount_add]
  push_cast
  field_simp
  ring

/-- Finite complete memory forces entry into a cycle of at most `card S` states. -/
theorem exists_periodic_tail [Fintype S] (step : S → S) (s : S) :
    ∃ T ell : ℕ, 0 < ell ∧ ell ≤ Fintype.card S ∧ IsPeriodicPt step ell (step^[T] s) := by
  obtain ⟨m, n, heq, hne⟩ : ∃ m n : ℕ, step^[m] s = step^[n] s ∧ m ≠ n := by
    simpa [Injective] using not_injective_infinite_finite (step^[·] s)
  have ordered : ∀ a b : ℕ, a < b → step^[a] s = step^[b] s →
      ∃ T ell : ℕ, 0 < ell ∧ ell ≤ Fintype.card S ∧
        IsPeriodicPt step ell (step^[T] s) := by
    intro a b hab heq'
    have hp : IsPeriodicPt step (b - a) (step^[a] s) := by
      change step^[b - a] (step^[a] s) = step^[a] s
      rw [← iterate_add_apply, Nat.sub_add_cancel hab.le]
      exact heq'.symm
    exact ⟨a, minimalPeriod step (step^[a] s),
      hp.minimalPeriod_pos (Nat.sub_pos_of_lt hab), minimalPeriod_le_card,
      isPeriodicPt_minimalPeriod step (step^[a] s)⟩
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ordered m n hlt heq
  · exact ordered n m hlt heq.symm

/-- The whole trajectory is periodic after a finite transient; periodicity is derived. -/
theorem exists_eventually_periodic_orbit [Fintype S] (step : S → S) (s : S) :
    ∃ T ell : ℕ, 0 < ell ∧ ell ≤ Fintype.card S ∧
      ∀ t : ℕ, step^[T + t + ell] s = step^[T + t] s := by
  obtain ⟨T, ell, hell, hcard, hp⟩ := exists_periodic_tail step s
  refine ⟨T, ell, hell, hcard, fun t => ?_⟩
  have hpt := (hp.apply_iterate t).eq
  simpa only [← iterate_add_apply, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpt

/-- Exact limiting frequency on a single finite deterministic trajectory is a bounded fraction. -/
theorem exists_recordFrequency_limit [Fintype S] (step : S → S) (record : S → Bool) (s : S) :
    ∃ k ell : ℕ, k ≤ ell ∧ 0 < ell ∧ ell ≤ Fintype.card S ∧
      Tendsto (recordFrequency step record s) atTop (𝓝 ((k : ℝ) / (ell : ℝ))) := by
  obtain ⟨T, ell, hell, hcard, hp⟩ := exists_periodic_tail step s
  refine ⟨recordCount step record ell (step^[T] s), ell,
    recordCount_le step record ell (step^[T] s), hell, hcard, ?_⟩
  exact tendsto_recordFrequency_of_shift step record s T
    (tendsto_recordFrequency_of_periodic step record hell hp)

/-- Any prescribed exact asymptotic frequency has a denominator bounded by complete state count. -/
theorem fraction_of_recordFrequency_tendsto [Fintype S] (step : S → S)
    (record : S → Bool) (s : S) {p : ℝ}
    (hp : Tendsto (recordFrequency step record s) atTop (𝓝 p)) :
    ∃ k ell : ℕ, k ≤ ell ∧ 0 < ell ∧ ell ≤ Fintype.card S ∧ p = (k : ℝ) / (ell : ℝ) := by
  obtain ⟨k, ell, hk, hell, hcard, hlimit⟩ := exists_recordFrequency_limit step record s
  exact ⟨k, ell, hk, hell, hcard, tendsto_nhds_unique hp hlimit⟩

end IDT.QMClosure.FiniteDeterministicRecordFrequency
