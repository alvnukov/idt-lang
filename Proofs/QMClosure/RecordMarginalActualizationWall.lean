import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Calibrated marginals do not determine registration or archival laws

The constructions concern one declared eligible
exclusive registration slot in one context. A record is a finite set of
distinct labels, so its cardinality does not count repeated same-label clicks.
It is not a bound on excitations, coincidences, composite records, interactions,
or the entire world. A label may itself describe a composite outcome.

An empty label set means absence of the declared labels. It is not identified
with an indefinitely pending history, a terminal no-click report, or a failure
report. Those require separate protocol semantics. A distribution is a finite
mathematical statistical extension; no actual history is selected and no
deterministic or fundamentally stochastic ontology is asserted.

The same probabilities below mean the same numbers and label-presence
marginals, not an already supplied interpretation as mutually exclusive,
exhaustive categorical events. The silent and multiple-label defects are
coupled by exact accounting, not independent omitted-axiom controls.

The archive construction is a joint law of two observations, not an execution
trace or a physically nondisturbing query protocol. Preservation is not built
into a definition of read-only and then advertised as a derived conclusion.
Physical apparatus dynamics, closed-system conservation including apparatus,
particle-type stability and all standing matter-regime applicability remain
unassessed. These controls establish none of those physical bridges.

Relation to existing artifacts: IntensityActualizationBoundary already checks
the binary countMass family, its presence marginals and mean-versus-per-run
boundary. The present contribution is the arbitrary finite-label counting
identity, support boundary, archive coupling and downstream fixed-family
adapters. InternalDetectorReadoutSeparation separately distinguishes conserved
internal transport from a selected outcome or irreversible stable record.
-/

namespace IDT.QMClosure.RecordMarginalActualizationWall

noncomputable section
open scoped BigOperators

/-- A finite real probability assignment; no realized sample is a field. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonnegative : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

variable {Ω R : Type*} [Fintype Ω] [Fintype R]

def FiniteLaw.event (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then μ.mass ω else 0

def FiniteLaw.expectation (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, μ.mass ω * f ω

def FiniteLaw.positiveSupport (μ : FiniteLaw Ω) (ω : Ω) : Prop := 0 < μ.mass ω

theorem FiniteLaw.event_nonnegative (μ : FiniteLaw Ω) (P : Ω → Prop) :
    0 ≤ μ.event P := by
  classical
  apply Finset.sum_nonneg
  intro ω _
  split_ifs <;> simp [μ.nonnegative]

theorem FiniteLaw.event_zero_iff (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.event P = 0 ↔ ∀ ω, P ω → μ.mass ω = 0 := by
  classical
  have hn : ∀ ω ∈ Finset.univ, 0 ≤ (if P ω then μ.mass ω else 0) := by
    intro ω _
    split_ifs <;> simp [μ.nonnegative]
  rw [FiniteLaw.event, Finset.sum_eq_zero_iff_of_nonneg hn]
  constructor
  · intro h ω hp
    simpa [hp] using h ω (Finset.mem_univ ω)
  · intro h ω _
    by_cases hp : P ω
    · simp [hp, h ω hp]
    · simp [hp]

theorem FiniteLaw.event_not (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.event (fun ω => ¬P ω) = 1 - μ.event P := by
  classical
  have h : μ.event P + μ.event (fun ω => ¬P ω) = 1 := by
    rw [FiniteLaw.event, FiniteLaw.event, ← Finset.sum_add_distrib]
    calc
      _ = ∑ ω, μ.mass ω := by
          apply Finset.sum_congr rfl
          intro ω _
          by_cases hp : P ω <;> simp [hp]
      _ = 1 := μ.total
  linarith

/-- Label presence is a relation to a sample, not an outcome selector. -/
structure RecordModel (R Ω : Type*) [Fintype Ω] where
  law : FiniteLaw Ω
  labels : Ω → Finset R

def RecordModel.marginal (M : RecordModel R Ω) (r : R) : ℝ :=
  M.law.event (fun ω => r ∈ M.labels ω)

def RecordModel.expectedCard (M : RecordModel R Ω) : ℝ :=
  M.law.expectation (fun ω => ((M.labels ω).card : ℝ))

def RecordModel.silentMass (M : RecordModel R Ω) : ℝ :=
  M.law.event (fun ω => (M.labels ω).card = 0)

def RecordModel.multipleDistinctMass (M : RecordModel R Ω) : ℝ :=
  M.law.event (fun ω => 1 < (M.labels ω).card)

def RecordModel.expectedExcess (M : RecordModel R Ω) : ℝ :=
  M.law.expectation (fun ω => (((M.labels ω).card - 1 : ℕ) : ℝ))

theorem RecordModel.sum_marginals (M : RecordModel R Ω) :
    (∑ r, M.marginal r) = M.expectedCard := by
  classical
  unfold RecordModel.marginal FiniteLaw.event
  rw [Finset.sum_comm]
  unfold RecordModel.expectedCard FiniteLaw.expectation
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ r, if r ∈ M.labels ω then M.law.mass ω else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : r ∈ M.labels ω <;> simp [hr]
    _ = ∑ r ∈ M.labels ω, M.law.mass ω := by simp
    _ = M.law.mass ω * ((M.labels ω).card : ℝ) := by
      simp [nsmul_eq_mul, mul_comm]

private theorem nat_balance (n : ℕ) :
    (n : ℝ) + (if n = 0 then 1 else 0) = 1 + ((n - 1 : ℕ) : ℝ) := by
  cases n <;> simp [add_comm]

omit [Fintype R] in
theorem RecordModel.card_silent_excess_balance (M : RecordModel R Ω) :
    M.expectedCard + M.silentMass = 1 + M.expectedExcess := by
  classical
  have hpoint (ω : Ω) :
      M.law.mass ω * ((M.labels ω).card : ℝ) +
          (if (M.labels ω).card = 0 then M.law.mass ω else 0) =
        M.law.mass ω + M.law.mass ω * (((M.labels ω).card - 1 : ℕ) : ℝ) := by
    have h := congrArg (fun t : ℝ => M.law.mass ω * t)
      (nat_balance (M.labels ω).card)
    simpa only [mul_add, mul_ite, mul_one, mul_zero] using h
  unfold RecordModel.expectedCard RecordModel.silentMass RecordModel.expectedExcess
    FiniteLaw.expectation FiniteLaw.event
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ ω, (M.law.mass ω +
        M.law.mass ω * (((M.labels ω).card - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hz : (M.labels ω).card = 0
      · simp [hz]
      · simpa [hz] using hpoint ω
    _ = _ := by rw [Finset.sum_add_distrib, M.law.total]

theorem RecordModel.expectedCard_eq_one (M : RecordModel R Ω) (p : FiniteLaw R)
    (calibrated : ∀ r, M.marginal r = p.mass r) : M.expectedCard = 1 := by
  rw [← M.sum_marginals]
  simp_rw [calibrated]
  exact p.total

/-- The coupled defect identity uses calibrated presence marginals. -/
theorem RecordModel.silent_eq_expectedExcess (M : RecordModel R Ω) (p : FiniteLaw R)
    (calibrated : ∀ r, M.marginal r = p.mass r) :
    M.silentMass = M.expectedExcess := by
  have hb := M.card_silent_excess_balance
  rw [M.expectedCard_eq_one p calibrated] at hb
  linarith

omit [Fintype R] in
theorem RecordModel.excess_zero_iff_multiple_zero (M : RecordModel R Ω) :
    M.expectedExcess = 0 ↔ M.multipleDistinctMass = 0 := by
  classical
  have hn : ∀ ω ∈ Finset.univ,
      0 ≤ M.law.mass ω * (((M.labels ω).card - 1 : ℕ) : ℝ) := by
    intro ω _
    exact mul_nonneg (M.law.nonnegative ω) (Nat.cast_nonneg _)
  constructor
  · intro he
    apply (M.law.event_zero_iff _).2
    intro ω hmulti
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp he ω (Finset.mem_univ ω)
    have hpos : 0 < (((M.labels ω).card - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < (M.labels ω).card - 1 by omega)
    exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hpos)
  · intro hm
    have hzero := (M.law.event_zero_iff _).mp hm
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hmulti : 1 < (M.labels ω).card
    · simp [hzero ω hmulti]
    · have hz : (M.labels ω).card - 1 = 0 := by omega
      simp [hz]

theorem RecordModel.silent_zero_iff_multiple_zero (M : RecordModel R Ω)
    (p : FiniteLaw R) (calibrated : ∀ r, M.marginal r = p.mass r) :
    M.silentMass = 0 ↔ M.multipleDistinctMass = 0 := by
  rw [M.silent_eq_expectedExcess p calibrated]
  exact M.excess_zero_iff_multiple_zero

/-- Positive support is a separate premise, not a selected realized history. -/
theorem RecordModel.one_on_positive_support (M : RecordModel R Ω) (p : FiniteLaw R)
    (calibrated : ∀ r, M.marginal r = p.mass r)
    (noMultiple : M.multipleDistinctMass = 0) (ω : Ω)
    (supported : M.law.positiveSupport ω) : (M.labels ω).card = 1 := by
  have noSilent := (M.silent_zero_iff_multiple_zero p calibrated).2 noMultiple
  have hn : (M.labels ω).card ≠ 0 := by
    intro hz
    have hm := (M.law.event_zero_iff _).mp noSilent ω hz
    exact (ne_of_gt supported) hm
  have hm : ¬1 < (M.labels ω).card := by
    intro hmulti
    have hz := (M.law.event_zero_iff _).mp noMultiple ω hmulti
    exact (ne_of_gt supported) hz
  omega

section RegistrationControls

variable [DecidableEq R]

def singletonRecords (p : FiniteLaw R) : RecordModel R R where
  law := p
  labels r := {r}

theorem singletonRecords_marginal (p : FiniteLaw R) (r : R) :
    (singletonRecords p).marginal r = p.mass r := by
  simp [RecordModel.marginal, FiniteLaw.event, singletonRecords]

def perturbedMass (p : FiniteLaw R) (r s : R) (ε : ℝ) : R ⊕ Fin 2 → ℝ
  | .inl t => p.mass t - (if t = r then ε else 0) - (if t = s then ε else 0)
  | .inr _ => ε

def perturbedLabels (r s : R) : R ⊕ Fin 2 → Finset R
  | .inl t => {t}
  | .inr k => if k = 0 then ∅ else {r, s}

def perturbedLaw (p : FiniteLaw R) (r s : R) (ε : ℝ)
    (distinct : r ≠ s) (nonnegative : 0 ≤ ε)
    (belowR : ε ≤ p.mass r) (belowS : ε ≤ p.mass s) : FiniteLaw (R ⊕ Fin 2) where
  mass := perturbedMass p r s ε
  nonnegative := by
    intro z
    cases z with
    | inl t =>
      by_cases htr : t = r
      · subst t
        simpa [perturbedMass, distinct] using sub_nonneg.mpr belowR
      · by_cases hts : t = s
        · subst t
          simpa [perturbedMass, Ne.symm distinct] using sub_nonneg.mpr belowS
        · simpa [perturbedMass, htr, hts] using p.nonnegative t
    | inr k => exact nonnegative
  total := by
    rw [Fintype.sum_sum_type]
    simp [perturbedMass, Finset.sum_sub_distrib, p.total, nsmul_eq_mul]
    ring

def perturbedRecords (p : FiniteLaw R) (r s : R) (ε : ℝ)
    (distinct : r ≠ s) (nonnegative : 0 ≤ ε)
    (belowR : ε ≤ p.mass r) (belowS : ε ≤ p.mass s) :
    RecordModel R (R ⊕ Fin 2) where
  law := perturbedLaw p r s ε distinct nonnegative belowR belowS
  labels := perturbedLabels r s

theorem perturbedRecords_marginal (p : FiniteLaw R) (r s : R) (ε : ℝ)
    (distinct : r ≠ s) (nonnegative : 0 ≤ ε)
    (belowR : ε ≤ p.mass r) (belowS : ε ≤ p.mass s) (t : R) :
    (perturbedRecords p r s ε distinct nonnegative belowR belowS).marginal t =
      p.mass t := by
  classical
  unfold RecordModel.marginal FiniteLaw.event
  rw [Fintype.sum_sum_type]
  by_cases htr : t = r
  · subst t
    simp [perturbedRecords, perturbedLaw, perturbedLabels, perturbedMass,
      Fin.sum_univ_two, distinct]
  · by_cases hts : t = s
    · subst t
      simp [perturbedRecords, perturbedLaw, perturbedLabels, perturbedMass,
        Fin.sum_univ_two, Ne.symm distinct]
    · simp [perturbedRecords, perturbedLaw, perturbedLabels, perturbedMass,
        Fin.sum_univ_two, htr, hts]

theorem perturbedRecords_silentMass (p : FiniteLaw R) (r s : R) (ε : ℝ)
    (distinct : r ≠ s) (nonnegative : 0 ≤ ε)
    (belowR : ε ≤ p.mass r) (belowS : ε ≤ p.mass s) :
    (perturbedRecords p r s ε distinct nonnegative belowR belowS).silentMass = ε := by
  classical
  simp [RecordModel.silentMass, FiniteLaw.event, Fintype.sum_sum_type,
    perturbedRecords, perturbedLaw, perturbedLabels, perturbedMass]

theorem perturbedRecords_multipleDistinctMass (p : FiniteLaw R) (r s : R) (ε : ℝ)
    (distinct : r ≠ s) (nonnegative : 0 ≤ ε)
    (belowR : ε ≤ p.mass r) (belowS : ε ≤ p.mass s) :
    (perturbedRecords p r s ε distinct nonnegative belowR belowS).multipleDistinctMass =
      ε := by
  classical
  simp [RecordModel.multipleDistinctMass, FiniteLaw.event, Fintype.sum_sum_type,
    perturbedRecords, perturbedLaw, perturbedLabels, perturbedMass, Fin.sum_univ_two,
    distinct]

theorem perturbedRecords_singleton_positive (p : FiniteLaw R) (r s : R) (ε : ℝ)
    (distinct : r ≠ s) (positive : 0 < ε)
    (belowR : ε < p.mass r) (belowS : ε < p.mass s)
    (t : R) (ht : 0 < p.mass t) :
    0 < (perturbedRecords p r s ε distinct positive.le belowR.le belowS.le).law.mass
      (.inl t) := by
  by_cases htr : t = r
  · subst t
    simpa [perturbedRecords, perturbedLaw, perturbedMass, distinct] using sub_pos.mpr belowR
  · by_cases hts : t = s
    · subst t
      simpa [perturbedRecords, perturbedLaw, perturbedMass, Ne.symm distinct] using
        sub_pos.mpr belowS
    · simpa [perturbedRecords, perturbedLaw, perturbedMass, htr, hts] using ht

/-- Exact calibrated wall, not independent deletion tests for the two defects. -/
theorem calibrated_registration_wall (p : FiniteLaw R) (r s : R) (ε : ℝ)
    (distinct : r ≠ s) (positive : 0 < ε)
    (belowR : ε < p.mass r) (belowS : ε < p.mass s) :
    let M := perturbedRecords p r s ε distinct positive.le belowR.le belowS.le
    (∀ t, M.marginal t = p.mass t) ∧ M.expectedCard = 1 ∧
      M.silentMass = ε ∧ M.multipleDistinctMass = ε ∧
      (∀ t, 0 < p.mass t → 0 < M.law.mass (.inl t)) := by
  dsimp only
  refine ⟨perturbedRecords_marginal p r s ε distinct positive.le belowR.le belowS.le,
    ?_, perturbedRecords_silentMass p r s ε distinct positive.le belowR.le belowS.le,
    perturbedRecords_multipleDistinctMass p r s ε distinct positive.le belowR.le belowS.le,
    perturbedRecords_singleton_positive p r s ε distinct positive belowR belowS⟩
  exact RecordModel.expectedCard_eq_one _ p
    (perturbedRecords_marginal p r s ε distinct positive.le belowR.le belowS.le)

/-- A specialization of the existing binary control, not new binary novelty.
It supplies no detector or copying operation. -/
def balancedTwo : FiniteLaw (Fin 2) where
  mass _ := 1 / 2
  nonnegative _ := by norm_num
  total := by norm_num [Fin.sum_univ_two]

def balancedRecords : RecordModel (Fin 2) (Fin 2 ⊕ Fin 2) :=
  perturbedRecords balancedTwo 0 1 (1 / 4) (by decide) (by norm_num)
    (by norm_num [balancedTwo]) (by norm_num [balancedTwo])

theorem balancedRecords_values :
    (∀ r, balancedRecords.marginal r = 1 / 2) ∧
      balancedRecords.expectedCard = 1 ∧
      balancedRecords.silentMass = 1 / 4 ∧
      balancedRecords.multipleDistinctMass = 1 / 4 := by
  have h := calibrated_registration_wall balancedTwo 0 1 (1 / 4) (by decide)
    (by norm_num) (by norm_num [balancedTwo]) (by norm_num [balancedTwo])
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

def zeroSilentLaw (p : FiniteLaw R) : FiniteLaw (R ⊕ Unit) where
  mass := Sum.elim p.mass (fun _ => 0)
  nonnegative := by intro z; cases z <;> simp [p.nonnegative]
  total := by simp [Fintype.sum_sum_type, p.total]

def zeroSilentRecords (p : FiniteLaw R) : RecordModel R (R ⊕ Unit) where
  law := zeroSilentLaw p
  labels := Sum.elim (fun r => {r}) (fun _ => ∅)

theorem zeroSilentRecords_calibrated (p : FiniteLaw R) (r : R) :
    (zeroSilentRecords p).marginal r = p.mass r := by
  simp [RecordModel.marginal, FiniteLaw.event, zeroSilentRecords, zeroSilentLaw,
    Fintype.sum_sum_type]

/-- A zero-mass element blocks a universal statement over the sample type.
Its membership in that type does not establish physical realizability. -/
theorem zeroSilentRecords_boundary (p : FiniteLaw R) :
    (zeroSilentRecords p).silentMass = 0 ∧
      (zeroSilentRecords p).multipleDistinctMass = 0 ∧
      (zeroSilentRecords p).labels (.inr ()) = ∅ ∧
      (zeroSilentRecords p).law.mass (.inr ()) = 0 ∧
      ¬∀ ω, ((zeroSilentRecords p).labels ω).card = 1 := by
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · simp [RecordModel.silentMass, FiniteLaw.event, zeroSilentRecords, zeroSilentLaw,
      Fintype.sum_sum_type]
  · simp [RecordModel.multipleDistinctMass, FiniteLaw.event, zeroSilentRecords,
      zeroSilentLaw, Fintype.sum_sum_type]
  · intro h
    simpa [zeroSilentRecords] using h (.inr ())

end RegistrationControls

section ArchiveControls

variable [DecidableEq R]

def diagonalArchive (p : FiniteLaw R) : FiniteLaw (R × R) where
  mass z := if z.1 = z.2 then p.mass z.1 else 0
  nonnegative := by intro z; split_ifs <;> simp [p.nonnegative]
  total := by simp [Fintype.sum_prod_type, p.total]

def productArchive (p : FiniteLaw R) : FiniteLaw (R × R) where
  mass z := p.mass z.1 * p.mass z.2
  nonnegative z := mul_nonneg (p.nonnegative z.1) (p.nonnegative z.2)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, p.total]

def firstMarginal (μ : FiniteLaw (R × R)) (r : R) : ℝ := ∑ s, μ.mass (r, s)
def secondMarginal (μ : FiniteLaw (R × R)) (s : R) : ℝ := ∑ r, μ.mass (r, s)
def disagreement (μ : FiniteLaw (R × R)) : ℝ := μ.event (fun z => z.1 ≠ z.2)

theorem diagonalArchive_marginals (p : FiniteLaw R) (r : R) :
    firstMarginal (diagonalArchive p) r = p.mass r ∧
      secondMarginal (diagonalArchive p) r = p.mass r := by
  simp [firstMarginal, secondMarginal, diagonalArchive]

omit [DecidableEq R] in
theorem productArchive_marginals (p : FiniteLaw R) (r : R) :
    firstMarginal (productArchive p) r = p.mass r ∧
      secondMarginal (productArchive p) r = p.mass r := by
  simp [firstMarginal, secondMarginal, productArchive,
    ← Finset.mul_sum, ← Finset.sum_mul, p.total]

theorem diagonalArchive_disagreement (p : FiniteLaw R) :
    disagreement (diagonalArchive p) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro z _
  by_cases h : z.1 = z.2 <;> simp [diagonalArchive, h]

theorem productArchive_disagreement (p : FiniteLaw R) :
    disagreement (productArchive p) = 1 - ∑ r, p.mass r ^ 2 := by
  classical
  rw [disagreement, FiniteLaw.event_not]
  congr 1
  simp [FiniteLaw.event, productArchive, Fintype.sum_prod_type, pow_two]

theorem productArchive_disagreement_positive (p : FiniteLaw R) (r s : R)
    (distinct : r ≠ s) (positiveR : 0 < p.mass r) (positiveS : 0 < p.mass s) :
    0 < disagreement (productArchive p) := by
  classical
  have hn : ∀ (z : R × R), z ∈ Finset.univ →
      0 ≤ (if z.1 ≠ z.2 then (productArchive p).mass z else 0) := by
    intro z _
    split_ifs
    · exact (productArchive p).nonnegative z
    · exact le_rfl
  have hle := Finset.single_le_sum hn (Finset.mem_univ (r, s))
  have hm : 0 < p.mass r * p.mass s := mul_pos positiveR positiveS
  exact lt_of_lt_of_le hm (by
    simpa [distinct, productArchive, disagreement, FiniteLaw.event] using hle)

/-- Single-time calibration does not fix the two-observation coupling. -/
theorem calibrated_archive_wall (p : FiniteLaw R) (r s : R)
    (distinct : r ≠ s) (positiveR : 0 < p.mass r) (positiveS : 0 < p.mass s) :
    (∀ t, firstMarginal (diagonalArchive p) t = p.mass t ∧
      secondMarginal (diagonalArchive p) t = p.mass t) ∧
    (∀ t, firstMarginal (productArchive p) t = p.mass t ∧
      secondMarginal (productArchive p) t = p.mass t) ∧
    disagreement (diagonalArchive p) = 0 ∧
    disagreement (productArchive p) = 1 - ∑ t, p.mass t ^ 2 ∧
    0 < disagreement (productArchive p) :=
  ⟨diagonalArchive_marginals p, productArchive_marginals p,
    diagonalArchive_disagreement p, productArchive_disagreement p,
    productArchive_disagreement_positive p r s distinct positiveR positiveS⟩

end ArchiveControls

end

end IDT.QMClosure.RecordMarginalActualizationWall
