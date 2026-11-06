import Mathlib

namespace IDT.QMClosure.IntensityActualizationBoundary

noncomputable section

/-!
# Coherent intensity does not determine detector records or their update

These finite constructions separate conserved mean intensity from per-run
counts, and fixed-preparation marginals from disturbance. They do not classify
all detector physics. The projection instrument below is an explicitly supplied
comparison model, not an IDT derivation of quantum measurement.
-/

/-- A probability distribution on four explicitly enumerated outcomes. -/
structure FourOutcomeLaw (mass : Fin 4 → ℝ) : Prop where
  nonnegative : ∀ i, 0 ≤ mass i
  normalized : ∑ i, mass i = 1

def expectation (mass observable : Fin 4 → ℝ) : ℝ :=
  ∑ i, mass i * observable i

/-- Outcome order: 00, 10, 01, 11. -/
def countMass (p q c : ℝ) : Fin 4 → ℝ := ![c, p - c, q - c, c]

def firstCount : Fin 4 → ℝ := ![0, 1, 0, 1]
def secondCount : Fin 4 → ℝ := ![0, 0, 1, 1]
def totalCount (i : Fin 4) : ℝ := firstCount i + secondCount i
def coincidence : Fin 4 → ℝ := ![0, 0, 0, 1]
def exactlyOne : Fin 4 → ℝ := ![0, 1, 1, 0]

/-- The indicator names agree with the actual finite count observables. -/
theorem count_indicator_semantics (i : Fin 4) :
    coincidence i = firstCount i * secondCount i ∧
    (exactlyOne i = 1 ↔ totalCount i = 1) ∧
    (totalCount i = 0 ∨ totalCount i = 1 ∨ totalCount i = 2) := by
  fin_cases i <;> norm_num [coincidence, firstCount, secondCount, exactlyOne, totalCount]

/-- This is an admissible family, not a characterization of every detector. -/
theorem count_probability_contract (p q c : ℝ) (hsum : p + q = 1)
    (_hp : 0 ≤ p) (_hq : 0 ≤ q) (hc : 0 ≤ c) (hcp : c ≤ p) (hcq : c ≤ q) :
    FourOutcomeLaw (countMass p q c) := by
  constructor
  · intro i
    fin_cases i <;> simp [countMass] <;> linarith
  · simp [countMass, Fin.sum_univ_succ]
    linarith

theorem count_moments (p q c : ℝ) (hsum : p + q = 1) :
    expectation (countMass p q c) firstCount = p ∧
    expectation (countMass p q c) secondCount = q ∧
    expectation (countMass p q c) totalCount = 1 ∧
    expectation (countMass p q c) coincidence = c ∧
    expectation (countMass p q c) exactlyOne = 1 - 2 * c := by
  simp [expectation, countMass, firstCount, secondCount, totalCount,
    coincidence, exactlyOne, Fin.sum_univ_succ]
  constructor <;> linarith

/-- Almost-sure exactly-one means probability one, not a pointwise assertion
on outcomes of zero mass. Under the probability contract it holds iff c = 0. -/
theorem almost_sure_exactly_one_iff (p q c : ℝ) (hsum : p + q = 1)
    (_law : FourOutcomeLaw (countMass p q c)) :
    expectation (countMass p q c) exactlyOne = 1 ↔ c = 0 := by
  rw [(count_moments p q c hsum).2.2.2.2]
  constructor <;> intro h <;> linarith

/-- The total has mean one, but its variance is 2c. -/
theorem total_count_variance (p q c : ℝ) (_hsum : p + q = 1) :
    expectation (countMass p q c) (fun i => (totalCount i - 1) ^ 2) = 2 * c := by
  simp [expectation, countMass, totalCount, firstCount, secondCount,
    Fin.sum_univ_succ]
  ring

def normalizedCoincidence (p q c : ℝ) : ℝ := c / (p * q)

/-- Balanced exclusive counts, product counts, and double-or-zero correlated
counts share their single-port means. The last model is not a photon HOM claim. -/
theorem balanced_count_countermodels :
    (∀ c ∈ ([0, (1 / 4 : ℝ), 1 / 2] : List ℝ),
      FourOutcomeLaw (countMass (1 / 2) (1 / 2) c) ∧
      expectation (countMass (1 / 2) (1 / 2) c) firstCount = 1 / 2 ∧
      expectation (countMass (1 / 2) (1 / 2) c) secondCount = 1 / 2 ∧
      expectation (countMass (1 / 2) (1 / 2) c) coincidence = c) ∧
    normalizedCoincidence (1 / 2) (1 / 2) 0 = 0 ∧
    normalizedCoincidence (1 / 2) (1 / 2) (1 / 4) = 1 ∧
    normalizedCoincidence (1 / 2) (1 / 2) (1 / 2) = 2 := by
  constructor
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals
      refine ⟨count_probability_contract _ _ _ (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num), ?_⟩
      norm_num [expectation, countMass, firstCount, secondCount, coincidence,
        Fin.sum_univ_succ]
  · norm_num [normalizedCoincidence]

inductive Context where
  | Z | X
  deriving DecidableEq

/-- A persistent lookup table assigns a bit to each of two contexts. The
entries 0,1,2,3 respectively carry (0,0),(0,1),(1,0),(1,1). -/
def table : Fin 4 → Fin 2 × Fin 2 := ![(0, 0), (0, 1), (1, 0), (1, 1)]

def lookup (context : Context) (ω : Fin 4) : Fin 2 :=
  match context with
  | .Z => (table ω).1
  | .X => (table ω).2

def tableMass (pZ pX : ℝ) : Fin 4 → ℝ :=
  ![pZ * pX, pZ * (1 - pX), (1 - pZ) * pX, (1 - pZ) * (1 - pX)]

def zeroProbability (mass : Fin 4 → ℝ) (context : Context) : ℝ :=
  ∑ ω, if lookup context ω = 0 then mass ω else 0

theorem table_probability_contract (pZ pX : ℝ)
    (hz : 0 ≤ pZ) (hz' : pZ ≤ 1) (hx : 0 ≤ pX) (hx' : pX ≤ 1) :
    FourOutcomeLaw (tableMass pZ pX) := by
  constructor
  · intro i
    fin_cases i <;> simp [tableMass]
    · exact mul_nonneg hz hx
    · exact mul_nonneg hz (sub_nonneg.mpr hx')
    · exact mul_nonneg (sub_nonneg.mpr hz') hx
    · exact mul_nonneg (sub_nonneg.mpr hz') (sub_nonneg.mpr hx')
  · simp [tableMass, Fin.sum_univ_succ]
    ring

theorem table_marginals (pZ pX : ℝ) :
    zeroProbability (tableMass pZ pX) .Z = pZ ∧
    zeroProbability (tableMass pZ pX) .X = pX := by
  simp [zeroProbability, lookup, table, tableMass, Fin.sum_univ_succ]
  constructor <;> ring

/-- The outcome is exclusive and deterministic given the table. The update
returns the same table; no transport under signal operations is asserted. -/
def measure (context : Context) (ω : Fin 4) : Fin 2 × Fin 4 :=
  (lookup context ω, ω)

theorem table_exclusive (context : Context) (ω : Fin 4) :
    ((measure context ω).1 = 0 ∨ (measure context ω).1 = 1) ∧
    ¬ ((measure context ω).1 = 0 ∧ (measure context ω).1 = 1) := by
  have h := (measure context ω).1.isLt
  constructor
  · omega
  · intro ⟨h0, h1⟩
    rw [h0] at h1
    norm_num at h1

theorem table_repeatable (context : Context) (ω : Fin 4) :
    (measure context (measure context ω).2).1 = (measure context ω).1 := rfl

theorem table_nondisturbing (first second : Context) (ω : Fin 4) :
    (measure first (measure second (measure first ω).2).2).1 =
      (measure first ω).1 := rfl

/-- Every finite measurement word leaves the persistent table intact. -/
def afterWord : List Context → Fin 4 → Fin 4
  | [], ω => ω
  | context :: rest, ω => afterWord rest (measure context ω).2

theorem afterWord_eq (word : List Context) (ω : Fin 4) : afterWord word ω = ω := by
  induction word with
  | nil => rfl
  | cons context rest ih => exact ih

def finalZ0Probability (mass : Fin 4 → ℝ) : ℝ :=
  ∑ ω, if lookup .Z (afterWord [.Z, .X, .Z] ω) = 0 then mass ω else 0

theorem table_zxz_probability (pZ pX : ℝ) :
    finalZ0Probability (tableMass pZ pX) = pZ := by
  simpa only [finalZ0Probability, afterWord_eq] using (table_marginals pZ pX).1

/-! The following linear maps and quadratic weights are supplied explicitly.
Their sequential predictions are comparisons, not derived detector dynamics. -/

abbrev Signal := ℝ × ℝ
def e0 : Signal := (1, 0)
def q (v : Signal) : ℝ := v.1 ^ 2 + v.2 ^ 2
def PZ0 (v : Signal) : Signal := (v.1, 0)
def PZ1 (v : Signal) : Signal := (0, v.2)
def PXplus (v : Signal) : Signal := ((v.1 + v.2) / 2, (v.1 + v.2) / 2)
def PXminus (v : Signal) : Signal := ((v.1 - v.2) / 2, (v.2 - v.1) / 2)

theorem supplied_projector_identities (v : Signal) :
    PXplus (PXplus v) = PXplus v ∧
    PXminus (PXminus v) = PXminus v ∧
    PXminus (PXplus v) = (0, 0) ∧
    PXplus (PXminus v) = (0, 0) ∧
    PZ0 (PZ0 v) = PZ0 v := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext <;> simp [PXplus, PXminus, PZ0] <;> ring

/-- The supplied two-outcome projection instrument has nonnegative weights
and preserves their sum. Its maps remain input assumptions of the comparator. -/
theorem supplied_projection_weight_split (v : Signal) :
    0 ≤ q (PXplus v) ∧ 0 ≤ q (PXminus v) ∧
    q (PXplus v) + q (PXminus v) = q v := by
  refine ⟨add_nonneg (sq_nonneg _) (sq_nonneg _),
    add_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
  dsimp [q, PXplus, PXminus]
  ring

theorem supplied_one_shot_weights :
    q (PZ0 e0) = 1 ∧ q (PXplus e0) = 1 / 2 ∧ q (PXminus e0) = 1 / 2 := by
  norm_num [q, PZ0, PXplus, PXminus, e0]

theorem supplied_zxz_weights :
    q (PZ0 (PXplus e0)) = 1 / 4 ∧
    q (PZ0 (PXminus e0)) = 1 / 4 ∧
    q (PZ0 (PXplus e0)) + q (PZ0 (PXminus e0)) = 1 / 2 := by
  norm_num [q, PZ0, PXplus, PXminus, e0]

/-- The supplied maps for both binary contexts; zero denotes Z0 or X+. -/
def suppliedProjector (context : Context) (bit : Fin 2) (v : Signal) : Signal :=
  match context with
  | .Z => if bit = 0 then PZ0 v else PZ1 v
  | .X => if bit = 0 then PXplus v else PXminus v

def otherBit (bit : Fin 2) : Fin 2 := if bit = 0 then 1 else 0

/-- A finite binary probability contract, including exclusive outcome labels. -/
structure BinaryOutcomeLaw (mass : Fin 2 → ℝ) : Prop where
  nonnegative : ∀ bit, 0 ≤ mass bit
  normalized : ∑ bit, mass bit = 1

/-- Algebraic record contract for the explicitly supplied instrument.
Same-context repetition has the same branch state; the opposite branch has
zero weight. Weight resolution becomes a probability law on normalized inputs. -/
structure SuppliedRecordContract : Prop where
  nonnegative : ∀ context bit v, 0 ≤ q (suppliedProjector context bit v)
  resolved : ∀ context v,
    q (suppliedProjector context 0 v) + q (suppliedProjector context 1 v) = q v
  repeatable : ∀ context bit v,
    suppliedProjector context bit (suppliedProjector context bit v) =
      suppliedProjector context bit v
  opposite_zero : ∀ context bit v,
    q (suppliedProjector context (otherBit bit) (suppliedProjector context bit v)) = 0

theorem supplied_record_contract : SuppliedRecordContract := by
  constructor
  · intro context bit v
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · intro context v
    cases context <;> dsimp [suppliedProjector, q, PZ0, PZ1, PXplus, PXminus] <;> ring
  · intro context bit v
    cases context <;> fin_cases bit <;> ext <;>
      simp [suppliedProjector, PZ0, PZ1, PXplus, PXminus] <;> ring
  · intro context bit v
    cases context <;> fin_cases bit
    all_goals simp [suppliedProjector, otherBit, q, PZ0, PZ1, PXplus, PXminus]
    all_goals ring

theorem supplied_binary_probability_contract (context : Context) (v : Signal)
    (hv : q v = 1) :
    BinaryOutcomeLaw (fun bit => q (suppliedProjector context bit v)) := by
  constructor
  · intro bit
    exact supplied_record_contract.nonnegative context bit v
  · simpa [Fin.sum_univ_succ, hv] using supplied_record_contract.resolved context v

/-- The initial Z measurement is certainly Z0 and leaves e0 intact.
The omitted initial-Z1 branches of the four-path law below have zero state. -/
theorem supplied_initial_z_certain :
    PZ0 e0 = e0 ∧ PZ1 e0 = (0, 0) ∧ q e0 = 1 ∧ q (PZ1 e0) = 0 := by
  norm_num [PZ0, PZ1, e0, q]

/-- These four exclusive paths are (X+,Z0), (X+,Z1), (X-,Z0), (X-,Z1).
The initial Z0 branch leaves e0 unchanged. This law is generated by the
supplied projectors, not inferred from intensity conservation alone. -/
def suppliedZXZMass : Fin 4 → ℝ :=
  ![q (PZ0 (PXplus e0)), q (PZ1 (PXplus e0)),
    q (PZ0 (PXminus e0)), q (PZ1 (PXminus e0))]

theorem supplied_zxz_mass_quarters (i : Fin 4) : suppliedZXZMass i = 1 / 4 := by
  fin_cases i <;> norm_num [suppliedZXZMass, q, PZ0, PZ1, PXplus, PXminus, e0]

theorem supplied_zxz_probability_contract : FourOutcomeLaw suppliedZXZMass := by
  constructor
  · intro i
    rw [supplied_zxz_mass_quarters]
    norm_num
  · norm_num [Fin.sum_univ_succ, supplied_zxz_mass_quarters]

/-- With table order (00,01,10,11), the second bit is the final Z outcome. -/
def finalZ0Event (i : Fin 4) : ℝ := if (table i).2 = 0 then 1 else 0

def suppliedFinalZ0Probability : ℝ := expectation suppliedZXZMass finalZ0Event

def suppliedInitialX0Probability : ℝ :=
  ∑ i, if (table i).1 = 0 then suppliedZXZMass i else 0

def suppliedInitialX1Probability : ℝ :=
  ∑ i, if (table i).1 = 1 then suppliedZXZMass i else 0

theorem supplied_record_event_probabilities :
    suppliedFinalZ0Probability = 1 / 2 ∧
    suppliedInitialX0Probability = 1 / 2 ∧
    suppliedInitialX1Probability = 1 / 2 := by
  norm_num [suppliedFinalZ0Probability, suppliedInitialX0Probability,
    suppliedInitialX1Probability, expectation, finalZ0Event, table,
    Fin.sum_univ_succ, supplied_zxz_mass_quarters]

/-- Two fixed-preparation record laws agree on initial Z/X marginals and
satisfy exclusive binary outcomes and same-context repeatability. The lookup
law is nondisturbing, whereas the supplied projection record law assigns
probability 1/2 to final Z0 after Z-X-Z. The comparison instrument is supplied
explicitly; its update is an input to this comparison. -/
theorem fixed_preparation_update_mismatch :
    FourOutcomeLaw (tableMass 1 (1 / 2)) ∧
    FourOutcomeLaw suppliedZXZMass ∧
    SuppliedRecordContract ∧
    zeroProbability (tableMass 1 (1 / 2)) .Z = q (PZ0 e0) ∧
    zeroProbability (tableMass 1 (1 / 2)) .X = suppliedInitialX0Probability ∧
    (∀ context ω,
      ((measure context ω).1 = 0 ∨ (measure context ω).1 = 1) ∧
      ¬ ((measure context ω).1 = 0 ∧ (measure context ω).1 = 1)) ∧
    (∀ context ω, (measure context (measure context ω).2).1 =
      (measure context ω).1) ∧
    finalZ0Probability (tableMass 1 (1 / 2)) = 1 ∧
    suppliedFinalZ0Probability = 1 / 2 ∧
    finalZ0Probability (tableMass 1 (1 / 2)) ≠ suppliedFinalZ0Probability := by
  refine ⟨table_probability_contract _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num), supplied_zxz_probability_contract,
    supplied_record_contract, ?_⟩
  rw [(table_marginals 1 (1 / 2)).1, (table_marginals 1 (1 / 2)).2,
    supplied_one_shot_weights.1, supplied_record_event_probabilities.2.1,
    table_zxz_probability, supplied_record_event_probabilities.1]
  norm_num [table_exclusive, table_repeatable]

/-- Machine-visible boundary ledger; these are named scope limits, not proofs
that any complete measurement reconstruction has been accomplished. -/
inductive OpenObligation where
  | recordStatisticsAndActualization
  | calibrationTransportAfterArbitraryReversibleSignalOperations
  | preparationMixingEquivalence
  | resetAndApparatusDynamics
  | compositesAndBell
  | fullQM
  deriving DecidableEq, Repr

def openObligations : List OpenObligation := [
  .recordStatisticsAndActualization,
  .calibrationTransportAfterArbitraryReversibleSignalOperations,
  .preparationMixingEquivalence,
  .resetAndApparatusDynamics,
  .compositesAndBell,
  .fullQM]

structure ScopeBoundary where
  coherentWeightTheoremLeavesRecordsOpen : Bool
  countConservationIsExpectationUnlessCoincidenceZero : Bool
  exclusiveRepeatableRecordsDoNotFixDisturbance : Bool
  projectionComparatorIsSupplied : Bool
  lookupLawIsFixedPreparationOnly : Bool
  completeAmplitudeCarrierHasNotBeenExtendedByHiddenRecords : Bool
  fullQMStatusUpgrade : Bool

def scopeBoundary : ScopeBoundary := ⟨true, true, true, true, true, true, false⟩

theorem boundary_remains_open :
    .recordStatisticsAndActualization ∈ openObligations ∧
    .calibrationTransportAfterArbitraryReversibleSignalOperations ∈ openObligations ∧
    .preparationMixingEquivalence ∈ openObligations ∧
    .resetAndApparatusDynamics ∈ openObligations ∧
    .compositesAndBell ∈ openObligations ∧
    .fullQM ∈ openObligations ∧ scopeBoundary.fullQMStatusUpgrade = false := by
  decide

end
end IDT.QMClosure.IntensityActualizationBoundary
