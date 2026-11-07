import Proofs.QMClosure.RecordMarginalActualizationWall
import Proofs.QMClosure.ConditionalRecordProbabilities

/-!
# Fixed-family adapters for registration and archival countermodels

Every adapter retains the same supplied Family,
channels, source/target weights, and reconstructed effects. Only a finite
statistical registration or two-observation coupling is added. The arbitrary
event-domain probability adapter retains DomainLaw, matched-projector domain
membership and calibration, positive source weight, and branch membership.

The numbers and label-presence marginals are preserved. They are not silently
identified with an already exclusive/exhaustive categorical event semantics.
The zero-label and multiple-distinct-label defects are coupled, not independent
axiom deletion controls. A Finset does not count repeated same-label clicks.
No extension of the entire effect-domain event interpretation is asserted:
identifying sums or refinements with unions of these sample predicates is an
additional bridge, which the multiple-label control need not satisfy.

The declared slot belongs to one eligible measurement context. Multi-excitation,
coincidence and composite records remain allowed outside or inside the supplied
outcome labels. There is no rule requiring one click per interaction or world.
Absence of these labels is distinct from pending execution, terminal no-click,
and failure. Existing normalized formulas do not supply missing physical rates
for those cases. No realized sample or history, update instrument, deterministic
ontology, or fundamentally stochastic ontology is selected.

The mathematical carrier is not an assumption of an independent physical
object possessing all properties before interaction. This adapter neither
requires nor refutes a persisting carrier. Apparatus must ultimately obey the
same rules; no closed-system conservation theorem is supplied, and expected
distinct-label count is not excitation, energy, charge or angular-momentum
conservation.

Applicability to Bose-Einstein condensation, superfluidity, superconductivity,
quasiparticles, entanglement, indistinguishability, topological phases,
decoherence and stable physical records is unassessed. No particle spectrum,
physical actualization, physical copying availability or full QM is derived.
-/

namespace IDT.QMClosure.RecordMarginalActualizationAdapter

noncomputable section
open RawOperationalHilbert NormalizedRecordEffects
open CalibratedEffectActualization DyadicEffectDomainActualization
open ConditionalRecordProbabilities RecordMarginalActualizationWall
open scoped BigOperators ComplexOrder

variable {V R : Type*} [Fintype R] [DecidableEq R] {U : R → Type*}
variable {source : Data V} {target : ∀ r, Data (U r)}

/-- A mathematical normalized vector from the unchanged raw record weights. -/
def ratioLaw (f : Family source target) (x : V)
    (positive : 0 < source.weight x) : FiniteLaw R where
  mass r := (target r).weight (f.channel r x) / source.weight x
  nonnegative r := div_nonneg ((target r).nonnegative (f.channel r x)) positive.le
  total := by
    rw [← Finset.sum_div, f.total, div_self (ne_of_gt positive)]

omit [DecidableEq R] in
theorem ratioLaw_mass (f : Family source target) (x : V)
    (positive : 0 < source.weight x) (r : R) :
    (ratioLaw f x positive).mass r =
      (target r).weight (f.channel r x) / source.weight x := rfl

omit [DecidableEq R] in
/-- Links the same effect to the same supplied channel, without a new channel. -/
theorem fixed_effect_weight (f : Family source target) (x : V) (r : R) :
    inner ℂ (source.feature x) (f.effect r (source.feature x)) =
      ((target r).weight (f.channel r x) : ℂ) :=
  f.effect_expectation r x

omit [DecidableEq R] in
/-- Feature normalization is mathematical, not a physical preparation control. -/
theorem fixed_effect_ratio (f : Family source target) (x : V)
    (positive : 0 < source.weight x) (r : R) :
    (inner ℂ (normalizedFeature source x)
      (f.effect r (normalizedFeature source x))).re = (ratioLaw f x positive).mass r :=
  normalized_effect_expectation f x r

theorem ratio_registration_wall (f : Family source target) (x : V)
    (positive : 0 < source.weight x) (r s : R) (ε : ℝ)
    (distinct : r ≠ s) (epsilonPositive : 0 < ε)
    (belowR : ε < (target r).weight (f.channel r x) / source.weight x)
    (belowS : ε < (target s).weight (f.channel s x) / source.weight x) :
    let p := ratioLaw f x positive
    let M := perturbedRecords p r s ε distinct epsilonPositive.le belowR.le belowS.le
    (∀ t, (singletonRecords p).marginal t =
      (target t).weight (f.channel t x) / source.weight x) ∧
    (∀ t, M.marginal t = (target t).weight (f.channel t x) / source.weight x) ∧
    M.expectedCard = 1 ∧ M.silentMass = ε ∧ M.multipleDistinctMass = ε ∧
    (∀ t, 0 < p.mass t → 0 < M.law.mass (.inl t)) := by
  dsimp only
  refine ⟨singletonRecords_marginal (ratioLaw f x positive), ?_⟩
  exact calibrated_registration_wall (ratioLaw f x positive) r s ε distinct
    epsilonPositive belowR belowS

theorem ratio_archive_wall (f : Family source target) (x : V)
    (positive : 0 < source.weight x) (r s : R) (distinct : r ≠ s)
    (positiveR : 0 < (target r).weight (f.channel r x))
    (positiveS : 0 < (target s).weight (f.channel s x)) :
    let p := ratioLaw f x positive
    (∀ t, firstMarginal (diagonalArchive p) t = p.mass t ∧
      secondMarginal (diagonalArchive p) t = p.mass t) ∧
    (∀ t, firstMarginal (productArchive p) t = p.mass t ∧
      secondMarginal (productArchive p) t = p.mass t) ∧
    disagreement (diagonalArchive p) = 0 ∧
    disagreement (productArchive p) = 1 - ∑ t, p.mass t ^ 2 ∧
    0 < disagreement (productArchive p) :=
  calibrated_archive_wall (ratioLaw f x positive) r s distinct
    (div_pos positiveR positive) (div_pos positiveS positive)

variable {D : Set (Op (H := source.Hilbert))}
variable {probability : Op (H := source.Hilbert) → ℝ}

/-- Every premise of the existing conditional record theorem is retained. -/
def conditionalLaw (f : Family source target) (x : V)
    (positive : 0 < source.weight x) (law : DomainLaw D probability)
    (matched_mem : projector (normalizedFeature source x) ∈ D)
    (calibrated : probability (projector (normalizedFeature source x)) = 1)
    (branch_mem : ∀ r, f.effect r ∈ D) : FiniteLaw R where
  mass r := probability (f.effect r)
  nonnegative r := (record_probability_bounds f law branch_mem r).1
  total := record_probabilities_sum f x positive law matched_mem calibrated branch_mem

omit [DecidableEq R] in
theorem conditionalLaw_eq_ratioLaw_mass (f : Family source target) (x : V)
    (positive : 0 < source.weight x) (law : DomainLaw D probability)
    (matched_mem : projector (normalizedFeature source x) ∈ D)
    (calibrated : probability (projector (normalizedFeature source x)) = 1)
    (branch_mem : ∀ r, f.effect r ∈ D) (r : R) :
    (conditionalLaw f x positive law matched_mem calibrated branch_mem).mass r =
      (ratioLaw f x positive).mass r :=
  record_probability f x positive law matched_mem calibrated branch_mem r

theorem conditional_registration_wall (f : Family source target) (x : V)
    (positive : 0 < source.weight x) (law : DomainLaw D probability)
    (matched_mem : projector (normalizedFeature source x) ∈ D)
    (calibrated : probability (projector (normalizedFeature source x)) = 1)
    (branch_mem : ∀ r, f.effect r ∈ D)
    (r s : R) (ε : ℝ) (distinct : r ≠ s) (epsilonPositive : 0 < ε)
    (belowR : ε < probability (f.effect r))
    (belowS : ε < probability (f.effect s)) :
    let p := conditionalLaw f x positive law matched_mem calibrated branch_mem
    let M := perturbedRecords p r s ε distinct epsilonPositive.le belowR.le belowS.le
    (∀ t, p.mass t = (target t).weight (f.channel t x) / source.weight x) ∧
    (∀ t, M.marginal t = probability (f.effect t)) ∧ M.expectedCard = 1 ∧
      M.silentMass = ε ∧ M.multipleDistinctMass = ε ∧
      (∀ t, 0 < probability (f.effect t) → 0 < M.law.mass (.inl t)) := by
  dsimp only
  refine ⟨record_probability f x positive law matched_mem calibrated branch_mem, ?_⟩
  exact calibrated_registration_wall
    (conditionalLaw f x positive law matched_mem calibrated branch_mem) r s ε
    distinct epsilonPositive belowR belowS

theorem conditional_archive_wall (f : Family source target) (x : V)
    (positive : 0 < source.weight x) (law : DomainLaw D probability)
    (matched_mem : projector (normalizedFeature source x) ∈ D)
    (calibrated : probability (projector (normalizedFeature source x)) = 1)
    (branch_mem : ∀ r, f.effect r ∈ D)
    (r s : R) (distinct : r ≠ s)
    (positiveR : 0 < probability (f.effect r))
    (positiveS : 0 < probability (f.effect s)) :
    let p := conditionalLaw f x positive law matched_mem calibrated branch_mem
    (∀ t, p.mass t = (target t).weight (f.channel t x) / source.weight x) ∧
    (∀ t, firstMarginal (diagonalArchive p) t = probability (f.effect t) ∧
      secondMarginal (diagonalArchive p) t = probability (f.effect t)) ∧
    (∀ t, firstMarginal (productArchive p) t = probability (f.effect t) ∧
      secondMarginal (productArchive p) t = probability (f.effect t)) ∧
    disagreement (diagonalArchive p) = 0 ∧
    disagreement (productArchive p) = 1 - ∑ t, probability (f.effect t) ^ 2 ∧
    0 < disagreement (productArchive p) := by
  dsimp only
  refine ⟨record_probability f x positive law matched_mem calibrated branch_mem, ?_⟩
  exact calibrated_archive_wall
    (conditionalLaw f x positive law matched_mem calibrated branch_mem) r s
    distinct positiveR positiveS

end

end IDT.QMClosure.RecordMarginalActualizationAdapter
