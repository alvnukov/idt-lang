import Proofs.QMClosure.OperationalQuadraticReconstruction
import Proofs.QMClosure.PreparationRecordObstruction

namespace IDT.QMClosure.NativePreparationParityWitness

noncomputable section

/-!
# Native intensity shares and the conditional preparation-record obstruction

The supplied positive reference is additional data. The reconstruction's
original monoid operations determine the four preparations and the actual
two-port readout shares. No complex consistency witness, scalar multiplication,
or serial product is used in these proofs.

The quadratic identities below concern averaged real readouts. They do not
identify probabilistic mixtures, full distributions, or complete operational
states. The finite probability obstruction applies only when an additional
actualization/calibration bridge supplies the stated probability marginals and
shared stochastic responses.
-/

open OperationalQuadraticReconstruction

section QuadraticIdentities

variable {U : Type*} [AddCommGroup U]

/-- The parallelogram law already forces a zero vacuum readout. -/
theorem quadratic_zero (Q : U → ℝ)
    (para : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) :
    Q 0 = 0 := by
  have h := para 0 0
  simp only [zero_add, sub_self] at h
  linarith

theorem quadratic_double (Q : U → ℝ)
    (para : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (e : U) : Q (e + e) = 4 * Q e := by
  have h := para e e
  rw [sub_self, quadratic_zero Q para] at h
  linarith

theorem quadratic_triple (Q : U → ℝ)
    (para : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (e : U) : Q (e + e + e) = 9 * Q e := by
  have h := para (e + e) e
  have hs : e + e - e = e := by abel
  rw [hs, quadratic_double Q para e] at h
  linarith

/-- Both parity sums agree for every quadratic readout on every additive
abelian carrier. No equality of the underlying distributions follows. -/
theorem parity_quadratic_sums (Q : U → ℝ)
    (even : ∀ x, Q (-x) = Q x)
    (para : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (E F : U) :
    Q (E + E + F) + Q (E - (F + F)) = 5 * (Q E + Q F) ∧
    Q (E + E - F) + Q (E + (F + F)) = 5 * (Q E + Q F) := by
  have h₁ := para (E + F) E
  have h₂ := para (E - F) F
  have h₃ := para (E - F) E
  have h₄ := para (E + F) F
  have h₅ := para E F
  have e₁ : E + F + E = E + E + F := by abel
  have e₂ : E + F - E = F := by abel
  have e₃ : E - F + F = E := by abel
  have e₄ : E - F - F = E - (F + F) := by abel
  have e₅ : E - F + E = E + E - F := by abel
  have e₆ : E - F - E = -F := by abel
  have e₇ : E + F + F = E + (F + F) := by abel
  have e₈ : E + F - F = E := by abel
  rw [e₁, e₂] at h₁
  rw [e₃, e₄] at h₂
  rw [e₅, e₆, even] at h₃
  rw [e₇, e₈] at h₄
  constructor <;> linarith

/-- Equal sign randomization cancels the cross term at the level of means. -/
theorem sign_randomized_reference_mean (Q : U → ℝ)
    (even : ∀ x, Q (-x) = Q x)
    (para : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (v reference : U) :
    (Q (v + reference) + Q (-v + reference)) / 2 = Q v + Q reference := by
  have h := para v reference
  have hs : -v + reference = -(v - reference) := by abel
  rw [hs, even]
  linarith

/-- The two sign-randomized parity averages agree for every common reference.
The denominator is common to the compared ensembles. -/
theorem reference_parity_mean (Q : U → ℝ)
    (even : ∀ x, Q (-x) = Q x)
    (para : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (E F reference : U) :
    (((Q (E + E + F + reference) + Q (-(E + E + F) + reference)) / 2) +
      ((Q (E - (F + F) + reference) + Q (-(E - (F + F)) + reference)) / 2)) / 2 =
    (((Q (E + E - F + reference) + Q (-(E + E - F) + reference)) / 2) +
      ((Q (E + (F + F) + reference) + Q (-(E + (F + F)) + reference)) / 2)) / 2 := by
  rw [sign_randomized_reference_mean Q even para,
    sign_randomized_reference_mean Q even para,
    sign_randomized_reference_mean Q even para,
    sign_randomized_reference_mean Q even para]
  obtain ⟨h₁, h₂⟩ := parity_quadratic_sums Q even para E F
  linarith

/-- An additive readout channel preserves the hypotheses of the mean identity. -/
theorem quadratic_after_additive_map {D : Type*} [AddCommGroup D]
    (L : U →+ D) (Q : D → ℝ)
    (even : ∀ x, Q (-x) = Q x)
    (para : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) :
    (∀ x, Q (L (-x)) = Q (L x)) ∧
    (∀ x y, Q (L (x + y)) + Q (L (x - y)) =
      2 * Q (L x) + 2 * Q (L y)) := by
  constructor
  · intro x
    rw [map_neg, even]
  · intro x y
    simpa only [map_add, map_sub] using para (L x) (L y)

end QuadraticIdentities

section Native

variable {V : Type*} [AddCommMonoid V]

/-- Preparation order is 00, 01, 10, 11. The inverse is the operation's
reconstructed double phase, so this definition requires only the original monoid. -/
def preparation (T : (V × V) →+ (V × V)) (e : V) : Fin 4 → V × V :=
  ![(e + e, e), (e + e, phase T (phase T e)),
    (e, e + e), (e, phase T (phase T (e + e)))]

/-- Simultaneous sign reversal is expressed with the reconstructed double phase. -/
def antipodePair (T : (V × V) →+ (V × V)) (p : V × V) : V × V :=
  (phase T (phase T p.1), phase T (phase T p.2))

def signMean (T : (V × V) →+ (V × V)) (Q : (V × V) → ℝ)
    (p reference : V × V) : ℝ :=
  (Q (p + reference) + Q (antipodePair T p + reference)) / 2

/-- The actual four native preparations have equal parity means for every
quadratic probe and every common reference after equal sign randomization.
This statement is about readout means, not probability laws or complete states. -/
theorem native_reference_parity_mean (T : (V × V) →+ (V × V)) (W : V → ℝ)
    (r : Reconstruction T W) (e : V) (Q : (V × V) → ℝ)
    (even : ∀ p, Q (antipodePair T p) = Q p)
    (para : ∀ p q, Q (p + q) + Q (p + antipodePair T q) = 2 * Q p + 2 * Q q)
    (reference : V × V) :
    (signMean T Q (preparation T e 0) reference +
      signMean T Q (preparation T e 3) reference) / 2 =
    (signMean T Q (preparation T e 1) reference +
      signMean T Q (preparation T e 2) reference) / 2 := by
  letI : AddCommGroup V := groupFromAntipodes (phase T) r.antipodes
  have quarter : ∀ z, phase T (phase T z) = -z := fun _ => rfl
  have he : ∀ p, Q (-p) = Q p := even
  have hp : ∀ p q, Q (p + q) + Q (p - q) = 2 * Q p + 2 * Q q := para
  simpa [preparation, signMean, antipodePair, quarter] using
    reference_parity_mean Q he hp ((e, 0) : V × V) ((0, e) : V × V) reference

def directShare (W : V → ℝ) (p : V × V) : ℝ :=
  W p.1 / (W p.1 + W p.2)

/-- Apply the reconstructed phase to the second port, then the actual supplied T.
The denominator is the same input total used by the direct share. -/
def generatedShare (T : (V × V) →+ (V × V)) (W : V → ℝ) (p : V × V) : ℝ :=
  W (T (p.1, phase T p.2)).1 / (W p.1 + W p.2)

/-- Global sign reversal preserves both readout shares. Consequently equal
sign randomization retains the four numerical tables at the intensity level. -/
theorem shares_global_sign_invariant (T : (V × V) →+ (V × V)) (W : V → ℝ)
    (r : Reconstruction T W) (p : V × V) :
    directShare W (antipodePair T p) = directShare W p ∧
    generatedShare T W (antipodePair T p) = generatedShare T W p := by
  letI : AddCommGroup V := groupFromAntipodes (phase T) r.antipodes
  have even : ∀ z, W (-z) = W z := r.even
  have hinv : antipodePair T p = -p := rfl
  rw [hinv]
  constructor
  · change W (-p.1) / (W (-p.1) + W (-p.2)) =
      W p.1 / (W p.1 + W p.2)
    simp only [even]
  · change W (T (-p.1, phase T (-p.2))).1 / (W (-p.1) + W (-p.2)) =
      W (T (p.1, phase T p.2)).1 / (W p.1 + W p.2)
    rw [(phase T).map_neg]
    have hp : (-p.1, -(phase T p.2)) = -(p.1, phase T p.2) := rfl
    rw [hp, T.map_neg]
    change W (-(T (p.1, phase T p.2)).1) / (W (-p.1) + W (-p.2)) =
      W (T (p.1, phase T p.2)).1 / (W p.1 + W p.2)
    simp only [even]

/-- The actual operation yields the sum and difference weights. This uses its
routing theorem and reconstructed half/mixed-square laws, not a supplied
Hadamard map or the complex consistency witness. -/
theorem actual_crossed_weights (T : (V × V) →+ (V × V)) (W : V → ℝ)
    (r : Reconstruction T W) (x y : V) :
    W (T (x, phase T y)).1 = W (x + y) / 2 ∧
    W (T (x, phase T y)).2 = W (x + phase T (phase T y)) / 2 := by
  letI : AddCommGroup V := groupFromAntipodes (phase T) r.antipodes
  have quarter : ∀ z, phase T (phase T z) = -z := fun _ => rfl
  have route : ∀ a b, T (a, b) =
      PositiveMixerQuadraticReadout.mixer (phase T) (half T) a b := by
    intro a b
    rw [congrFun r.routing]
    change (half T (a + phase T a) +
      half T (b + phase T (phase T (phase T b))),
      half T (a + phase T (phase T (phase T a))) +
      half T (b + phase T b)) =
      (half T (a + phase T a) + half T (b - phase T b),
       half T (a - phase T a) + half T (b + phase T b))
    rw [quarter (phase T a), quarter (phase T b)]
    rfl
  have ha : ∀ z, W (PositiveMixerQuadraticReadout.coefficientA
      (phase T) (half T) z) = W z / 2 := by
    intro z
    change W (half T (z + phase T z)) = W z / 2
    rw [r.half_scaling, r.mixed_square]
    ring
  have hb : ∀ z, W (PositiveMixerQuadraticReadout.coefficientB
      (phase T) (half T) z) = W z / 2 := by
    intro z
    have h := PositiveMixerQuadraticReadout.phase_coefficientA
      (phase T) (half T) r.halves quarter z
    have hw := congrArg W h
    rw [r.phase_invariant] at hw
    have he : ∀ v, W (-v) = W v := r.even
    rw [he] at hw
    rw [← hw, ha]
  rw [route, PositiveMixerQuadraticReadout.mixer_crossed
    (phase T) (half T) r.halves quarter, ha, hb]
  constructor <;> rfl

/-- All four preparations have the same nonzero-reference total. -/
theorem native_weight_tables (T : (V × V) →+ (V × V)) (W : V → ℝ)
    (r : Reconstruction T W) (e : V) (a : Fin 4) :
    W (preparation T e a).1 = ![4 * W e, 4 * W e, W e, W e] a ∧
    W (preparation T e a).2 = ![W e, W e, 4 * W e, 4 * W e] a ∧
    W (T ((preparation T e a).1, phase T (preparation T e a).2)).1 =
      ![9 * W e / 2, W e / 2, 9 * W e / 2, W e / 2] a ∧
    W (T ((preparation T e a).1, phase T (preparation T e a).2)).2 =
      ![W e / 2, 9 * W e / 2, W e / 2, 9 * W e / 2] a := by
  letI : AddCommGroup V := groupFromAntipodes (phase T) r.antipodes
  have quarter : ∀ z, phase T (phase T z) = -z := fun _ => rfl
  have even : ∀ z, W (-z) = W z := r.even
  have para : ∀ x y, W (x + y) + W (x - y) = 2 * W x + 2 * W y := by
    intro x y
    exact r.parallelogram x y
  have htwo := quadratic_double W para e
  have hthree := quadratic_triple W para e
  have hnegdouble : W (-e - e) = 4 * W e := by
    have hs : -e - e = -(e + e) := by abel
    rw [hs, even, htwo]
  have e₁ : e + e + -e = e := by abel
  have e₃ : e + (e + e) = e + e + e := by abel
  have hc := actual_crossed_weights T W r
    (preparation T e a).1 (preparation T e a).2
  fin_cases a <;>
    simp [preparation, quarter, htwo, hthree, even, e₁, e₃, hnegdouble,
      ← sub_eq_add_neg] at hc ⊢ <;>
    exact hc

theorem native_total (T : (V × V) →+ (V × V)) (W : V → ℝ)
    (r : Reconstruction T W) (e : V) (a : Fin 4) :
    W (preparation T e a).1 + W (preparation T e a).2 = 5 * W e := by
  obtain ⟨h₁, h₂, _, _⟩ := native_weight_tables T W r e a
  rw [h₁, h₂]
  fin_cases a <;> norm_num <;> ring

/-- Exact rational intensity shares follow from a supplied positive reference.
They have not been identified here with probabilities of events. -/
theorem native_shares (T : (V × V) →+ (V × V)) (W : V → ℝ)
    (r : Reconstruction T W) (e : V) (positive_reference : 0 < W e)
    (a : Fin 4) :
    directShare W (preparation T e a) = PreparationRecordObstruction.targetZ a ∧
    generatedShare T W (preparation T e a) = PreparationRecordObstruction.targetX a := by
  obtain ⟨h₁, _, h₃, _⟩ := native_weight_tables T W r e a
  have htotal := native_total T W r e a
  have hn : W e ≠ 0 := ne_of_gt positive_reference
  unfold directShare generatedShare
  rw [htotal, h₁, h₃]
  constructor <;> fin_cases a <;>
    norm_num [PreparationRecordObstruction.targetZ, PreparationRecordObstruction.targetX] <;>
    field_simp [hn] <;> ring

/-- The sign-reversed representatives have the same exact intensity targets.
No identification with probability marginals is made by this theorem. -/
theorem native_antipode_shares (T : (V × V) →+ (V × V)) (W : V → ℝ)
    (r : Reconstruction T W) (e : V) (positive_reference : 0 < W e)
    (a : Fin 4) :
    directShare W (antipodePair T (preparation T e a)) =
      PreparationRecordObstruction.targetZ a ∧
    generatedShare T W (antipodePair T (preparation T e a)) =
      PreparationRecordObstruction.targetX a := by
  obtain ⟨hz, hx⟩ := shares_global_sign_invariant T W r (preparation T e a)
  rw [hz, hx]
  exact native_shares T W r e positive_reference a

/-- Arithmetic decoding score of two tables, without any probabilistic
interpretation of their entries. -/
def decodingScore (Z X : Fin 4 → ℝ) : ℝ :=
  (Z 0 + X 0 + Z 1 + 1 - X 1 + 1 - Z 2 + X 2 + 2 - Z 3 - X 3) / 8

theorem native_decoding_score (T : (V × V) →+ (V × V)) (W : V → ℝ)
    (r : Reconstruction T W) (e : V) (positive_reference : 0 < W e) :
    decodingScore (fun a => directShare W (preparation T e a))
      (fun a => generatedShare T W (preparation T e a)) = 17 / 20 := by
  have hz : ∀ a, directShare W (preparation T e a) =
      PreparationRecordObstruction.targetZ a :=
    fun a => (native_shares T W r e positive_reference a).1
  have hx : ∀ a, generatedShare T W (preparation T e a) =
      PreparationRecordObstruction.targetX a :=
    fun a => (native_shares T W r e positive_reference a).2
  simp only [decodingScore, hz, hx]
  norm_num [PreparationRecordObstruction.targetZ, PreparationRecordObstruction.targetX,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- Conditional bridge only: calibration of supplied finite probability laws
to the reconstructed intensity shares forces a parity-record separation. -/
theorem actualized_record_obstruction {Ω : Type*} [Fintype Ω]
    (T : (V × V) →+ (V × V)) (W : V → ℝ) (r : Reconstruction T W)
    (e : V) (positive_reference : 0 < W e)
    (μ : Fin 4 → Ω → ℝ) (rZ rX : Ω → ℝ)
    (law : PreparationRecordObstruction.ProbabilityFamily μ)
    (hZ : PreparationRecordObstruction.Response rZ) (hX : PreparationRecordObstruction.Response rX)
    (actualizationZ : ∀ a, PreparationRecordObstruction.marginal μ rZ a =
      directShare W (preparation T e a))
    (actualizationX : ∀ a, PreparationRecordObstruction.marginal μ rX a =
      generatedShare T W (preparation T e a)) :
    PreparationRecordObstruction.success μ rZ rX = 17 / 20 ∧
    2 / 5 ≤ PreparationRecordObstruction.parityTV μ ∧ ¬ PreparationRecordObstruction.ParityEquivalent μ := by
  have hcal : PreparationRecordObstruction.Calibrated μ rZ rX := by
    constructor
    · intro a
      rw [actualizationZ a, (native_shares T W r e positive_reference a).1]
    · intro a
      rw [actualizationX a, (native_shares T W r e positive_reference a).2]
  exact ⟨PreparationRecordObstruction.calibrated_success μ rZ rX law hcal,
    PreparationRecordObstruction.calibrated_parityTV_lower_bound μ rZ rX law hZ hX hcal,
    PreparationRecordObstruction.no_calibrated_parity_equivalent_family μ rZ rX law hZ hX hcal⟩

end Native

/-- A supplied real quadratic probe distinguishes intensity distributions
despite equal parity means. It is not a newly reconstructed physical detector. -/
def suppliedQuadraticProbe (p : ℝ × ℝ) : ℝ := (p.1 + 2 * p.2) ^ 2

theorem supplied_probe_quadratic :
    (∀ p, suppliedQuadraticProbe (-p) = suppliedQuadraticProbe p) ∧
    (∀ p q, suppliedQuadraticProbe (p + q) + suppliedQuadraticProbe (p - q) =
      2 * suppliedQuadraticProbe p + 2 * suppliedQuadraticProbe q) := by
  constructor <;> intros <;> simp [suppliedQuadraticProbe] <;> ring

theorem supplied_probe_values :
    suppliedQuadraticProbe (2, 1) = 16 ∧
    suppliedQuadraticProbe (2, -1) = 0 ∧
    suppliedQuadraticProbe (1, 2) = 25 ∧
    suppliedQuadraticProbe (1, -2) = 9 := by
  norm_num [suppliedQuadraticProbe]

/-- Equal means do not imply equality of completed intensity distributions:
the even support {16,9} and odd support {0,25} are disjoint. -/
theorem supplied_probe_mean_without_distribution_equality :
    (suppliedQuadraticProbe (2, 1) + suppliedQuadraticProbe (1, -2)) / 2 =
      (suppliedQuadraticProbe (2, -1) + suppliedQuadraticProbe (1, 2)) / 2 ∧
    Disjoint ({suppliedQuadraticProbe (2, 1), suppliedQuadraticProbe (1, -2)} : Set ℝ)
      {suppliedQuadraticProbe (2, -1), suppliedQuadraticProbe (1, 2)} := by
  norm_num [suppliedQuadraticProbe, Set.disjoint_left]

/-- Explicit assumptions, conclusions, and open bridges; no proof-status change. -/
inductive BoundaryRole where
  | suppliedReconstructionLaws
  | suppliedPositiveReference
  | reconstructedActualOperationIntensityShares
  | reconstructedUniversalQuadraticParityMeans
  | commonDenominatorRequiredForNormalizedMeanComparison
  | equalQuadraticMeansNotFullDistributionsOrOperationalStateEquality
  | probabilityMixtureAndEventActualizationOpen
  | finiteProbabilityNormalizationAndSharedResponsesSupplied
  | conditionalFiniteRecordParityTVLowerBound
  | hiddenRecordEquivalenceNeedsPreparationNoncontextuality
  | jointlyObservableRecordEquivalenceIsStrongerOperationalCondition
  | suppliedQuadraticProbeOnly
  | noHilbertScalarOrSerialMultiplicationPremise
  | noQuantumMeasurementOrFullQMClaim
  | noPrimitiveInevitabilityOrStatusUpgrade
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole :=
  [.suppliedReconstructionLaws, .suppliedPositiveReference,
   .reconstructedActualOperationIntensityShares, .reconstructedUniversalQuadraticParityMeans,
   .commonDenominatorRequiredForNormalizedMeanComparison,
   .equalQuadraticMeansNotFullDistributionsOrOperationalStateEquality,
   .probabilityMixtureAndEventActualizationOpen,
   .finiteProbabilityNormalizationAndSharedResponsesSupplied,
   .conditionalFiniteRecordParityTVLowerBound,
   .hiddenRecordEquivalenceNeedsPreparationNoncontextuality,
   .jointlyObservableRecordEquivalenceIsStrongerOperationalCondition,
   .suppliedQuadraticProbeOnly, .noHilbertScalarOrSerialMultiplicationPremise,
   .noQuantumMeasurementOrFullQMClaim, .noPrimitiveInevitabilityOrStatusUpgrade]

end

end IDT.QMClosure.NativePreparationParityWitness
