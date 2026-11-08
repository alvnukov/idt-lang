import Proofs.QMClosure.UniversalDetectorConservationWall
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic

/-!
Two finite omission controls distinguish universal detector conservation from
conservation for selected complementary events, and distinguish common full-law
transport from raw-label routing. The positive Bool control has finite pairwise KL. The Dirac control has
infinite KL between distinct preparations.
-/
namespace IDT.QMClosure.DetectorConservationOmissionControls

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
open InvariantEffectReadoutBridge DetectorEffectOperations

abbrev Label := Fin 5

/-- Five four-cycles on the off-diagonal pairs, with fixed diagonals. -/
def operation : Label × Label → Label × Label
  | (0, 1) => (0, 2)
  | (0, 2) => (1, 0)
  | (1, 0) => (2, 0)
  | (2, 0) => (0, 1)
  | (0, 3) => (0, 4)
  | (0, 4) => (3, 0)
  | (3, 0) => (4, 0)
  | (4, 0) => (0, 3)
  | (1, 2) => (1, 3)
  | (1, 3) => (2, 1)
  | (2, 1) => (3, 1)
  | (3, 1) => (1, 2)
  | (1, 4) => (2, 3)
  | (2, 3) => (4, 1)
  | (4, 1) => (3, 2)
  | (3, 2) => (1, 4)
  | (2, 4) => (3, 4)
  | (3, 4) => (4, 2)
  | (4, 2) => (4, 3)
  | (4, 3) => (2, 4)
  | p => p

theorem operation_square : ∀ p, operation (operation p) = p.swap := by decide

theorem operation_diagonal : ∀ x, operation (x, x) = (x, x) := by decide

/-- The singleton class and its four-element complement. -/
def labelClass (x : Label) : Bool := decide (x = 0)

def classPair (p : Label × Label) : Bool × Bool := (labelClass p.1, labelClass p.2)

theorem operation_class_pair : ∀ p,
    classPair (operation p) = classPair p ∨
      classPair (operation p) = (classPair p).swap := by decide

/-- Every scalar readout depending only on this partition has conserved products. -/
theorem class_response_product (r : Bool → ℝ) (p : Label × Label) :
    r (labelClass (operation p).1) * r (labelClass (operation p).2) =
      r (labelClass p.1) * r (labelClass p.2) := by
  rcases operation_class_pair p with h | h
  · exact congrArg (fun q : Bool × Bool => r q.1 * r q.2) h
  · have hh := congrArg (fun q : Bool × Bool => r q.1 * r q.2) h
    simpa only [classPair, Prod.swap, mul_comm] using hh

/-- A genuine binary kernel with distinct strictly positive rows. -/
def boolEffect : Effect Bool where
  value := fun b => if b then 1 / 3 else 2 / 3
  measurable := measurable_of_finite _
  nonnegative := fun b => by cases b <;> norm_num
  atMostOne := fun b => by cases b <;> norm_num

def positivePreparation (x : Label) : Measure Bool := boolEffect.binaryKernel (labelClass x)

instance positivePreparation_probability (x : Label) :
    IsProbabilityMeasure (positivePreparation x) := inferInstanceAs
      (IsProbabilityMeasure (boolEffect.binaryKernel (labelClass x)))

theorem positivePreparation_singleton_positive (x : Label) (b : Bool) :
    0 < positivePreparation x {b} := by
  cases hb : labelClass x <;> cases b <;>
    simp [positivePreparation, hb, Effect.binaryKernel, boolEffect] <;> norm_num


/-- Strictly positive rows on the finite outcome space are mutually absolutely continuous. -/
theorem positivePreparation_absolutelyContinuous (x y : Label) :
    positivePreparation x ≪ positivePreparation y := by
  intro s hs
  have hempty : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    have hle : positivePreparation y {b} ≤ positivePreparation y s :=
      measure_mono (Set.singleton_subset_iff.mpr hb)
    exact (not_le_of_gt (positivePreparation_singleton_positive y b)) (hle.trans_eq hs)
  simp only [hempty, measure_empty]

/-- Every real function on Bool is bounded and integrable under a probability law. -/
private theorem bool_integrable (μ : Measure Bool) [IsProbabilityMeasure μ]
    (f : Bool → ℝ) : Integrable f μ := by
  apply Integrable.of_bound (measurable_of_finite f).aestronglyMeasurable
    (max ‖f false‖ ‖f true‖)
  exact Filter.Eventually.of_forall fun b => by
    cases b
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- The common-transport omission control retains finite pairwise latent KL. -/
theorem positivePreparation_kl_ne_top (x y : Label) :
    klDiv (positivePreparation x) (positivePreparation y) ≠ ∞ :=
  klDiv_ne_top (positivePreparation_absolutelyContinuous x y)
    (bool_integrable _ _)

theorem positivePreparation_distinct : positivePreparation 0 ≠ positivePreparation 1 := by
  intro h
  have hh := congrArg (fun μ : Measure Bool => μ {true}) h
  norm_num [positivePreparation, labelClass, Effect.binaryKernel, boolEffect] at hh

/-- Even every detector is conserved when the transport premise is omitted. -/
theorem positivePreparation_all_products (g : Effect Bool) (p : Label × Label) :
    g.acceptance (positivePreparation (operation p).1) *
      g.acceptance (positivePreparation (operation p).2) =
      g.acceptance (positivePreparation p.1) * g.acceptance (positivePreparation p.2) :=
  class_response_product (fun b => g.acceptance (boolEffect.binaryKernel b)) p

theorem positivePreparation_equal_input_laws :
    (positivePreparation 0).prod (positivePreparation 1) =
      (positivePreparation 0).prod (positivePreparation 2) := rfl

/-- Raw routing of equal input laws requires different ordered output laws. -/
theorem positivePreparation_output_laws_distinct :
    (positivePreparation (operation (0, 1)).1).prod
        (positivePreparation (operation (0, 1)).2) ≠
      (positivePreparation (operation (0, 2)).1).prod
        (positivePreparation (operation (0, 2)).2) := by
  intro h
  have hm := congrArg (Measure.map (Prod.fst : Bool × Bool → Bool)) h
  have he : positivePreparation 0 = positivePreparation 1 := by
    simpa only [operation, Measure.map_fst_prod, measure_univ, one_smul] using hm
  exact positivePreparation_distinct he

/-- No single function of full input laws can implement that raw-label routing. -/
theorem positivePreparation_no_common_transport :
    ¬ ∃ Φ : Measure (Bool × Bool) → Measure (Bool × Bool), ∀ p,
      Φ ((positivePreparation p.1).prod (positivePreparation p.2)) =
        (positivePreparation (operation p).1).prod
          (positivePreparation (operation p).2) := by
  rintro ⟨Φ, hΦ⟩
  apply positivePreparation_output_laws_distinct
  rw [← hΦ (0, 1), ← hΦ (0, 2), positivePreparation_equal_input_laws]

/-- Actual point preparations admit the deterministic common channel. -/
def diracPreparation (x : Label) : Measure Label := Measure.dirac x

def deterministicChannel : Kernel (Label × Label) (Label × Label) :=
  Kernel.deterministic operation (measurable_of_finite _)

instance deterministicChannel_markov : IsMarkovKernel deterministicChannel := by
  unfold deterministicChannel
  infer_instance

theorem diracPreparation_covariance (p : Label × Label) :
    deterministicChannel ∘ₘ ((diracPreparation p.1).prod (diracPreparation p.2)) =
      (diracPreparation (operation p).1).prod (diracPreparation (operation p).2) := by
  simp [diracPreparation, deterministicChannel, Measure.dirac_prod_dirac,
    Measure.deterministic_comp_eq_map, Measure.map_dirac]

/-- A selected detector has two different acceptance levels. -/
def selectedEffect : Effect Label where
  value := fun x => if labelClass x then 1 / 3 else 2 / 3
  measurable := measurable_of_finite _
  nonnegative := fun x => by cases labelClass x <;> norm_num
  atMostOne := fun x => by cases labelClass x <;> norm_num

@[simp] theorem dirac_acceptance (g : Effect Label) (x : Label) :
    g.acceptance (diracPreparation x) = g.value x := by
  simp [Effect.acceptance, diracPreparation]

theorem selectedEffect_nonconstant :
    selectedEffect.acceptance (diracPreparation 0) ≠
      selectedEffect.acceptance (diracPreparation 1) := by
  norm_num [selectedEffect, labelClass]

theorem selectedEffect_product (p : Label × Label) :
    selectedEffect.acceptance (diracPreparation (operation p).1) *
      selectedEffect.acceptance (diracPreparation (operation p).2) =
      selectedEffect.acceptance (diracPreparation p.1) *
        selectedEffect.acceptance (diracPreparation p.2) := by
  simp only [dirac_acceptance]
  exact class_response_product (fun b => if b then 1 / 3 else 2 / 3) p

theorem selectedComplement_product (p : Label × Label) :
    (complement selectedEffect).acceptance (diracPreparation (operation p).1) *
      (complement selectedEffect).acceptance (diracPreparation (operation p).2) =
      (complement selectedEffect).acceptance (diracPreparation p.1) *
        (complement selectedEffect).acceptance (diracPreparation p.2) := by
  simp only [dirac_acceptance]
  exact class_response_product (fun b => 1 - (if b then 1 / 3 else 2 / 3)) p

theorem selectedSureAverage_product (p : Label × Label) :
    (average sure selectedEffect).acceptance (diracPreparation (operation p).1) *
      (average sure selectedEffect).acceptance (diracPreparation (operation p).2) =
      (average sure selectedEffect).acceptance (diracPreparation p.1) *
        (average sure selectedEffect).acceptance (diracPreparation p.2) := by
  simp only [dirac_acceptance]
  exact class_response_product (fun b => (1 + (if b then 1 / 3 else 2 / 3)) / 2) p

/-- The Dirac control violates finite KL for every two distinct labels. -/
theorem diracPreparation_kl_top {x y : Label} (hxy : x ≠ y) :
    klDiv (diracPreparation x) (diracPreparation y) = ∞ := by
  apply klDiv_of_not_ac
  intro hac
  have hy : diracPreparation y {x} = 0 := by
    simp [diracPreparation, hxy]
  have hx := hac hy
  simp [diracPreparation] at hx

end
end IDT.QMClosure.DetectorConservationOmissionControls
