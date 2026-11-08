import Proofs.QMClosure.InternalReferenceEntropyBridge
import Proofs.QMClosure.ReferenceEntropyFactorizationControls
import Proofs.QMClosure.PortFrameAlignment
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Finite internal-reference omission controls

The first control omits raw fixed diagonals while retaining one common channel.
The second fixes raw diagonals but assigns a channel separately to each raw pair.
Both retain an internal full-support reference, finite reference-relative KL,
full product covariance and reference preservation. The second even retains
sample-swap symmetry for every selected channel. Their infinite pairwise KL
values concern the stronger support/finite-KL conclusion. They assert no
separate minimality result for reference-entropy factorization alone.
-/

namespace IDT.QMClosure.InternalReferenceProcessControls

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

private theorem product_singleton {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) [SFinite ν] (a : A) (b : B) :
    μ.prod ν {(a, b)} = μ {a} * ν {b} := by
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]

private theorem absolutelyContinuous_of_positive_singletons {A : Type*}
    [MeasurableSpace A] (μ α : Measure A) (positive : ∀ a, 0 < α {a}) : μ ≪ α := by
  intro s hs
  have he : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact (not_le_of_gt (positive a))
      ((measure_mono (Set.singleton_subset_iff.mpr ha)).trans_eq hs)
  simp [he]

private theorem deterministic_comp_singleton {A : Type*} [Finite A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (f g : A → A) (left : Function.LeftInverse g f) (right : Function.RightInverse g f)
    (μ : Measure A) (q : A) :
    (Kernel.deterministic f (measurable_of_finite _) ∘ₘ μ) {q} = μ {g q} := by
  rw [Measure.deterministic_comp_eq_map, Measure.map_apply (measurable_of_finite _)
    (measurableSet_singleton _)]
  congr 1
  ext a
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    simpa only [left a] using congrArg g h
  · rintro rfl
    exact right q

namespace WithoutFixedDiagonal

abbrev Port := Bool × Bool
abbrev operation := PortFrameAlignment.FirstOutputControl.gate

def bitLaw (a : Bool) : Measure Bool :=
  if a then ReferenceEntropyFactorizationControls.fair else Measure.dirac false

instance bitLaw_probability (a : Bool) : IsProbabilityMeasure (bitLaw a) := by
  cases a <;> simp only [bitLaw, Bool.false_eq_true, if_false, if_true] <;> infer_instance

@[simp] theorem bitLaw_singleton (a b : Bool) :
    bitLaw a {b} = if a then 1 / 2 else if b then 0 else 1 := by
  cases a <;> cases b <;> simp [bitLaw]

def preparation (x : Port) : Measure Port := (bitLaw x.1).prod (bitLaw x.2)
def reference : Measure Port := preparation (true, true)

instance preparation_probability (x : Port) : IsProbabilityMeasure (preparation x) := by
  unfold preparation
  infer_instance

instance reference_probability : IsProbabilityMeasure reference := by
  unfold reference
  infer_instance

@[simp] theorem reference_singleton (a : Port) : reference {a} = 1 / 4 := by
  rcases a with ⟨a, b⟩
  rw [reference, preparation, product_singleton]
  simp only [bitLaw_singleton, if_true]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

def channel : Kernel (Port × Port) (Port × Port) :=
  Kernel.deterministic operation (measurable_of_finite _)

instance channel_markov : IsMarkovKernel channel := by
  unfold channel
  infer_instance

theorem operation_square (p : Port × Port) : operation (operation p) = p.swap :=
  PortFrameAlignment.FirstOutputControl.gate_square p

theorem operation_four (p : Port × Port) :
    operation (operation (operation (operation p))) = p := by
  rw [operation_square, operation_square]
  rfl

private theorem channel_singleton (μ : Measure (Port × Port)) (q : Port × Port) :
    (channel ∘ₘ μ) {q} = μ {operation (operation (operation q))} := by
  exact deterministic_comp_singleton operation (fun q => operation (operation (operation q)))
    operation_four operation_four μ q

theorem covariance (p : Port × Port) :
    channel ∘ₘ ((preparation p.1).prod (preparation p.2)) =
      (preparation (operation p).1).prod (preparation (operation p).2) := by
  apply Measure.ext_of_singleton
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rw [channel_singleton]
  rcases p with ⟨⟨w, x⟩, ⟨y, z⟩⟩
  simp only [PortFrameAlignment.FirstOutputControl.gate, preparation, product_singleton]
  ring

theorem reference_preserving :
    channel ∘ₘ reference.prod reference = reference.prod reference := by
  apply Measure.ext_of_singleton
  intro q
  rw [channel_singleton, product_singleton, product_singleton]
  simp

theorem channel_swap_symmetric (q : Port × Port) :
    channel q.swap = (channel q).map Prod.swap := by
  simp [channel, Kernel.deterministic_apply, Measure.map_dirac,
    PortFrameAlignment.FirstOutputControl.gate]

theorem finite_referenceKL (x : Port) : klDiv (preparation x) reference ≠ ∞ := by
  apply klDiv_ne_top
  · exact absolutelyContinuous_of_positive_singletons _ _ (fun a => by simp)
  · exact Integrable.of_finite

/-- The complete reference-factorization contract is retained in this control. -/
def contract : ReferenceEntropyFactorization.Contract Port Port where
  preparation := preparation
  probability := preparation_probability
  reference := reference
  referenceProbability := reference_probability
  finiteReferenceEntropy := finite_referenceKL
  operation := operation
  square := operation_square
  channel := channel
  markov := channel_markov
  referencePreserving := reference_preserving
  firstMarginal p := by rw [covariance, Measure.fst_prod]
  secondMarginal p := by rw [covariance, Measure.snd_prod]

theorem reference_internal : reference = preparation (true, true) := rfl

theorem diagonal_not_fixed :
    operation ((false, true), (false, true)) ≠ ((false, true), (false, true)) := by
  decide

theorem diagonal_law_moves :
    preparation (operation ((false, true), (false, true))).1 ≠
      preparation (false, true) := by
  intro h
  have hh := congrArg (fun μ : Measure Port => μ {(false, true)}) h
  norm_num [PortFrameAlignment.FirstOutputControl.gate, preparation, product_singleton,
    ENNReal.inv_eq_zero] at hh
  exact (ENNReal.inv_ne_zero.mpr (by norm_num : (2 : ℝ≥0∞) ≠ ∞)) hh.symm

theorem reference_not_absolutelyContinuous :
    ¬ reference ≪ preparation (false, false) := by
  intro h
  have hh := h (show preparation (false, false) {(false, true)} = 0 by
    norm_num [preparation, product_singleton])
  norm_num at hh

theorem infinite_pairwiseKL :
    klDiv (preparation (true, true)) (preparation (false, false)) = ∞ :=
  klDiv_of_not_ac reference_not_absolutelyContinuous

end WithoutFixedDiagonal

namespace WithoutCommonChannel

abbrev Sample := Fin 4
abbrev Label := Fin 5

def reference : Measure Sample := (PMF.uniformOfFintype Sample).toMeasure

instance reference_probability : IsProbabilityMeasure reference := by
  unfold reference
  infer_instance

@[simp] theorem reference_singleton (a : Sample) : reference {a} = 1 / 4 := by
  simp [reference, PMF.uniformOfFintype_apply]

/-- Label zero is the reference, and labels one through four are the four Dirac laws. -/
def preparation : Label → Measure Sample
  | 0 => reference
  | 1 => Measure.dirac 0
  | 2 => Measure.dirac 1
  | 3 => Measure.dirac 2
  | _ => Measure.dirac 3

instance preparation_probability (x : Label) : IsProbabilityMeasure (preparation x) := by
  fin_cases x <;> simp only [preparation] <;> infer_instance

/-- Five disjoint four-cycles, with the five diagonal pairs fixed. -/
def operation : Label × Label → Label × Label
  | (0, 1) => (0, 2)
  | (0, 2) => (1, 0)
  | (1, 0) => (2, 0)
  | (2, 0) => (0, 1)
  | (0, 3) => (0, 4)
  | (0, 4) => (3, 0)
  | (3, 0) => (4, 0)
  | (4, 0) => (0, 3)
  | (1, 2) => (3, 4)
  | (3, 4) => (2, 1)
  | (2, 1) => (4, 3)
  | (4, 3) => (1, 2)
  | (1, 3) => (2, 4)
  | (2, 4) => (3, 1)
  | (3, 1) => (4, 2)
  | (4, 2) => (1, 3)
  | (1, 4) => (2, 3)
  | (2, 3) => (4, 1)
  | (4, 1) => (3, 2)
  | (3, 2) => (1, 4)
  | p => p

theorem operation_square : ∀ p, operation (operation p) = p.swap := by decide
theorem operation_diagonal : ∀ x, operation (x, x) = (x, x) := by decide

/-- The selected swap flag and common translation in the two sample coordinates. -/
def parameters : Label × Label → Bool × Sample
  | (0, 1) => (false, 1)
  | (0, 2) => (true, 3)
  | (1, 0) => (false, 1)
  | (2, 0) => (true, 3)
  | (0, 3) => (false, 1)
  | (0, 4) => (true, 3)
  | (3, 0) => (false, 1)
  | (4, 0) => (true, 3)
  | (1, 2) => (false, 2)
  | (3, 4) => (true, 2)
  | (2, 1) => (false, 2)
  | (4, 3) => (true, 2)
  | (1, 3) => (false, 1)
  | (2, 4) => (false, 1)
  | (3, 1) => (false, 1)
  | (4, 2) => (false, 1)
  | (1, 4) => (true, 2)
  | (2, 3) => (false, 2)
  | (4, 1) => (true, 2)
  | (3, 2) => (false, 2)
  | _ => (false, 0)

def transport (p : Label × Label) (q : Sample × Sample) : Sample × Sample :=
  if (parameters p).1 then (q.2 + (parameters p).2, q.1 + (parameters p).2)
  else (q.1 + (parameters p).2, q.2 + (parameters p).2)

def inverseTransport (p : Label × Label) (q : Sample × Sample) : Sample × Sample :=
  if (parameters p).1 then (q.2 - (parameters p).2, q.1 - (parameters p).2)
  else (q.1 - (parameters p).2, q.2 - (parameters p).2)

theorem inverseTransport_transport (p : Label × Label) :
    Function.LeftInverse (inverseTransport p) (transport p) := by
  intro q
  cases h : (parameters p).1 <;> simp [transport, inverseTransport, h]

theorem transport_inverseTransport (p : Label × Label) :
    Function.RightInverse (inverseTransport p) (transport p) := by
  intro q
  cases h : (parameters p).1 <;> simp [transport, inverseTransport, h]

def permutation (p : Label × Label) : (Sample × Sample) ≃ (Sample × Sample) where
  toFun := transport p
  invFun := inverseTransport p
  left_inv := inverseTransport_transport p
  right_inv := transport_inverseTransport p

theorem transport_swap (p : Label × Label) (q : Sample × Sample) :
    transport p q.swap = (transport p q).swap := by
  cases h : (parameters p).1 <;> simp [transport, h]

def channel (p : Label × Label) : Kernel (Sample × Sample) (Sample × Sample) :=
  Kernel.deterministic (transport p) (measurable_of_finite _)

instance channel_markov (p : Label × Label) : IsMarkovKernel (channel p) := by
  unfold channel
  infer_instance

private theorem channel_singleton (p : Label × Label) (μ : Measure (Sample × Sample))
    (q : Sample × Sample) : (channel p ∘ₘ μ) {q} = μ {inverseTransport p q} :=
  deterministic_comp_singleton (transport p) (inverseTransport p)
    (inverseTransport_transport p) (transport_inverseTransport p) μ q

theorem reference_preserving (p : Label × Label) :
    channel p ∘ₘ reference.prod reference = reference.prod reference := by
  apply Measure.ext_of_singleton
  intro q
  rw [channel_singleton, product_singleton, product_singleton]
  simp

theorem channel_swap_symmetric (p : Label × Label) (q : Sample × Sample) :
    channel p q.swap = (channel p q).map Prod.swap := by
  simp [channel, Kernel.deterministic_apply, Measure.map_dirac, transport_swap]

/-- Integer atom weights with common denominator four. -/
def multiplicity : Label → Sample → ℕ
  | 0, _ => 1
  | 1, a => if a = 0 then 4 else 0
  | 2, a => if a = 1 then 4 else 0
  | 3, a => if a = 2 then 4 else 0
  | _, a => if a = 3 then 4 else 0

private theorem preparation_singleton (x : Label) (a : Sample) :
    preparation x {a} = (multiplicity x a : ℝ≥0∞) / 4 := by
  fin_cases x <;> fin_cases a <;>
    norm_num [preparation, multiplicity, Pi.single_apply, Fin.ext_iff, ENNReal.div_self]

private theorem multiplicity_covariance : ∀ (p : Label × Label) (q : Sample × Sample),
    multiplicity p.1 (inverseTransport p q).1 *
        multiplicity p.2 (inverseTransport p q).2 =
      multiplicity (operation p).1 q.1 * multiplicity (operation p).2 q.2 := by
  decide

theorem covariance (p : Label × Label) :
    channel p ∘ₘ ((preparation p.1).prod (preparation p.2)) =
      (preparation (operation p).1).prod (preparation (operation p).2) := by
  apply Measure.ext_of_singleton
  intro q
  rw [channel_singleton, product_singleton, product_singleton]
  simp only [preparation_singleton, div_eq_mul_inv]
  have hm := congrArg (fun n : ℕ => (n : ℝ≥0∞)) (multiplicity_covariance p q)
  simp only [Nat.cast_mul] at hm
  calc
    _ = ((multiplicity p.1 (inverseTransport p q).1 : ℝ≥0∞) *
        multiplicity p.2 (inverseTransport p q).2) * (4⁻¹ * 4⁻¹) := by ring
    _ = ((multiplicity (operation p).1 q.1 : ℝ≥0∞) *
        multiplicity (operation p).2 q.2) * (4⁻¹ * 4⁻¹) := by rw [hm]
    _ = _ := by ring

theorem reference_internal : reference = preparation 0 := rfl

theorem finite_referenceKL (x : Label) : klDiv (preparation x) reference ≠ ∞ := by
  apply klDiv_ne_top
  · exact absolutelyContinuous_of_positive_singletons _ _ (fun a => by simp)
  · exact Integrable.of_finite

theorem reference_not_absolutelyContinuous : ¬ reference ≪ preparation 1 := by
  intro h
  have hh := h (show preparation 1 {(1 : Sample)} = 0 by simp [preparation])
  norm_num at hh

theorem reference_reverseKL_top : klDiv reference (preparation 1) = ∞ :=
  klDiv_of_not_ac reference_not_absolutelyContinuous

theorem infinite_pairwiseKL : klDiv (preparation 1) (preparation 2) = ∞ := by
  apply klDiv_of_not_ac
  intro h
  have hh := h (show preparation 2 {(0 : Sample)} = 0 by simp [preparation])
  simp [preparation] at hh

/-- No single kernel can supply all the displayed product covariances. -/
theorem no_common_channel :
    ¬ ∃ κ : Kernel (Sample × Sample) (Sample × Sample),
      ∀ p, κ ∘ₘ ((preparation p.1).prod (preparation p.2)) =
        (preparation (operation p).1).prod (preparation (operation p).2) := by
  rintro ⟨κ, hκ⟩
  apply reference_not_absolutelyContinuous
  have hforward : preparation 1 ≪ preparation 0 := by
    change preparation 1 ≪ reference
    exact absolutelyContinuous_of_positive_singletons _ _ (fun a => by simp)
  exact InternalReferenceSupportBridge.reverse_absolutelyContinuous preparation
    preparation_probability operation operation_square operation_diagonal κ hκ hforward

end WithoutCommonChannel

namespace GaussianWitness

open NativeGaussianStatisticalProcess

/-- An explicit consistency witness for the pointed statistical interface. -/
def pointedModel : InternalReferenceEntropyBridge.PointedContract ℂ Sample where
  preparation := model.preparation
  probability := model.probability
  chosenReference := model.chosenZero
  finiteReferenceEntropy x := model.finiteEntropy x model.chosenZero
  operation := model.operation
  square := model.square
  transparent := model.transparent
  channel := model.channel
  markov := model.markov
  covariance := model.covariance

theorem preparations_distinct :
    pointedModel.preparation 0 ≠ pointedModel.preparation 1 := by
  intro h
  have hh : (0 : ℂ) = 1 := preparation_injective h
  norm_num at hh

end GaussianWitness
end
end IDT.QMClosure.InternalReferenceProcessControls
