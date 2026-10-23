import Mathlib.Tactic

namespace IDT.QMClosure.ContinuationSufficiency

/-! Total deterministic operations, with every finite word admitted. The state,
alphabet, and readout are supplied; none is selected by this mathematics. -/

def run {A S : Type*} (step : A → S → S) : S → List A → S
  | s, [] => s
  | s, a :: word => run step (step a s) word

def BehaviorEquivalent {A S O : Type*} (step : A → S → S) (readout : S → O)
    (x y : S) : Prop :=
  ∀ word, readout (run step x word) = readout (run step y word)

def OutputCompatible {S O : Type*} (readout : S → O) (R : S → S → Prop) : Prop :=
  ∀ x y, R x y → readout x = readout y

def SuccessorClosed {A S : Type*} (step : A → S → S) (R : S → S → Prop) : Prop :=
  ∀ a x y, R x y → R (step a x) (step a y)

def PredictivelySufficient {A S O Q : Type*} (step : A → S → S)
    (readout : S → O) (q : S → Q) : Prop :=
  ∀ x y, q x = q y → BehaviorEquivalent step readout x y

def UpdateSufficient {A S Q : Type*} (step : A → S → S) (q : S → Q) : Prop :=
  SuccessorClosed step (fun x y => q x = q y)

/-- No finiteness, reflexivity, symmetry, or transitivity of R is needed. -/
theorem relation_sound_for_all_words {A S O : Type*}
    (step : A → S → S) (readout : S → O) (R : S → S → Prop)
    (hout : OutputCompatible readout R) (hstep : SuccessorClosed step R) :
    ∀ x y, R x y → BehaviorEquivalent step readout x y := by
  intro x y hxy word
  induction word generalizing x y with
  | nil => exact hout x y hxy
  | cons a word ih => exact ih _ _ (hstep a x y hxy)

theorem behavior_output_compatible {A S O : Type*}
    (step : A → S → S) (readout : S → O) :
    OutputCompatible readout (BehaviorEquivalent step readout) := by
  intro x y h
  exact h []

theorem behavior_successor_closed {A S O : Type*}
    (step : A → S → S) (readout : S → O) :
    SuccessorClosed step (BehaviorEquivalent step readout) := by
  intro a x y h word
  exact h (a :: word)

/-- Largest means relation inclusion, not largest state-space cardinality. -/
theorem behavior_is_greatest_compatible_closed_relation {A S O : Type*}
    (step : A → S → S) (readout : S → O) (R : S → S → Prop) :
    OutputCompatible readout R ∧ SuccessorClosed step R →
      ∀ x y, R x y → BehaviorEquivalent step readout x y := by
  rintro ⟨hout, hstep⟩
  exact relation_sound_for_all_words step readout R hout hstep

theorem behavior_equivalence {A S O : Type*}
    (step : A → S → S) (readout : S → O) :
    Equivalence (BehaviorEquivalent step readout) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x word; rfl
  · intro x y h word; exact (h word).symm
  · intro x y z hxy hyz word; exact (hxy word).trans (hyz word)

theorem output_and_update_imply_predictive {A S O Q : Type*}
    (step : A → S → S) (readout : S → O) (q : S → Q)
    (hout : OutputCompatible readout (fun x y => q x = q y))
    (hupdate : UpdateSufficient step q) : PredictivelySufficient step readout q :=
  relation_sound_for_all_words step readout _ hout hupdate

/-- A supplied bijective coordinate change preserves behavior; no linearity. -/
theorem run_coordinate_transport {A S T : Type*}
    (step : A → S → S) (e : S ≃ T) (x : S) (word : List A) :
    run (fun a t => e (step a (e.symm t))) (e x) word = e (run step x word) := by
  induction word generalizing x with
  | nil => rfl
  | cons a word ih => simpa only [run, e.symm_apply_apply] using ih (step a x)

theorem behavior_coordinate_transport_iff {A S T O : Type*}
    (step : A → S → S) (readout : S → O) (e : S ≃ T) (x y : S) :
    BehaviorEquivalent (fun a t => e (step a (e.symm t)))
      (fun t => readout (e.symm t)) (e x) (e y) ↔
      BehaviorEquivalent step readout x y := by
  simp only [BehaviorEquivalent, run_coordinate_transport, e.symm_apply_apply]

/-! Predictive sufficiency need not imply update sufficiency.
States a,b,c,d have outputs 0,0,1,1 and q-values 0,0,1,2. -/

def splitStep (_ : Unit) (s : Fin 4) : Fin 4 :=
  if s.val = 0 ∨ s.val = 2 then 2 else 3

def splitOutput (s : Fin 4) : Nat := if s.val < 2 then 0 else 1
def splitQ (s : Fin 4) : Nat := if s.val < 2 then 0 else s.val - 1

theorem split_q_predictively_sufficient :
    PredictivelySufficient splitStep splitOutput splitQ := by
  have hout : OutputCompatible splitOutput (fun x y => splitOutput x = splitOutput y) :=
    fun _ _ h => h
  have hstep : SuccessorClosed splitStep (fun x y => splitOutput x = splitOutput y) := by
    intro a x y _
    cases a
    fin_cases x <;> fin_cases y <;> decide
  intro x y h
  apply relation_sound_for_all_words splitStep splitOutput _ hout hstep x y
  fin_cases x <;> fin_cases y <;> simp_all [splitQ, splitOutput]

theorem split_q_not_update_sufficient : ¬ UpdateSufficient splitStep splitQ := by
  intro h
  have hh := h () 0 1 (by decide)
  norm_num [splitStep, splitQ] at hh

/-! A closed phase-flip fixture; the rational readout formula is supplied. -/

def phaseCoordinates (s : Fin 3) : ℚ × ℚ :=
  if s.val = 0 then (2, 0) else if s.val = 1 then (1, 1) else (1, -1)

def phaseStep (_ : Unit) (s : Fin 3) : Fin 3 :=
  if s.val = 0 then 0 else if s.val = 1 then 2 else 1

def phaseQ (s : Fin 3) : ℚ := (phaseCoordinates s).1 + (phaseCoordinates s).2
def phaseReadout (s : Fin 3) : ℚ := phaseQ s ^ 2 / (phaseQ s ^ 2 + 1)

theorem phase_step_involutive : Function.Involutive (phaseStep ()) := by
  intro s
  fin_cases s <;> decide

theorem phase_step_flips_second_coordinate (s : Fin 3) :
    phaseCoordinates (phaseStep () s) =
      ((phaseCoordinates s).1, -(phaseCoordinates s).2) := by
  fin_cases s <;> norm_num [phaseCoordinates, phaseStep]

theorem phase_equal_now_distinct_after :
    phaseQ 0 = 2 ∧ phaseQ 1 = 2 ∧
    phaseReadout 0 = 4 / 5 ∧ phaseReadout 1 = 4 / 5 ∧
    phaseReadout (phaseStep () 0) = 4 / 5 ∧
    phaseReadout (phaseStep () 1) = 0 := by
  norm_num [phaseQ, phaseCoordinates, phaseReadout, phaseStep]

theorem phase_q_not_predictively_sufficient :
    ¬ PredictivelySufficient phaseStep phaseReadout phaseQ := by
  intro h
  have hh := h 0 1 (by norm_num [phaseQ, phaseCoordinates]) [()]
  norm_num [run, phaseReadout, phaseQ, phaseCoordinates, phaseStep] at hh

/-! A reversible control: agreement now and after one step misses a two-step
witness. This is one concrete cycle, not an arbitrary-delay Lean theorem. -/

def cycleStep (_ : Unit) (s : Fin 4) : Fin 4 :=
  if s.val = 0 then 1 else if s.val = 1 then 2 else if s.val = 2 then 3 else 0

def cycleBack (s : Fin 4) : Fin 4 :=
  if s.val = 0 then 3 else if s.val = 1 then 0 else if s.val = 2 then 1 else 2

def cycleOutput (s : Fin 4) : Nat := if s.val = 3 then 1 else 0

theorem cycle_step_bijective : Function.Bijective (cycleStep ()) := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨cycleBack, ?_, ?_⟩
  · intro s; fin_cases s <;> decide
  · intro s; fin_cases s <;> decide

theorem delayed_two_step_witness :
    cycleOutput (run cycleStep 0 []) = cycleOutput (run cycleStep 1 []) ∧
    cycleOutput (run cycleStep 0 [()]) = cycleOutput (run cycleStep 1 [()]) ∧
    cycleOutput (run cycleStep 0 [(), ()]) ≠
      cycleOutput (run cycleStep 1 [(), ()]) := by decide

/-! Entries name outstanding bridges. Their count is only a list-shape lemma,
not a theorem that physical obligations have or have not been discharged. -/

inductive OpenBridge where
  | physicalStateAndModelAdequacy
  | actualOperationAlphabetAndFullWordLegality
  | exactReadoutAndMeasurementBridge
  | stochasticInstrumentsAndAdaptiveProtocols
  | acceptedPrimitiveBindingAndQuantumSelection
  | pythonCertificateKernelReification
  deriving DecidableEq, Repr

def openBridges : List OpenBridge :=
  [.physicalStateAndModelAdequacy,
   .actualOperationAlphabetAndFullWordLegality,
   .exactReadoutAndMeasurementBridge,
   .stochasticInstrumentsAndAdaptiveProtocols,
   .acceptedPrimitiveBindingAndQuantumSelection,
   .pythonCertificateKernelReification]

theorem open_bridge_list_length : openBridges.length = 6 := rfl

end IDT.QMClosure.ContinuationSufficiency
