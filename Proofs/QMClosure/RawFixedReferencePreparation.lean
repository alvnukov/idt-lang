import Proofs.QMClosure.SourceLocalOriginalSemantics
import Proofs.QMClosure.AllocatedPreparation

/-!
# A raw term retracting onto diagonal-fixed points

The core uses only mediality and the bookend law. The native compiler retains
all three output wires and charges three separately supplied occurrences of a
known source. Its vacuum variant has three vacuum input ports and no source
tags. Neither syntax establishes physical joint availability or copying of an
unknown preparation. Retraction need not preserve a nonzero source: the final
control exhibits collapse to zero. No probability law or QM closure is derived.
-/

namespace IDT.QMClosure.RawFixedReferencePreparation

noncomputable section

open MedialSwapRoot WeightFreeRawProbability NativeVacuumProbabilityFamily
open SourceLocalOriginalSemantics

variable {V : Type*}

/-- A term of the original first channel; no normalized gate is used. -/
def retract (f : V → V → V) (x : V) : V := f x (f x (f x x))

section Core

variable {f : V → V → V} (h : DiagonalNormalization.Laws f)

include h in
/-- An alternative raw term for the same retracted value. -/
theorem retract_eq_right (x : V) :
    retract f x = f (DiagonalNormalization.diagonal f x)
      (f (DiagonalNormalization.diagonal f x) x) := by
  let y := DiagonalNormalization.diagonal f x
  let a := f x y
  let b := f y x
  have hy : f y y = x := DiagonalNormalization.diagonal_involutive h x
  have haa : f a a = b := by
    change DiagonalNormalization.diagonal f (f x y) = f y x
    rw [DiagonalNormalization.diagonal_map h,
      DiagonalNormalization.diagonal_involutive h]
  have hab : f a b = y := h.bookend x y
  have hba : f b a = x := h.bookend y x
  change f x a = f y b
  calc
    f x a = f (f y y) (f x y) := by rw [hy]
    _ = f (f y x) (f y y) := h.medial y y x y
    _ = f b x := by rw [hy]
    _ = f (f a a) (f b a) := by rw [haa, hba]
    _ = f (f a b) (f a a) := h.medial a a b a
    _ = f y b := by rw [hab, haa]

include h in
/-- Every raw input is sent to a fixed point of the raw diagonal. -/
theorem diagonal_retract_fixed (x : V) :
    DiagonalNormalization.diagonal f (retract f x) = retract f x := by
  change DiagonalNormalization.diagonal f
    (f x (f x (DiagonalNormalization.diagonal f x))) = retract f x
  rw [DiagonalNormalization.diagonal_map h,
    DiagonalNormalization.diagonal_map h,
    DiagonalNormalization.diagonal_involutive h]
  exact (retract_eq_right h x).symm

include h in
/-- The third gate's selected raw term is exactly the retraction. -/
theorem retract_eq_middle (x : V) :
    f (f x (DiagonalNormalization.diagonal f x))
      (DiagonalNormalization.diagonal f x) = retract f x := by
  have hm := h.medial x (DiagonalNormalization.diagonal f x) x x
  change f (f x (DiagonalNormalization.diagonal f x))
      (DiagonalNormalization.diagonal f x) =
    f (DiagonalNormalization.diagonal f x)
      (f (DiagonalNormalization.diagonal f x) x) at hm
  exact hm.trans (retract_eq_right h x).symm

/-- Already fixed references are retained exactly. -/
theorem retract_eq_self_of_fixed (x : V)
    (hx : DiagonalNormalization.diagonal f x = x) : retract f x = x := by
  have hxx : f x x = x := hx
  simp only [retract, hxx]

include h in
theorem retract_idempotent (x : V) : retract f (retract f x) = retract f x :=
  retract_eq_self_of_fixed (retract f x) (diagonal_retract_fixed h x)

end Core

/-- Specialization to the literal original raw operational data. -/
def rawRetract (r : RawOperationalData V) : V → V :=
  retract (firstChannel r.operation)

theorem g_rawRetract_fixed (r : RawOperationalData V) (x : V) :
    g r (rawRetract r x) = rawRetract r x :=
  diagonal_retract_fixed (rawLaws r) x

theorem rawRetract_eq_self_of_fixed (r : RawOperationalData V) (x : V)
    (hx : g r x = x) : rawRetract r x = x :=
  retract_eq_self_of_fixed x hx

theorem rawRetract_idempotent (r : RawOperationalData V) (x : V) :
    rawRetract r (rawRetract r x) = rawRetract r x :=
  retract_idempotent (rawLaws r) x

/-- Exactly three original pair gates, with ordered ports (0,1), (2,0), (2,1). -/
def fixedReferenceWord : Native (Fin 3) :=
  .seq (.pair 0 1 (by decide))
    (.seq (.pair 2 0 (by decide)) (.pair 2 1 (by decide)))

/-- The complete final vector, including both unselected outputs. -/
theorem evalRaw_fixedReferenceWord (r : RawOperationalData V) (x : V) :
    evalRaw r.operation fixedReferenceWord (fun _ => x) =
      ![firstChannel r.operation (g r x) x,
        firstChannel r.operation (g r x) (firstChannel r.operation x (g r x)),
        rawRetract r x] := by
  have hs (p : V × V) := raw_operation_eq_symmetric r.operation r.square p
  funext i
  fin_cases i <;>
    simp [fixedReferenceWord, evalRaw, hs, g, DiagonalNormalization.diagonal]
  exact retract_eq_middle (rawLaws r) x

theorem evalRaw_fixedReferenceWord_selected (r : RawOperationalData V) (x : V) :
    evalRaw r.operation fixedReferenceWord (fun _ => x) 2 = rawRetract r x := by
  rw [evalRaw_fixedReferenceWord]
  rfl

/-- Three charged occurrences of one known source label, with all outputs kept. -/
def knownSourceProgram : AllocatedPreparation.Program Unit where
  Wires := Fin 3
  wireFintype := inferInstance
  wireDecidableEq := inferInstance
  input := fun _ => some ()
  circuit := fixedReferenceWord
  cursor := 2

/-- Three vacuum ports; the absence of tags does not make the port count zero. -/
def vacuumProgram : AllocatedPreparation.Program Unit where
  Wires := Fin 3
  wireFintype := inferInstance
  wireDecidableEq := inferInstance
  input := fun _ => none
  circuit := fixedReferenceWord
  cursor := 2

theorem budget_knownSourceProgram : AllocatedPreparation.budget knownSourceProgram = 3 := by
  simp [AllocatedPreparation.budget, AllocatedPreparation.SourceOccurrences,
    knownSourceProgram, Fintype.card_subtype]

theorem budget_vacuumProgram : AllocatedPreparation.budget vacuumProgram = 0 := by
  simp [AllocatedPreparation.budget, AllocatedPreparation.SourceOccurrences, vacuumProgram]

theorem knownSourceProgram_wire_count : Fintype.card knownSourceProgram.Wires = 3 := by decide

theorem vacuumProgram_wire_count : Fintype.card vacuumProgram.Wires = 3 := by decide

theorem eval_knownSourceProgram (r : RawOperationalData V) (x : V) :
    AllocatedPreparation.eval r.operation r.chosenZero (fun _ : Unit => x)
      knownSourceProgram = rawRetract r x :=
  evalRaw_fixedReferenceWord_selected r x

theorem eval_vacuumProgram (r : RawOperationalData V) (stock : Unit → V) :
    AllocatedPreparation.eval r.operation r.chosenZero stock vacuumProgram =
      rawRetract r r.chosenZero :=
  evalRaw_fixedReferenceWord_selected r r.chosenZero

namespace Controls

/-- A nonzero pure minus-sector input in the existing checked raw model. -/
def collapsingSource : SourceLocalOriginalSemantics.Controls.PairCarrier := (0, 1)

theorem collapsingSource_ne_zero : collapsingSource ≠ (0, 0) := by
  intro h
  have hc := congrArg Prod.snd h
  norm_num [collapsingSource] at hc

/-- Retraction can destroy a nonzero source; noncollapse is a separate question. -/
theorem rawRetract_collapses :
    rawRetract SourceLocalOriginalSemantics.Controls.fixedData collapsingSource = (0, 0) := by
  apply Prod.ext <;> apply Complex.ext <;>
    norm_num [rawRetract, retract, firstChannel, collapsingSource,
      SourceLocalOriginalSemantics.Controls.fixedData,
      RawOperationalData.ofWeighted, OriginalGateProbabilityWall.rawData,
      OriginalGateProbabilityWall.operation, CompositeProductControls.RawSign.n]

end Controls

end

end IDT.QMClosure.RawFixedReferencePreparation
