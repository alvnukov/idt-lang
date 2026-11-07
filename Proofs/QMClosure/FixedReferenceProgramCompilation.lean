import Proofs.QMClosure.RawFixedReferencePreparation

/-!
# Explicit preparation of every allocated program input

Each old input position receives three allocated copies of its original tag or
vacuum input. Three original pair gates act within each disjoint block; the
old circuit then acts on the active block while both garbage blocks remain.
The equations hold for every raw operation, without operational laws or source
label equality. The selected preparation is the actual three-gate raw output.

The counts below measure allocated ports, source occurrences, and literal pair
constructors. They imply no copying of unknown inputs, physical joint source
availability, probability preservation, marginalization, erasure, conditioning,
independence, or extension of a single-source probability law to these arrays.
-/

namespace IDT.QMClosure.FixedReferenceProgramCompilation

noncomputable section

open NativeVacuumProbabilityFamily WeightFreeRawProbability AllocatedPreparation
open RawFixedReferencePreparation (fixedReferenceWord)

variable {S V : Type*}

/-- Every output of the actual original three-gate preparation is retained. -/
def preparedOutputs (T : V × V → V × V) (x : V) : Fin 3 → V :=
  evalRaw T fixedReferenceWord (fun _ => x)

/-- The actual selected raw value, with no symmetry or bookend assumption. -/
def preparedValue (T : V × V → V × V) (x : V) : V := preparedOutputs T x 2

/-- Old active ports, first garbage ports, and second garbage ports. -/
abbrev Wires (ι : Type) := ι ⊕ (ι ⊕ ι)

section Batch

variable {ι : Type} [DecidableEq ι]

def triple (x : ι → V) : Wires ι → V := Sum.elim x (Sum.elim x x)

/-- The ordered gates are garbage0/garbage1, active/garbage0, active/garbage1. -/
def block (i : ι) : Native (Wires ι) :=
  .seq (.pair (.inr (.inl i)) (.inr (.inr i)) (by simp))
    (.seq (.pair (.inl i) (.inr (.inl i)) (by simp))
      (.pair (.inl i) (.inr (.inr i)) (by simp)))

/-- Blocks execute from the list tail toward its head. A nodup list has disjoint blocks. -/
def batch : List ι → Native (Wires ι)
  | [] => .identity
  | i :: is => .seq (batch is) (block i)

def stageState (T : V × V → V × V) (x : ι → V) (is : List ι) : Wires ι → V :=
  Sum.elim (fun i => if i ∈ is then preparedOutputs T (x i) 2 else x i)
    (Sum.elim (fun i => if i ∈ is then preparedOutputs T (x i) 0 else x i)
      (fun i => if i ∈ is then preparedOutputs T (x i) 1 else x i))

/-- A nodup batch prepares exactly its listed blocks and leaves all others alone. -/
theorem evalRaw_batch (T : V × V → V × V) (x : ι → V) :
    ∀ is : List ι, is.Nodup →
      evalRaw T (batch is) (triple x) = stageState T x is := by
  intro is
  induction is with
  | nil => intro _; rfl
  | cons i is ih =>
    intro hn
    have hni : i ∉ is := (List.nodup_cons.mp hn).1
    have ht : is.Nodup := (List.nodup_cons.mp hn).2
    change evalRaw T (block i) (evalRaw T (batch is) (triple x)) = _
    rw [ih ht]
    funext w
    rcases w with k | (k | k)
    all_goals
      by_cases hki : k = i
      · subst k
        simp [stageState, block, evalRaw, preparedOutputs, fixedReferenceWord, hni]
      · simp [stageState, block, evalRaw, hki]

def preparedState (T : V × V → V × V) (x : ι → V) : Wires ι → V :=
  Sum.elim (fun i => preparedOutputs T (x i) 2)
    (Sum.elim (fun i => preparedOutputs T (x i) 0)
      (fun i => preparedOutputs T (x i) 1))

variable [Fintype ι]

/-- Each old wire appears once in the finite batch. -/
def preparationWord : Native (Wires ι) := batch (Finset.univ : Finset ι).toList

theorem evalRaw_preparationWord (T : V × V → V × V) (x : ι → V) :
    evalRaw T preparationWord (triple x) = preparedState T x := by
  rw [preparationWord, evalRaw_batch T x _ (Finset.nodup_toList _)]
  funext w
  rcases w with k | (k | k) <;> simp [stageState, preparedState]

end Batch

/-- Triple every original tag/vacuum position, prepare each block, then run the
original circuit on active ports. The entire enlarged output array is retained. -/
def compile (p : Program S) : Program S where
  Wires := Wires p.Wires
  wireFintype := inferInstance
  wireDecidableEq := inferInstance
  input := Sum.elim p.input (Sum.elim p.input p.input)
  circuit := .seq preparationWord (padCircuit (p.Wires ⊕ p.Wires) p.circuit)
  cursor := .inl p.cursor

theorem inputState_compile (zero : V) (stock : S → V) (p : Program S) :
    inputState zero stock (compile p) = triple (inputState zero stock p) := by
  funext w
  rcases w with i | (i | i) <;> rfl

theorem prepared_inputState (T : V × V → V × V) (zero : V) (stock : S → V)
    (p : Program S) :
    (fun i => preparedValue T (inputState zero stock p i)) =
      inputState (preparedValue T zero) (fun s => preparedValue T (stock s)) p := by
  funext i
  cases hi : p.input i <;> simp [inputState, hi]

/-- Exact full output semantics: two garbage blocks remain after the old word. -/
theorem compile_outputs (T : V × V → V × V) (zero : V) (stock : S → V)
    (p : Program S) :
    evalRaw T (compile p).circuit (inputState zero stock (compile p)) =
      Sum.elim
        (evalRaw T p.circuit
          (inputState (preparedValue T zero) (fun s => preparedValue T (stock s)) p))
        (Sum.elim (fun i => preparedOutputs T (inputState zero stock p i) 0)
          (fun i => preparedOutputs T (inputState zero stock p i) 1)) := by
  change evalRaw T (padCircuit (p.Wires ⊕ p.Wires) p.circuit)
    (evalRaw T preparationWord (inputState zero stock (compile p))) = _
  rw [inputState_compile, evalRaw_preparationWord,
    ReferenceOccurrenceCompilation.evalRaw_padCircuit]
  have hp := prepared_inputState T zero stock p
  change Sum.elim (evalRaw T p.circuit
    (fun i => preparedValue T (inputState zero stock p i))) _ = _
  rw [hp]
  rfl

/-- All old output coordinates agree with the old word on prepared inputs. -/
theorem compile_active (T : V × V → V × V) (zero : V) (stock : S → V)
    (p : Program S) (i : p.Wires) :
    evalRaw T (compile p).circuit (inputState zero stock (compile p)) (.inl i) =
      evalRaw T p.circuit
        (inputState (preparedValue T zero) (fun s => preparedValue T (stock s)) p) i := by
  rw [compile_outputs]
  rfl

/-- Main-word pairing and permutations preserve every prepared garbage output. -/
theorem compile_garbage (T : V × V → V × V) (zero : V) (stock : S → V)
    (p : Program S) (i : p.Wires) :
    (evalRaw T (compile p).circuit (inputState zero stock (compile p)) (.inr (.inl i)) =
        preparedOutputs T (inputState zero stock p i) 0) ∧
      (evalRaw T (compile p).circuit (inputState zero stock (compile p)) (.inr (.inr i)) =
        preparedOutputs T (inputState zero stock p i) 1) := by
  rw [compile_outputs]
  exact ⟨rfl, rfl⟩

/-- Selected-value compiler theorem for an arbitrary raw operation. -/
theorem compile_eval (T : V × V → V × V) (zero : V) (stock : S → V)
    (p : Program S) :
    eval T zero stock (compile p) =
      eval T (preparedValue T zero) (fun s => preparedValue T (stock s)) p :=
  compile_active T zero stock p p.cursor

/-- Literal source positions split into three distinct copies, even for equal tags. -/
def compileOccurrencesEquiv (p : Program S) :
    SourceOccurrences (compile p) ≃
      SourceOccurrences p ⊕ (SourceOccurrences p ⊕ SourceOccurrences p) where
  toFun := fun w => match w with
    | ⟨.inl i, hi⟩ => .inl ⟨i, hi⟩
    | ⟨.inr (.inl i), hi⟩ => .inr (.inl ⟨i, hi⟩)
    | ⟨.inr (.inr i), hi⟩ => .inr (.inr ⟨i, hi⟩)
  invFun := fun w => match w with
    | .inl i => ⟨.inl i.val, i.property⟩
    | .inr (.inl i) => ⟨.inr (.inl i.val), i.property⟩
    | .inr (.inr i) => ⟨.inr (.inr i.val), i.property⟩
  left_inv := by
    intro w
    rcases w with ⟨w, hw⟩
    rcases w with i | (i | i) <;> rfl
  right_inv := by
    intro w
    rcases w with i | (i | i) <;> rfl

theorem compile_budget (p : Program S) : budget (compile p) = 3 * budget p := by
  unfold budget
  rw [Fintype.card_congr (compileOccurrencesEquiv p)]
  simp only [Fintype.card_sum]
  omega

theorem compile_width (p : Program S) : Fintype.card (compile p).Wires =
    3 * Fintype.card p.Wires := by
  change Fintype.card (p.Wires ⊕ (p.Wires ⊕ p.Wires)) = _
  simp only [Fintype.card_sum]
  omega

theorem compile_budget_zero (p : Program S) (hp : budget p = 0) :
    budget (compile p) = 0 := by rw [compile_budget, hp, Nat.mul_zero]

/-- Number of literal pair constructors; this is not a physical runtime cost. -/
def pairedGateCount {ι : Type} : Native ι → ℕ
  | .identity => 0
  | .pair _ _ _ => 1
  | .permute _ => 0
  | .seq c d => pairedGateCount c + pairedGateCount d

theorem pairedGateCount_block {ι : Type} [DecidableEq ι] (i : ι) :
    pairedGateCount (block i) = 3 := rfl

theorem pairedGateCount_batch {ι : Type} [DecidableEq ι] (is : List ι) :
    pairedGateCount (batch is) = 3 * is.length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [batch, pairedGateCount, pairedGateCount_block, List.length_cons, ih]
    omega

theorem pairedGateCount_preparationWord {ι : Type} [DecidableEq ι] [Fintype ι] :
    pairedGateCount (preparationWord : Native (Wires ι)) = 3 * Fintype.card ι := by
  rw [preparationWord, pairedGateCount_batch, Finset.length_toList]
  rfl

theorem pairedGateCount_padCircuit {ι κ : Type} (c : Native ι) :
    pairedGateCount (padCircuit κ c) = pairedGateCount c := by
  induction c with
  | identity => rfl
  | pair i j hij => rfl
  | permute e => rfl
  | seq c d hc hd => simp only [padCircuit, pairedGateCount, hc, hd]

theorem compile_pairedGateCount (p : Program S) :
    pairedGateCount (compile p).circuit =
      3 * Fintype.card p.Wires + pairedGateCount p.circuit := by
  change pairedGateCount preparationWord +
    pairedGateCount (padCircuit (p.Wires ⊕ p.Wires) p.circuit) = _
  rw [pairedGateCount_preparationWord, pairedGateCount_padCircuit]

end

end IDT.QMClosure.FixedReferenceProgramCompilation
