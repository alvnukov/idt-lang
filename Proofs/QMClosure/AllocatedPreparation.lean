import Proofs.QMClosure.NativeRecipeContextRealization

/-!
# Explicitly allocated raw preparations

A program retains a finite input array, a native word, and every output wire.
The cursor selects one value. Tags record supplied source occurrences; distinct
tagged wires count separately even when their labels agree. Pairing makes two
disjoint copies of the supplied program syntax and charges both input arrays.
This is allocation of known preparations, not cloning of an unknown token.

Joint availability of the tagged input array in the specified common raw frame
remains a physical hypothesis. The budget measures syntax, not physical
capacity, independence, tensor factors, or particle number. A probability law
for a single basis preparation does not automatically cover these arrays.

All compiler equations below concern arbitrary raw operations and selected
values. They assume no zero preservation, linearity, mediality, square law,
readout, probability, or identity between different preparation histories.
-/

namespace IDT.QMClosure.AllocatedPreparation

noncomputable section

open NativeVacuumProbabilityFamily NativeGaussianResponse
open OperationalContextQuotient
open WeightFreeRawProbability (evalRaw)
open ReferenceOccurrenceCompilation (evalRaw_padCircuit evalRaw_pair_select referenceCount)
open NativeRecipeContextRealization (mapRefs)

variable {S V : Type*}

/-- A complete finite raw preparation with explicitly tagged input resources. -/
structure Program (S : Type*) where
  Wires : Type
  wireFintype : Fintype Wires
  wireDecidableEq : DecidableEq Wires
  input : Wires → Option S
  circuit : Native Wires
  cursor : Wires

attribute [instance] Program.wireFintype Program.wireDecidableEq

/-- A source occurrence is an input position, not a distinct source label. -/
def SourceOccurrences (p : Program S) :=
  {w : p.Wires // (p.input w).isSome = true}

instance sourceOccurrencesFintype (p : Program S) : Fintype (SourceOccurrences p) :=
  inferInstanceAs (Fintype {w : p.Wires // (p.input w).isSome = true})

def occurrencePort (p : Program S) : SourceOccurrences p → p.Wires := Subtype.val

theorem occurrencePort_injective (p : Program S) :
    Function.Injective (occurrencePort p) := Subtype.val_injective

/-- Every tagged position is charged, including repeated labels. -/
def budget (p : Program S) : ℕ := Fintype.card (SourceOccurrences p)

def inputState (zero : V) (stock : S → V) (p : Program S) : p.Wires → V :=
  fun w => (p.input w).elim zero stock

def eval (T : V × V → V × V) (zero : V) (stock : S → V) (p : Program S) : V :=
  evalRaw T p.circuit (inputState zero stock p) p.cursor

/-- A zero input, with no tagged source. No condition on `T (zero, zero)` is used. -/
def zeroProgram : Program S where
  Wires := Unit
  wireFintype := inferInstance
  wireDecidableEq := inferInstance
  input := fun _ => none
  circuit := .identity
  cursor := ()

/-- A supplied source occurrence at a single identity wire. -/
def sourceProgram (label : S) : Program S where
  Wires := Unit
  wireFintype := inferInstance
  wireDecidableEq := inferInstance
  input := fun _ => some label
  circuit := .identity
  cursor := ()

@[simp] theorem eval_zeroProgram (T : V × V → V × V) (zero : V) (stock : S → V) :
    eval T zero stock (zeroProgram : Program S) = zero := rfl

@[simp] theorem eval_sourceProgram (T : V × V → V × V) (zero : V)
    (stock : S → V) (label : S) :
    eval T zero stock (sourceProgram label) = stock label := rfl

@[simp] theorem budget_zeroProgram : budget (zeroProgram : Program S) = 0 := by
  simp [budget, SourceOccurrences, zeroProgram]

@[simp] theorem budget_sourceProgram (label : S) : budget (sourceProgram label) = 1 := by
  simp [budget, SourceOccurrences, sourceProgram, Fintype.card_subtype]

section Event

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Preserve the actual event word and tower. Only its marked basis input is
tagged; the other input coordinates receive the supplied zero. -/
def ofEvent (label : S) (s : ι) (e : Event ι) : Program S where
  Wires := Tower ι e.level
  wireFintype := inferInstance
  wireDecidableEq := inferInstance
  input := fun w => if w = sourceAt s e.level then some label else none
  circuit := e.circuit
  cursor := e.port

theorem inputState_ofEvent (zero : V) (stock : S → V) (label : S)
    (s : ι) (e : Event ι) :
    inputState zero stock (ofEvent label s e) =
      fun w => if w = sourceAt s e.level then stock label else zero := by
  funext w
  change (if w = sourceAt s e.level then some label else none).elim zero stock =
    if w = sourceAt s e.level then stock label else zero
  split_ifs <;> rfl

/-- The original raw basis recipe, at exactly the original circuit and level. -/
theorem eval_ofEvent (T : V × V → V × V) (zero : V) (stock : S → V)
    (label : S) (s : ι) (e : Event ι) :
    eval T zero stock (ofEvent label s e) =
      evalRaw T e.circuit
        (fun w => if w = sourceAt s e.level then stock label else zero) e.port := by
  unfold eval
  rw [inputState_ofEvent]
  rfl

theorem ofEvent_occurrence_eq_source (label : S) (s : ι) (e : Event ι)
    (w : SourceOccurrences (ofEvent label s e)) :
    w.val = sourceAt s e.level := by
  by_contra h
  have hw := w.property
  simp [ofEvent] at hw
  exact h hw

/-- There is precisely one allocated source occurrence, independently of level. -/
def ofEventOccurrenceEquiv (label : S) (s : ι) (e : Event ι) :
    SourceOccurrences (ofEvent label s e) ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => ⟨sourceAt s e.level, by simp [ofEvent]⟩
  left_inv := by
    intro w
    apply Subtype.ext
    exact (ofEvent_occurrence_eq_source label s e w).symm
  right_inv := by intro u; cases u; rfl

@[simp] theorem budget_ofEvent (label : S) (s : ι) (e : Event ι) :
    budget (ofEvent label s e) = 1 := by
  unfold budget
  rw [Fintype.card_congr (ofEventOccurrenceEquiv label s e)]
  simp

end Event

/-- Constructorwise right-block lifting; every left input stays untouched. -/
def rightLift {ι : Type} (κ : Type) : Native ι → Native (κ ⊕ ι)
  | .identity => .identity
  | .pair i j hij => .pair (.inr i) (.inr j) (fun h => hij (Sum.inr.inj h))
  | .permute e => .permute (Equiv.sumCongr (Equiv.refl κ) e)
  | .seq c d => .seq (rightLift κ c) (rightLift κ d)

/-- Arbitrary left inputs, including nonzero ones, survive right-block execution. -/
theorem evalRaw_rightLift {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (T : V × V → V × V) (c : Native ι) (a : κ ⊕ ι → V) :
    evalRaw T (rightLift κ c) a =
      Sum.elim (a ∘ Sum.inl) (evalRaw T c (a ∘ Sum.inr)) := by
  induction c generalizing a with
  | identity =>
    funext k
    cases k <;> rfl
  | pair i j hij =>
    funext k
    cases k <;> simp [evalRaw, rightLift, Function.comp_def]
  | permute e =>
    funext k
    cases k <;> rfl
  | seq c d hc hd =>
    change evalRaw T (rightLift κ d) (evalRaw T (rightLift κ c) a) = _
    rw [hc, hd]
    rfl

/-- The full two-block word evaluates both given arrays without disturbing the
other block. This is stronger than the selected-value compiler theorem. -/
theorem evalRaw_blocks {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (T : V × V → V × V) (c : Native ι) (d : Native κ) (a : ι ⊕ κ → V) :
    evalRaw T (.seq (padCircuit κ c) (rightLift ι d)) a =
      Sum.elim (evalRaw T c (a ∘ Sum.inl)) (evalRaw T d (a ∘ Sum.inr)) := by
  change evalRaw T (rightLift ι d) (evalRaw T (padCircuit κ c) a) = _
  rw [evalRaw_padCircuit, evalRaw_rightLift]
  rfl

/-- Literal disjoint allocation, then one ordered raw pair at the two cursors.
Even `pair o p p` contains two allocated copies of all tagged input positions. -/
def pair (o : Output) (p q : Program S) : Program S where
  Wires := p.Wires ⊕ q.Wires
  wireFintype := inferInstance
  wireDecidableEq := inferInstance
  input := Sum.elim p.input q.input
  circuit := .seq (.seq (padCircuit q.Wires p.circuit) (rightLift p.Wires q.circuit))
    (.pair (.inl p.cursor) (.inr q.cursor) (by simp))
  cursor := select o (.inl p.cursor, .inr q.cursor)

theorem inputState_pair (zero : V) (stock : S → V) (o : Output) (p q : Program S) :
    inputState zero stock (pair o p q) =
      Sum.elim (inputState zero stock p) (inputState zero stock q) := by
  funext w
  cases w <;> rfl

/-- Only the selected value is compared; all other program outputs are retained. -/
theorem eval_pair (T : V × V → V × V) (zero : V) (stock : S → V)
    (o : Output) (p q : Program S) :
    eval T zero stock (pair o p q) =
      select o (T (eval T zero stock p, eval T zero stock q)) := by
  change evalRaw T (.pair (.inl p.cursor) (.inr q.cursor) (by simp))
    (evalRaw T (.seq (padCircuit q.Wires p.circuit) (rightLift p.Wires q.circuit))
      (inputState zero stock (pair o p q)))
    (select o (.inl p.cursor, .inr q.cursor)) = _
  rw [evalRaw_pair_select, evalRaw_blocks, inputState_pair]
  rfl

/-- Resource occurrences split by allocated block, with no equality test on labels. -/
def pairOccurrencesEquiv (o : Output) (p q : Program S) :
    SourceOccurrences (pair o p q) ≃ SourceOccurrences p ⊕ SourceOccurrences q where
  toFun := fun w => match w with
    | ⟨.inl i, hi⟩ => .inl ⟨i, hi⟩
    | ⟨.inr j, hj⟩ => .inr ⟨j, hj⟩
  invFun := fun w => match w with
    | .inl i => ⟨.inl i.val, i.property⟩
    | .inr j => ⟨.inr j.val, j.property⟩
  left_inv := by
    intro w
    rcases w with ⟨w, hw⟩
    cases w <;> rfl
  right_inv := by
    intro w
    cases w <;> rfl

theorem budget_pair (o : Output) (p q : Program S) :
    budget (pair o p q) = budget p + budget q := by
  unfold budget
  rw [Fintype.card_congr (pairOccurrencesEquiv o p q), Fintype.card_sum]

theorem budget_repeated (o : Output) (p : Program S) :
    budget (pair o p p) = budget p + budget p := budget_pair o p p

/-- Each context reference occurrence supplies a whole preparation afresh. -/
def realize : Context (Program S) → Program S → Program S
  | .hole, p => p
  | .left o c r, p => pair o (realize c p) r
  | .right o r c, p => pair o r (realize c p)

def referenceBudget : Context (Program S) → ℕ
  | .hole => 0
  | .left _ c r => referenceBudget c + budget r
  | .right _ r c => budget r + referenceBudget c

theorem eval_realize (T : V × V → V × V) (zero : V) (stock : S → V)
    (C : Context (Program S)) (p : Program S) :
    eval T zero stock (realize C p) =
      Context.eval T (mapRefs (eval T zero stock) C) (eval T zero stock p) := by
  induction C with
  | hole => rfl
  | left o c r ih =>
    simp only [realize, eval_pair, mapRefs, Context.eval, ih]
  | right o r c ih =>
    simp only [realize, eval_pair, mapRefs, Context.eval, ih]

theorem budget_realize (C : Context (Program S)) (p : Program S) :
    budget (realize C p) = budget p + referenceBudget C := by
  induction C with
  | hole => simp [realize, referenceBudget]
  | left o c r ih =>
    rw [realize, budget_pair, ih, referenceBudget]
    omega
  | right o r c ih =>
    rw [realize, budget_pair, ih, referenceBudget]
    omega

section EventContexts

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem referenceBudget_ofEvent (label : S) (s : ι) (C : Context (Event ι)) :
    referenceBudget (mapRefs (ofEvent label s) C) = referenceCount C := by
  induction C with
  | hole => rfl
  | left o c r ih =>
    simp only [mapRefs, referenceBudget, referenceCount, budget_ofEvent, ih]
  | right o r c ih =>
    simp only [mapRefs, referenceBudget, referenceCount, budget_ofEvent, ih]
    omega

/-- One supplied occurrence per reference, plus the one-source hole preparation.
The same source label may appear throughout; every occurrence is still charged. -/
theorem budget_realize_ofEvent (label : S) (s : ι)
    (C : Context (Event ι)) (e : Event ι) :
    budget (realize (mapRefs (ofEvent label s) C) (ofEvent label s e)) =
      referenceCount C + 1 := by
  rw [budget_realize, budget_ofEvent, referenceBudget_ofEvent]
  omega

end EventContexts

end

end IDT.QMClosure.AllocatedPreparation
