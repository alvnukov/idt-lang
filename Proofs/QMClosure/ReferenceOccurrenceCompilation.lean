import Proofs.QMClosure.OperationalContextQuotient
import Proofs.QMClosure.WeightFreeRawProbability

/-!
# Reference-occurrence compilation of one-hole contexts

Every reference occurrence gets its own input port, even when two occurrences
carry equal values. Compilation uses only native circuit syntax and an arbitrary
raw binary operation. The complete output array is retained; the cursor merely
selects the output that interprets the context.

The input array is given mathematically. Its port count is neither a source
count nor a statistical-independence claim. A preparation certificate may supply
many correlated ports from one source. Arbitrary raw operations may duplicate
values, so fresh syntactic occurrences do not establish physical no-cloning.
Shared-history references require jointly retained outputs or certificates;
replacing one correlated output is not automatically legal. An overwritten input
cannot silently be reused: reuse requires a retained output or another explicit
input occurrence. No physical availability, reference alignment, source
replication, probability law, actualization, particle ontology, or matter regime
is established here.
-/

namespace IDT.QMClosure.ReferenceOccurrenceCompilation

noncomputable section

open OperationalContextQuotient NativeVacuumProbabilityFamily
open WeightFreeRawProbability (evalRaw)

variable {V : Type*}

/-- Padding preserves arbitrary old inputs and every arbitrary fresh input.
There is no distinguished zero and no law on the raw operation. -/
theorem evalRaw_padCircuit {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (T : V × V → V × V) (c : Native ι) (a : ι ⊕ κ → V) :
    evalRaw T (padCircuit κ c) a =
      Sum.elim (evalRaw T c (a ∘ Sum.inl)) (a ∘ Sum.inr) := by
  induction c generalizing a with
  | identity =>
    funext k
    cases k <;> rfl
  | pair i j hij =>
    funext k
    cases k <;> simp [evalRaw, padCircuit, Function.comp_def]
  | permute e =>
    funext k
    cases k <;> rfl
  | seq c d hc hd =>
    change evalRaw T (padCircuit κ d) (evalRaw T (padCircuit κ c) a) = _
    rw [hc, hd]
    rfl

/-- The selected output of one literal raw pair gate. -/
theorem evalRaw_pair_select {ι : Type} [DecidableEq ι]
    (T : V × V → V × V) (i j : ι) (hij : i ≠ j)
    (a : ι → V) (s : Output) :
    evalRaw T (.pair i j hij) a (select s (i, j)) =
      select s (T (a i, a j)) := by
  cases s <;> simp [evalRaw, select, Ne.symm hij]

/-- One distinguished hole port, then one fresh port at every context node. -/
def Ports : Context V → Type
  | .hole => Unit
  | .left _ c _ => Ports c ⊕ Unit
  | .right _ _ c => Ports c ⊕ Unit

instance portsDecidableEq : (c : Context V) → DecidableEq (Ports c)
  | .hole => inferInstanceAs (DecidableEq Unit)
  | .left _ c _ =>
    letI := portsDecidableEq c
    inferInstanceAs (DecidableEq (Ports c ⊕ Unit))
  | .right _ _ c =>
    letI := portsDecidableEq c
    inferInstanceAs (DecidableEq (Ports c ⊕ Unit))

instance portsFintype : (c : Context V) → Fintype (Ports c)
  | .hole => inferInstanceAs (Fintype Unit)
  | .left _ c _ =>
    letI := portsFintype c
    inferInstanceAs (Fintype (Ports c ⊕ Unit))
  | .right _ _ c =>
    letI := portsFintype c
    inferInstanceAs (Fintype (Ports c ⊕ Unit))

/-- Reference syntax is indexed by occurrences, never deduplicated by value. -/
def RefOccurrences : Context V → Type
  | .hole => Empty
  | .left _ c _ => RefOccurrences c ⊕ Unit
  | .right _ _ c => RefOccurrences c ⊕ Unit

def referenceValue : (c : Context V) → RefOccurrences c → V
  | .hole => Empty.elim
  | .left _ c r => Sum.elim (referenceValue c) (fun _ => r)
  | .right _ r c => Sum.elim (referenceValue c) (fun _ => r)

def occurrencePort : (c : Context V) → RefOccurrences c → Ports c
  | .hole => Empty.elim
  | .left _ c _ => Sum.elim (fun q => .inl (occurrencePort c q)) (fun _ => .inr ())
  | .right _ _ c => Sum.elim (fun q => .inl (occurrencePort c q)) (fun _ => .inr ())

def holePort : (c : Context V) → Ports c
  | .hole => ()
  | .left _ c _ => .inl (holePort c)
  | .right _ _ c => .inl (holePort c)

/-- All raw references are visible as supplied input coordinates. -/
def inputs : (c : Context V) → V → Ports c → V
  | .hole, x => fun _ => x
  | .left _ c r, x => Sum.elim (inputs c x) (fun _ => r)
  | .right _ r c, x => Sum.elim (inputs c x) (fun _ => r)

/-- The cursor selects one output; it does not discard the others. -/
def cursor : (c : Context V) → Ports c
  | .hole => ()
  | .left s c _ => select s (.inl (cursor c), .inr ())
  | .right s _ c => select s (.inr (), .inl (cursor c))

/-- Compile the inner word on old ports, then act on its cursor and the fresh
reference port in the context's operand order. No primitive copying or discard
instruction is introduced. -/
def compile : (c : Context V) → Native (Ports c)
  | .hole => .identity
  | .left _ c _ =>
    .seq (padCircuit Unit (compile c))
      (.pair (.inl (cursor c)) (.inr ()) (by simp))
  | .right _ _ c =>
    .seq (padCircuit Unit (compile c))
      (.pair (.inr ()) (.inl (cursor c)) (by simp))

theorem occurrencePort_injective (c : Context V) :
    Function.Injective (occurrencePort c) := by
  induction c with
  | hole => intro q; exact Empty.elim q
  | left s c r ih =>
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (ih (Sum.inl.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => cases a; cases b; rfl
  | right s r c ih =>
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (ih (Sum.inl.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => cases a; cases b; rfl

theorem holePort_not_occurrence (c : Context V) (q : RefOccurrences c) :
    holePort c ≠ occurrencePort c q := by
  induction c with
  | hole => exact Empty.elim q
  | left s c r ih =>
    cases q with
    | inl q => intro h; exact ih q (Sum.inl.inj h)
    | inr q => intro h; cases h
  | right s r c ih =>
    cases q with
    | inl q => intro h; exact ih q (Sum.inl.inj h)
    | inr q => intro h; cases h

theorem inputs_hole (c : Context V) (x : V) :
    inputs c x (holePort c) = x := by
  induction c with
  | hole => rfl
  | left s c r ih => exact ih
  | right s r c ih => exact ih

theorem inputs_reference (c : Context V) (x : V) (q : RefOccurrences c) :
    inputs c x (occurrencePort c q) = referenceValue c q := by
  induction c with
  | hole => exact Empty.elim q
  | left s c r ih =>
    cases q with
    | inl q => exact ih q
    | inr q => rfl
  | right s r c ih =>
    cases q with
    | inl q => exact ih q
    | inr q => rfl

def referenceCount : Context V → Nat
  | .hole => 0
  | .left _ c _ => referenceCount c + 1
  | .right _ _ c => referenceCount c + 1

theorem card_ports (c : Context V) :
    Fintype.card (Ports c) = referenceCount c + 1 := by
  induction c with
  | hole => simp [Ports, referenceCount]
  | left s c r ih =>
    change Fintype.card (Ports c ⊕ Unit) = (referenceCount c + 1) + 1
    rw [Fintype.card_sum, ih]
    simp
  | right s r c ih =>
    change Fintype.card (Ports c ⊕ Unit) = (referenceCount c + 1) + 1
    rw [Fintype.card_sum, ih]
    simp

/-- Exact selected-result semantics for every raw binary operation. The full
compiled array still contains all other outputs. -/
theorem compile_correct (T : V × V → V × V) (c : Context V) (x : V) :
    evalRaw T (compile c) (inputs c x) (cursor c) = Context.eval T c x := by
  induction c with
  | hole => rfl
  | left s c r ih =>
    change evalRaw T (.pair (.inl (cursor c)) (.inr ()) (by simp))
      (evalRaw T (padCircuit Unit (compile c)) (inputs (.left s c r) x))
      (select s (.inl (cursor c), .inr ())) =
        select s (T (Context.eval T c x, r))
    rw [evalRaw_pair_select, evalRaw_padCircuit]
    simp only [inputs, Function.comp_def, Sum.elim_inl, Sum.elim_inr, ih]
  | right s r c ih =>
    change evalRaw T (.pair (.inr ()) (.inl (cursor c)) (by simp))
      (evalRaw T (padCircuit Unit (compile c)) (inputs (.right s r c) x))
      (select s (.inr (), .inl (cursor c))) =
        select s (T (r, Context.eval T c x))
    rw [evalRaw_pair_select, evalRaw_padCircuit]
    simp only [inputs, Function.comp_def, Sum.elim_inl, Sum.elim_inr, ih]

/-- Substitution agrees at selected semantic results. The two sides have
different port types/resources; no equality of complete arrays or physical
composition/preparation theorem is asserted. -/
theorem compile_plug_selected (T : V × V → V × V)
    (c d : Context V) (x : V) :
    evalRaw T (compile (c.plug d)) (inputs (c.plug d) x) (cursor (c.plug d)) =
      evalRaw T (compile c)
        (inputs c (evalRaw T (compile d) (inputs d x) (cursor d))) (cursor c) := by
  rw [compile_correct, compile_correct, compile_correct, Context.eval_plug]

end

end IDT.QMClosure.ReferenceOccurrenceCompilation
