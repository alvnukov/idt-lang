import Proofs.QMClosure.FixedReferenceProgramCompilation

/-!
# A doubled original-gate compiler for diagonal normalization

Both initially supplied rails carry the same entire input array. A logical
pair is compiled to two original within-rail pairs followed by two cross-rail
diagonal pairs. Every macro restores literal equality of both rails. No new
source copies are allocated during execution. The generic simulation needs
only diagonal synchronization; its square-swap corollary needs no medial law.

Allocated programs charge both copies of every known input occurrence and
retain both entire output rails. Vacuum ports are doubled even when their
source budget is zero. These are raw evaluation and syntax-count theorems.
No unknown-input encoder, physical joint availability, probability transport,
marginalization, conditioning, or QM closure is established.
-/

namespace IDT.QMClosure.RawDoubledNormalizationCompiler

noncomputable section

open NativeVacuumProbabilityFamily WeightFreeRawProbability AllocatedPreparation
open MedialSwapRoot SourceLocalOriginalSemantics
open FixedReferenceProgramCompilation (pairedGateCount)

variable {S V : Type*}

/-- Postcompose both original gate outputs with the supplied diagonal map. -/
def normalizedWith (T : V × V → V × V) (g : V → V) : V × V → V × V :=
  (Prod.map g g) ∘ T

/-- Two supplied copies of an entire array, not an unknown-input copying gate. -/
def duplicate {ι : Type} (x : ι → V) : ι ⊕ ι → V := Sum.elim x x

theorem duplicate_injective {ι : Type} :
    Function.Injective (fun x : ι → V => duplicate x) := by
  intro x y h
  funext i
  exact congrFun h (.inl i)

section Words

variable {ι : Type}

/-- Four ordered original pairs implementing one logical normalized pair. -/
def pairMacro (i j : ι) (hij : i ≠ j) : Native (ι ⊕ ι) :=
  .seq (.pair (.inl i) (.inl j) (fun h => hij (Sum.inl.inj h)))
    (.seq (.pair (.inr i) (.inr j) (fun h => hij (Sum.inr.inj h)))
      (.seq (.pair (.inl i) (.inr i) (by simp))
        (.pair (.inl j) (.inr j) (by simp))))

/-- Sequence and identity are preserved; each permutation acts on both rails. -/
def compileWord : Native ι → Native (ι ⊕ ι)
  | .identity => .identity
  | .pair i j hij => pairMacro i j hij
  | .permute e => .permute (Equiv.sumCongr e e)
  | .seq c d => .seq (compileWord c) (compileWord d)

variable [DecidableEq ι]

/-- Every output on both rails is synchronized again after one macro. -/
theorem evalRaw_pairMacro (T : V × V → V × V) (g : V → V)
    (hdiag : ∀ z, T (z, z) = (g z, g z)) (i j : ι) (hij : i ≠ j) (x : ι → V) :
    evalRaw T (pairMacro i j hij) (duplicate x) =
      duplicate (evalRaw (normalizedWith T g) (.pair i j hij) x) := by
  funext w
  rcases w with k | k
  all_goals
    by_cases hki : k = i
    · subst k
      simp [pairMacro, evalRaw, duplicate, normalizedWith, hdiag, hij]
    · by_cases hkj : k = j
      · subst k
        simp [pairMacro, evalRaw, duplicate, normalizedWith, hdiag, Ne.symm hij]
      · simp [pairMacro, evalRaw, duplicate, normalizedWith, hki, hkj]

/-- Whole-array simulation at every width and after every compiled subword. -/
theorem evalRaw_compileWord (T : V × V → V × V) (g : V → V)
    (hdiag : ∀ z, T (z, z) = (g z, g z)) (c : Native ι) (x : ι → V) :
    evalRaw T (compileWord c) (duplicate x) =
      duplicate (evalRaw (normalizedWith T g) c x) := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij => exact evalRaw_pairMacro T g hdiag i j hij x
  | permute e =>
    funext w
    cases w <;> rfl
  | seq c d hc hd =>
    change evalRaw T (compileWord d) (evalRaw T (compileWord c) (duplicate x)) = _
    rw [hc, hd]
    rfl

end Words

/-- Square-swap alone forces the two original diagonal outputs to coincide. -/
theorem diagonal_synchronization_of_square (T : V × V → V × V)
    (square : ∀ p, T (T p) = p.swap) (z : V) :
    T (z, z) =
      (DiagonalNormalization.diagonal (firstChannel T) z,
        DiagonalNormalization.diagonal (firstChannel T) z) :=
  raw_operation_eq_symmetric T square (z, z)

/-- Square-only corollary: no first-channel mediality or chosen zero is needed. -/
theorem evalRaw_compileWord_of_square {ι : Type} [DecidableEq ι]
    (T : V × V → V × V) (square : ∀ p, T (T p) = p.swap)
    (c : Native ι) (x : ι → V) :
    evalRaw T (compileWord c) (duplicate x) =
      duplicate (evalRaw
        (normalizedWith T (DiagonalNormalization.diagonal (firstChannel T))) c x) :=
  evalRaw_compileWord T _ (diagonal_synchronization_of_square T square) c x

theorem normalizedWith_rawData (r : RawOperationalData V) :
    normalizedWith r.operation (g r) = r.normalizedOperation := by
  funext p
  exact (normalized_eq_after r p).symm

/-- The standard raw-data adapter uses its literal normalized operation. -/
theorem evalRaw_compileWord_rawData {ι : Type} [DecidableEq ι]
    (r : RawOperationalData V) (c : Native ι) (x : ι → V) :
    evalRaw r.operation (compileWord c) (duplicate x) =
      duplicate (evalRaw r.normalizedOperation c x) := by
  have h := evalRaw_compileWord r.operation (g r)
    (diagonal_synchronization_of_square r.operation r.square) c x
  rw [normalizedWith_rawData] at h
  exact h

/-- Double the original input occurrences once; every output rail is retained. -/
def compileProgram (p : Program S) : Program S where
  Wires := p.Wires ⊕ p.Wires
  wireFintype := inferInstance
  wireDecidableEq := inferInstance
  input := Sum.elim p.input p.input
  circuit := compileWord p.circuit
  cursor := .inl p.cursor

theorem inputState_compileProgram (zero : V) (stock : S → V) (p : Program S) :
    inputState zero stock (compileProgram p) = duplicate (inputState zero stock p) := by
  funext w
  cases w <;> rfl

theorem compileProgram_outputs (T : V × V → V × V) (g : V → V)
    (hdiag : ∀ z, T (z, z) = (g z, g z)) (zero : V) (stock : S → V) (p : Program S) :
    evalRaw T (compileProgram p).circuit (inputState zero stock (compileProgram p)) =
      duplicate (evalRaw (normalizedWith T g) p.circuit (inputState zero stock p)) := by
  rw [inputState_compileProgram]
  exact evalRaw_compileWord T g hdiag p.circuit (inputState zero stock p)

/-- The old zero and source stock are unchanged; no reference projection occurs. -/
theorem compileProgram_eval (T : V × V → V × V) (g : V → V)
    (hdiag : ∀ z, T (z, z) = (g z, g z)) (zero : V) (stock : S → V) (p : Program S) :
    eval T zero stock (compileProgram p) = eval (normalizedWith T g) zero stock p := by
  unfold eval
  rw [compileProgram_outputs T g hdiag zero stock p]
  rfl

theorem compileProgram_eval_rawData (r : RawOperationalData V)
    (zero : V) (stock : S → V) (p : Program S) :
    eval r.operation zero stock (compileProgram p) = eval r.normalizedOperation zero stock p := by
  rw [← normalizedWith_rawData r]
  exact compileProgram_eval r.operation (g r)
    (diagonal_synchronization_of_square r.operation r.square) zero stock p

/-- Two positions are charged even when their source tags agree. -/
def compileProgramOccurrencesEquiv (p : Program S) :
    SourceOccurrences (compileProgram p) ≃ SourceOccurrences p ⊕ SourceOccurrences p where
  toFun := fun w => match w with
    | ⟨.inl i, hi⟩ => .inl ⟨i, hi⟩
    | ⟨.inr i, hi⟩ => .inr ⟨i, hi⟩
  invFun := fun w => match w with
    | .inl i => ⟨.inl i.val, i.property⟩
    | .inr i => ⟨.inr i.val, i.property⟩
  left_inv := by
    intro w
    rcases w with ⟨w, hw⟩
    cases w <;> rfl
  right_inv := by
    intro w
    cases w <;> rfl

theorem compileProgram_budget (p : Program S) :
    budget (compileProgram p) = 2 * budget p := by
  unfold budget
  rw [Fintype.card_congr (compileProgramOccurrencesEquiv p), Fintype.card_sum]
  omega

theorem compileProgram_width (p : Program S) :
    Fintype.card (compileProgram p).Wires = 2 * Fintype.card p.Wires := by
  change Fintype.card (p.Wires ⊕ p.Wires) = _
  rw [Fintype.card_sum]
  omega

theorem compileProgram_budget_zero (p : Program S) (hp : budget p = 0) :
    budget (compileProgram p) = 0 := by rw [compileProgram_budget, hp, Nat.mul_zero]

/-- Four literal original pair constructors replace each old pair constructor. -/
theorem compileWord_pairedGateCount {ι : Type} (c : Native ι) :
    pairedGateCount (compileWord c) = 4 * pairedGateCount c := by
  induction c with
  | identity => rfl
  | pair i j hij => rfl
  | permute e => rfl
  | seq c d hc hd => simp only [compileWord, pairedGateCount, hc, hd, Nat.mul_add]

theorem compileProgram_pairedGateCount (p : Program S) :
    pairedGateCount (compileProgram p).circuit = 4 * pairedGateCount p.circuit :=
  compileWord_pairedGateCount p.circuit

end

end IDT.QMClosure.RawDoubledNormalizationCompiler
