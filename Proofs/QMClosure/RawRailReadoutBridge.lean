import Proofs.QMClosure.ResponseDoubledNormalizationCompiler
import Proofs.QMClosure.ReferenceOccurrenceCompilation

/-!
# A supplied physical rail law implies the existing logical compiled law

The domain includes every original-operation raw word, with two supplied copies
of the old basis input. Relayout-aware vacuum padding is a new supplied axiom.
No transfer from a fixed-seed single-source law or converse is asserted.
The rail law assigns one categorical outcome label from the complete rail set.
Two source occurrences specify supplied preparation resources; they do not specify
particle number, independent trials, or a joint click-pattern distribution.
No two-particle/Fock preparation or one-click actualization follows.
-/

namespace IDT.QMClosure.RawRailReadoutBridge

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open ResponseContextQuotient NativeVacuumProbabilityFamily
open MixerGeneratedProcessWall
open RawDoubledNormalizationCompiler (compileWord duplicate pairMacro)
open scoped BigOperators

variable {V Ω : Type*}

/-- Rename every physical wire, including conjugation of output permutations. -/
def renameWord {α β : Type} (e : α ≃ β) : Native α → Native β
  | .identity => .identity
  | .pair i j hij => .pair (e i) (e j) (fun h => hij (e.injective h))
  | .permute p => .permute (e.symm.trans (p.trans e))
  | .seq c f => .seq (renameWord e c) (renameWord e f)

/-- The old rails and the fresh rails are regrouped by their logical positions. -/
def relay (ι κ : Type) : ((ι ⊕ ι) ⊕ (κ ⊕ κ)) ≃ ((ι ⊕ κ) ⊕ (ι ⊕ κ)) where
  toFun := Sum.elim (Sum.elim (fun i => .inl (.inl i)) (fun i => .inr (.inl i)))
    (Sum.elim (fun k => .inl (.inr k)) (fun k => .inr (.inr k)))
  invFun := Sum.elim (Sum.elim (fun i => .inl (.inl i)) (fun k => .inr (.inl k)))
    (Sum.elim (fun i => .inl (.inr i)) (fun k => .inr (.inr k)))
  left_inv := by intro w; rcases w with (i | i) | (k | k) <;> rfl
  right_inv := by intro w; rcases w with (i | k) | (i | k) <;> rfl

def railInl {ι κ : Type} : ι ⊕ ι → (ι ⊕ κ) ⊕ (ι ⊕ κ) :=
  Sum.elim (fun i => .inl (.inl i)) (fun i => .inr (.inl i))

def railPad {ι : Type} (κ : Type) (c : Native (ι ⊕ ι)) :
    Native ((ι ⊕ κ) ⊕ (ι ⊕ κ)) :=
  renameWord (relay ι κ) (padCircuit (κ ⊕ κ) c)

/-- Covariance is valid for arbitrary raw operations and arbitrary input arrays. -/
theorem evalRaw_renameWord {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : V × V → V × V) (e : α ≃ β) (c : Native α) (x : β → V) :
    WeightFreeRawProbability.evalRaw T (renameWord e c) x =
      (WeightFreeRawProbability.evalRaw T c (x ∘ e)) ∘ e.symm := by
  induction c generalizing x with
  | identity => funext w; simp [renameWord, WeightFreeRawProbability.evalRaw]
  | pair i j hij =>
    funext w
    have hi : w = e i ↔ e.symm w = i := by
      constructor
      · intro h; rw [h]; simp
      · intro h; simpa using congrArg e h
    have hj : w = e j ↔ e.symm w = j := by
      constructor
      · intro h; rw [h]; simp
      · intro h; simpa using congrArg e h
    simp [renameWord, WeightFreeRawProbability.evalRaw, hi, hj]
  | permute p =>
    funext w
    simp [renameWord, WeightFreeRawProbability.evalRaw]
  | seq c f hc hf =>
    simp only [renameWord, WeightFreeRawProbability.evalRaw]
    rw [hf, hc]
    have hinput :
        ((WeightFreeRawProbability.evalRaw T c (x ∘ e)) ∘ e.symm) ∘ e =
          WeightFreeRawProbability.evalRaw T c (x ∘ e) := by
      funext i
      simp
    rw [hinput]

/-- This syntax identity is the layout bridge used by logical vacuum extension. -/
theorem railPad_compileWord {ι κ : Type} (c : Native ι) :
    railPad κ (compileWord c) = compileWord (padCircuit κ c) := by
  induction c with
  | identity => rfl
  | pair i j hij => rfl
  | permute e =>
    apply congrArg Circuit.permute
    apply Equiv.ext
    intro w
    rcases w with (i | k) | (i | k) <;> rfl
  | seq c f hc hf => exact congrArg₂ Circuit.seq hc hf

def rawPrepared (d : Data V Ω) (v : V) {ι : Type} [DecidableEq ι]
    (s : ι) (c : Native (ι ⊕ ι)) : ι ⊕ ι → V :=
  WeightFreeRawProbability.evalRaw d.operation c
    (duplicate (ResponseNativeProbabilitySelection.basisInput d v s))

/-- The exact old input values survive physical zero padding and relayout. -/
theorem rawPrepared_railPad (d : Data V Ω) (v : V)
    {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (s : ι) (c : Native (ι ⊕ ι)) (w : ι ⊕ ι) :
    rawPrepared d v (.inl s) (railPad κ c) (railInl w) = rawPrepared d v s c w := by
  unfold rawPrepared railPad
  rw [evalRaw_renameWord, ReferenceOccurrenceCompilation.evalRaw_padCircuit]
  have hin :
      (duplicate (ResponseNativeProbabilitySelection.basisInput d v (.inl s)) ∘
        relay ι κ) ∘ Sum.inl =
      duplicate (ResponseNativeProbabilitySelection.basisInput d v s) := by
    funext a
    cases a <;> simp [duplicate, relay, Function.comp_def,
      ResponseNativeProbabilitySelection.basisInput]
  rw [hin]
  cases w <;> rfl

/-- Six supplied physical conditions on all raw words, with a logical seed.
The last condition is relayout-aware padding, not older fixed-seed padding. -/
structure RailLaw (d : Data V Ω) (v : V) where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] →
    ι → Native (ι ⊕ ι) → (ι ⊕ ι) → ℝ
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native (ι ⊕ ι)) (w : ι ⊕ ι), 0 ≤ prob s c w
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native (ι ⊕ ι)), ∑ w, prob s c w = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c e : Native (ι ⊕ ι)),
    (∀ w, ResponseEq d.operation d.signature
      (rawPrepared d v s c w) (rawPrepared d v s e w)) → prob s c = prob s e
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native (ι ⊕ ι))
    (e : Equiv.Perm (ι ⊕ ι)) w, prob s (.seq c (.permute e)) w = prob s c (e w)
  spectator_pair : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native (ι ⊕ ι))
    (a b w : ι ⊕ ι) (hab : a ≠ b), w ≠ a → w ≠ b →
    prob s (.seq c (.pair a b hab)) w = prob s c w
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Native (ι ⊕ ι)) (w : ι ⊕ ι), prob (.inl s) (railPad κ c) (railInl w) = prob s c w

/-- Equal full contextual responses within one raw output force equal readouts. -/
theorem probability_eq_of_responseEq (d : Data V Ω) (v : V) (L : RailLaw d v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native (ι ⊕ ι))
    (a b : ι ⊕ ι)
    (h : ResponseEq d.operation d.signature (rawPrepared d v s c a)
      (rawPrepared d v s c b)) : L.prob s c a = L.prob s c b := by
  classical
  have he : ∀ w, ResponseEq d.operation d.signature
      (rawPrepared d v s (.seq c (.permute (Equiv.swap a b))) w)
      (rawPrepared d v s c w) := by
    intro w
    by_cases hwa : w = a
    · subst w
      simpa [rawPrepared, WeightFreeRawProbability.evalRaw] using
        (responseSetoid d.operation d.signature).symm h
    · by_cases hwb : w = b
      · subst w
        simpa [rawPrepared, WeightFreeRawProbability.evalRaw] using h
      · simp [rawPrepared, WeightFreeRawProbability.evalRaw,
          Equiv.swap_apply_of_ne_of_ne hwa hwb]
        intro q
        rfl
  have hp := congrFun (L.prepared_eq s _ _ he) a
  rw [L.output_perm] at hp
  simpa using hp.symm

/-- Literal all-zero outputs remain all zero under the exact physical padding. -/
theorem rawPrepared_railPad_all_zero (d : Data V Ω) (v : V)
    {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (s : ι) (c : Native (ι ⊕ ι))
    (h : ∀ w, rawPrepared d v s c w = d.chosenZero) :
    ∀ w, rawPrepared d v (.inl s) (railPad κ c) w = d.chosenZero := by
  intro w
  rcases w with (i | k) | (i | k)
  · exact (rawPrepared_railPad d v s c (.inl i)).trans (h (.inl i))
  · unfold rawPrepared railPad
    rw [evalRaw_renameWord, ReferenceOccurrenceCompilation.evalRaw_padCircuit]
    simp [Function.comp_def, relay, duplicate, ResponseNativeProbabilitySelection.basisInput]
  · exact (rawPrepared_railPad d v s c (.inr i)).trans (h (.inr i))
  · unfold rawPrepared railPad
    rw [evalRaw_renameWord, ReferenceOccurrenceCompilation.evalRaw_padCircuit]
    simp [Function.comp_def, relay, duplicate, ResponseNativeProbabilitySelection.basisInput]

/-- Width two to four already forbids a raw word that erases both source rails.
This uses the new relayout-aware axiom on this exact RailLaw domain. -/
theorem no_law_of_zero_prepared (d : Data V Ω) (v : V)
    (c : Native ((Fin 1) ⊕ (Fin 1)))
    (h : ∀ w, rawPrepared d v (0 : Fin 1) c w = d.chosenZero) :
    ¬ Nonempty (RailLaw d v) := by
  rintro ⟨L⟩
  have eqOld (w : (Fin 1) ⊕ (Fin 1)) :
      L.prob (0 : Fin 1) c w = L.prob (0 : Fin 1) c (.inl 0) := by
    apply probability_eq_of_responseEq
    rw [h, h]
    intro q
    rfl
  have hz := rawPrepared_railPad_all_zero (κ := Unit) d v (0 : Fin 1) c h
  have eqNew (w : ((Fin 1) ⊕ Unit) ⊕ ((Fin 1) ⊕ Unit)) :
      L.prob (.inl (0 : Fin 1)) (railPad Unit c) w =
        L.prob (0 : Fin 1) c (.inl 0) := by
    rw [← L.vacuum (κ := Unit) (0 : Fin 1) c (.inl 0)]
    apply probability_eq_of_responseEq
    rw [hz, hz]
    intro q
    rfl
  have ho := L.normalized (0 : Fin 1) c
  have hn := L.normalized (.inl (0 : Fin 1)) (railPad Unit c)
  simp only [eqOld, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
    Fintype.card_fin, nsmul_eq_mul] at ho
  simp only [eqNew, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_unit, nsmul_eq_mul] at hn
  norm_num at ho hn
  linarith

/-- A single original pair erasing the two supplied source occurrences rules out
this RailLaw, independently of the logical compiled law. -/
theorem no_law_of_source_pair_zero (d : Data V Ω) (v : V)
    (h : d.operation (v, v) = (d.chosenZero, d.chosenZero)) :
    ¬ Nonempty (RailLaw d v) := by
  apply no_law_of_zero_prepared d v
    (.pair (.inl (0 : Fin 1)) (.inr (0 : Fin 1)) (by simp))
  intro w
  rcases w with i | i <;> fin_cases i <;>
    simp [rawPrepared, WeightFreeRawProbability.evalRaw,
      RawDoubledNormalizationCompiler.duplicate,
      ResponseNativeProbabilitySelection.basisInput, h]

/-- Summing the two retained physical rails gives the exact existing logical law. -/
def toCompiledLaw (d : Data V Ω) (v : V) (L : RailLaw d v) :
    ResponseDoubledNormalizationCompiler.CompiledLaw d v where
  prob s c i := L.prob s (compileWord c) (.inl i) + L.prob s (compileWord c) (.inr i)
  nonnegative s c i := add_nonneg (L.nonnegative s _ _) (L.nonnegative s _ _)
  normalized s c := by
    rw [Finset.sum_add_distrib]
    simpa only [Fintype.sum_sum_type] using L.normalized s (compileWord c)
  prepared_eq s c e h := by
    have hp := L.prepared_eq s (compileWord c) (compileWord e) h
    funext i
    rw [congrFun hp (.inl i), congrFun hp (.inr i)]
  output_perm s c e i := by
    change L.prob s (.seq (compileWord c) (.permute (Equiv.sumCongr e e))) (.inl i) +
      L.prob s (.seq (compileWord c) (.permute (Equiv.sumCongr e e))) (.inr i) = _
    rw [L.output_perm, L.output_perm]
    rfl
  spectator_pair s c i j k hij hki hkj := by
    have hs (w : _ ⊕ _) (hwi : w ≠ .inl i) (hwj : w ≠ .inl j)
        (hwri : w ≠ .inr i) (hwrj : w ≠ .inr j) :
        L.prob s (compileWord (.seq c (.pair i j hij))) w =
          L.prob s (compileWord c) w := by
      have reassoc (a b f : Native (_ ⊕ _)) :
          L.prob s (.seq a (.seq b f)) = L.prob s (.seq (.seq a b) f) := by
        apply L.prepared_eq
        intro q context
        rfl
      simp only [compileWord, pairMacro]
      rw [reassoc, reassoc, reassoc]
      rw [L.spectator_pair s _ _ _ _ _ hwj hwrj,
        L.spectator_pair s _ _ _ _ _ hwi hwri,
        L.spectator_pair s _ _ _ _ _ hwri hwrj,
        L.spectator_pair s _ _ _ _ _ hwi hwj]
    rw [hs (.inl k) (by simpa using hki) (by simpa using hkj) (by simp) (by simp),
      hs (.inr k) (by simp) (by simp) (by simpa using hki) (by simpa using hkj)]
  vacuum s c i := by
    rw [← railPad_compileWord]
    exact congrArg₂ (· + ·) (L.vacuum s (compileWord c) (.inl i))
      (L.vacuum s (compileWord c) (.inr i))

theorem compiled_rails_responseEq (d : Data V Ω) (v : V)
    {ι : Type} [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    ResponseEq d.operation d.signature
      (rawPrepared d v s (compileWord c) (.inl i))
      (rawPrepared d v s (compileWord c) (.inr i)) := by
  apply (d.classOf_eq_iff_responseEq _ _).mp
  have h := ResponseDoubledNormalizationCompiler.encodedPrepared_class d v s c
  exact (congrFun h (.inl i)).trans (congrFun h (.inr i)).symm

/-- Each physical rail at the compiled boundary has exactly half the logical value. -/
theorem compiled_left_probability (d : Data V Ω) (v : V) (L : RailLaw d v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s (compileWord c) (.inl i) = Complex.normSq (c.eval (source s) i) / 2 := by
  have he := probability_eq_of_responseEq d v L s (compileWord c) (.inl i) (.inr i)
    (compiled_rails_responseEq d v s c i)
  have hp := ResponseDoubledNormalizationCompiler.probability_eq_normSq d v
    (toCompiledLaw d v L) s c i
  change L.prob s (compileWord c) (.inl i) + L.prob s (compileWord c) (.inr i) = _ at hp
  linarith

theorem compiled_right_probability (d : Data V Ω) (v : V) (L : RailLaw d v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s (compileWord c) (.inr i) = Complex.normSq (c.eval (source s) i) / 2 := by
  rw [← probability_eq_of_responseEq d v L s (compileWord c) (.inl i) (.inr i)
    (compiled_rails_responseEq d v s c i)]
  exact compiled_left_probability d v L s c i

theorem compiled_probability_fields_equal (d : Data V Ω) (v : V) (L M : RailLaw d v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (w : ι ⊕ ι) :
    L.prob s (compileWord c) w = M.prob s (compileWord c) w := by
  cases w with
  | inl i => rw [compiled_left_probability, compiled_left_probability]
  | inr i => rw [compiled_right_probability, compiled_right_probability]

/-- Necessary condition only; no converse or arbitrary-raw-word uniqueness follows. -/
theorem law_nonempty_implies_reference_infiniteOrder (d : Data V Ω) (v : V)
    (h : Nonempty (RailLaw d v)) :
    WeightFreeRawProbability.ReferenceInfiniteOrder d.quotientData (d.classOf v) := by
  obtain ⟨L⟩ := h
  exact (ResponseDoubledNormalizationCompiler.law_nonempty_iff_reference_infiniteOrder d v).mp
    ⟨toCompiledLaw d v L⟩

end
end IDT.QMClosure.RawRailReadoutBridge
