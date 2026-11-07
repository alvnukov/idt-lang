import Proofs.QMClosure.RawRailReadoutBridge
import Proofs.QMClosure.ResponseClassPreparationCompiler
import Proofs.QMClosure.NativeSignedVariationSelection

/-!
# Bounded signed variation on actual compiled raw rails

The supplied rail law assigns arbitrary signed real values to all original raw
words. Its five conditions contain no nonnegativity premise. Equal paired rail
values and their sum produce the existing native signed accounting contract.
The explicit all-event, all-depth variation premise selects quadratic readout
on compiled words and only then supplies a positive logical compiled law.
No positive law on all raw rail words, outcome actualization, physical input
availability, or full QM closure is constructed.
-/

namespace IDT.QMClosure.SignedRawRailReadoutBridge

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open ResponseContextQuotient NativeVacuumProbabilityFamily
open MixerGeneratedProcessWall RawRailReadoutBridge
open RawDoubledNormalizationCompiler (compileWord pairMacro)
open NativeBinaryLeaves NativeBinaryRefinement
open scoped BigOperators

variable {V Ω : Type*}

/-- The old all-word physical rail contract with only nonnegativity omitted. -/
structure SignedRailLaw (d : Data V Ω) (v : V) where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] →
    ι → Native (ι ⊕ ι) → (ι ⊕ ι) → ℝ
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native (ι ⊕ ι)), ∑ w, prob s c w = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c e : Native (ι ⊕ ι)),
    (∀ w, ResponseEq d.operation d.signature
      (rawPrepared d v s c w) (rawPrepared d v s e w)) → prob s c = prob s e
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native (ι ⊕ ι)) (e : Equiv.Perm (ι ⊕ ι)) w,
    prob s (.seq c (.permute e)) w = prob s c (e w)
  spectator_pair : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native (ι ⊕ ι)) (a b w : ι ⊕ ι) (hab : a ≠ b),
    w ≠ a → w ≠ b → prob s (.seq c (.pair a b hab)) w = prob s c w
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Native (ι ⊕ ι)) (w : ι ⊕ ι),
    prob (.inl s) (railPad κ c) (railInl w) = prob s c w

/-- Swap consistency alone equates response-equivalent output values. -/
theorem probability_eq_of_responseEq (d : Data V Ω) (v : V) (L : SignedRailLaw d v)
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

/-- The same marked logical source and whole circuit determine the paired sum. -/
def toNativeSignedLaw (d : Data V Ω) (v : V) (L : SignedRailLaw d v) :
    NativeSignedAccounting.SignedLaw where
  prob s c i := L.prob s (compileWord c) (.inl i) + L.prob s (compileWord c) (.inr i)
  normalized s c := by
    rw [Finset.sum_add_distrib]
    simpa only [Fintype.sum_sum_type] using L.normalized s (compileWord c)
  prepared_eq s c e h := by
    have hraw := RawNativeDyadicSemantics.scalar_prepared_eq_raw
      d.quotientData.zeroWeightData (d.classOf v) s c e h
    change RawNativeProbabilitySelection.rawPrepared d.quotientData.zeroWeightData
        (d.classOf v) s c =
      RawNativeProbabilitySelection.rawPrepared d.quotientData.zeroWeightData
        (d.classOf v) s e at hraw
    have hprepared : WeightFreeRawProbability.prepared d.quotientData (d.classOf v) s c =
        WeightFreeRawProbability.prepared d.quotientData (d.classOf v) s e := by
      simpa only [WeightFreeRawProbability.rawPrepared_eq_prepared] using hraw
    have hresponse :=
      (ResponseDoubledNormalizationCompiler.responseEq_iff_prepared_eq d v s c e).mpr
        hprepared
    have hp := L.prepared_eq s (compileWord c) (compileWord e) hresponse
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

theorem toNativeSignedLaw_prob (d : Data V Ω) (v : V) (L : SignedRailLaw d v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    (toNativeSignedLaw d v L).prob s c i =
      L.prob s (compileWord c) (.inl i) + L.prob s (compileWord c) (.inr i) := rfl

/-- Equal paired values follow before imposing any variation bound. -/
theorem compiled_rails_equal (d : Data V Ω) (v : V) (L : SignedRailLaw d v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s (compileWord c) (.inl i) = L.prob s (compileWord c) (.inr i) :=
  probability_eq_of_responseEq d v L s (compileWord c) (.inl i) (.inr i)
    (compiled_rails_responseEq d v s c i)

/-- Only selected actual descendants are counted, and both physical rails remain. -/
def selectedVariation (d : Data V Ω) (v : V) (L : SignedRailLaw d v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) (k : ℕ) : ℝ :=
  ∑ w : Leaf (4*k+1),
    (|L.prob (sourceAt s (4*k+1)) (compileWord (tree c i (4*k+1)))
      (.inl (leafPort i (4*k+1) w))| +
    |L.prob (sourceAt s (4*k+1)) (compileWord (tree c i (4*k+1)))
      (.inr (leafPort i (4*k+1) w))|)

/-- Paired equality identifies the physical absolute budget with native variation. -/
theorem selectedVariation_eq_native (d : Data V Ω) (v : V) (L : SignedRailLaw d v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) (k : ℕ) :
    selectedVariation d v L s c i k =
      NativeSignedVariationSelection.selectedVariation (toNativeSignedLaw d v L) s c i k := by
  apply Finset.sum_congr rfl
  intro w _
  simp only [NativeSignedVariationSelection.signedLeafProbability, toNativeSignedLaw]
  rw [compiled_rails_equal d v L (sourceAt s (4*k+1)) (tree c i (4*k+1))
    (leafPort i (4*k+1) w)]
  set a := L.prob (sourceAt s (4*k+1)) (compileWord (tree c i (4*k+1)))
    (.inr (leafPort i (4*k+1) w))
  rw [show a + a = 2*a by ring, abs_mul]
  norm_num
  ring

/-- A bound for every physical output controls the selected leaf subset. -/
theorem selectedVariation_le_global_bound (d : Data V Ω) (v : V)
    (L : SignedRailLaw d v) (C : ℝ)
    (hglobal : ∀ {α : Type} [Fintype α] [DecidableEq α]
      (s : α) (c : Native (α ⊕ α)), ∑ w, |L.prob s c w| ≤ C)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) (k : ℕ) :
    selectedVariation d v L s c i k ≤ C := by
  let f : Wire ι (4*k+1) → ℝ := fun j =>
    |L.prob (sourceAt s (4*k+1)) (compileWord (tree c i (4*k+1))) (.inl j)| +
    |L.prob (sourceAt s (4*k+1)) (compileWord (tree c i (4*k+1))) (.inr j)|
  have hsubset : (∑ w : Leaf (4*k+1), f (leafPort i (4*k+1) w)) ≤ ∑ j, f j := by
    calc
      _ = ∑ j ∈ Finset.univ.image (leafPort i (4*k+1)), f j := by
        symm
        exact Finset.sum_image (fun a _ b _ hab => leafPort_injective i (4*k+1) hab)
      _ ≤ ∑ j, f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have htotal := hglobal (sourceAt s (4*k+1)) (compileWord (tree c i (4*k+1)))
  rw [Fintype.sum_sum_type] at htotal
  exact hsubset.trans (by simpa only [f, Finset.sum_add_distrib] using htotal)

/-- The event may determine its bound; depth and added width may not. -/
def EventwiseBoundedVariation (d : Data V Ω) (v : V) (L : SignedRailLaw d v) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι),
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → selectedVariation d v L s c i k ≤ C

theorem toNativeSignedLaw_eventwiseBoundedVariation (d : Data V Ω) (v : V)
    (L : SignedRailLaw d v) (hbounded : EventwiseBoundedVariation d v L) :
    NativeSignedVariationSelection.EventwiseBoundedVariation (toNativeSignedLaw d v L) := by
  intro ι _ _ s c i
  obtain ⟨C, hC⟩ := hbounded s c i
  exact ⟨C, fun k hk => by rw [← selectedVariation_eq_native]; exact hC k hk⟩

/-- The signed paired sum is selected before either rail is made nonnegative. -/
theorem compiled_pair_probability (d : Data V Ω) (v : V) (L : SignedRailLaw d v)
    (hbounded : EventwiseBoundedVariation d v L)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s (compileWord c) (.inl i) + L.prob s (compileWord c) (.inr i) =
      Complex.normSq (c.eval (source s) i) :=
  NativeSignedVariationSelection.probability_eq_normSq_of_bounded_variation
    (toNativeSignedLaw d v L) (toNativeSignedLaw_eventwiseBoundedVariation d v L hbounded) s c i

theorem compiled_left_probability (d : Data V Ω) (v : V) (L : SignedRailLaw d v)
    (hbounded : EventwiseBoundedVariation d v L)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s (compileWord c) (.inl i) = Complex.normSq (c.eval (source s) i) / 2 := by
  have he := compiled_rails_equal d v L s c i
  have hp := compiled_pair_probability d v L hbounded s c i
  linarith

theorem compiled_right_probability (d : Data V Ω) (v : V) (L : SignedRailLaw d v)
    (hbounded : EventwiseBoundedVariation d v L)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s (compileWord c) (.inr i) = Complex.normSq (c.eval (source s) i) / 2 := by
  rw [← compiled_rails_equal d v L s c i]
  exact compiled_left_probability d v L hbounded s c i

/-- Positivity is supplied only on the logical compiled boundary after selection. -/
def toCompiledLaw (d : Data V Ω) (v : V) (L : SignedRailLaw d v)
    (hbounded : EventwiseBoundedVariation d v L) :
    ResponseDoubledNormalizationCompiler.CompiledLaw d v where
  prob := (toNativeSignedLaw d v L).prob
  nonnegative s c i := by
    change L.prob s (compileWord c) (.inl i) + L.prob s (compileWord c) (.inr i) ≥ 0
    rw [compiled_pair_probability d v L hbounded]
    exact Complex.normSq_nonneg _
  normalized := (toNativeSignedLaw d v L).normalized
  prepared_eq s c e h := by
    have hp := L.prepared_eq s (compileWord c) (compileWord e) h
    funext i
    exact congrArg₂ (· + ·) (congrFun hp (.inl i)) (congrFun hp (.inr i))
  output_perm := (toNativeSignedLaw d v L).output_perm
  spectator_pair := (toNativeSignedLaw d v L).spectator_pair
  vacuum := (toNativeSignedLaw d v L).vacuum

/-- The positive logical adapter retains the whole paired probability field. -/
theorem toCompiledLaw_entire_prob (d : Data V Ω) (v : V) (L : SignedRailLaw d v)
    (hbounded : EventwiseBoundedVariation d v L) :
    @ResponseDoubledNormalizationCompiler.CompiledLaw.prob V Ω d v
        (toCompiledLaw d v L hbounded) =
      @NativeSignedAccounting.SignedLaw.prob (toNativeSignedLaw d v L) := rfl

end
end IDT.QMClosure.SignedRawRailReadoutBridge
