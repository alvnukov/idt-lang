import Proofs.QMClosure.ReferenceOccurrenceCompilation
import Proofs.QMClosure.RawDoubledNormalizationCompiler

/-!
# An original-rail vacuum-extension obstruction

The input always has two distinct supplied source positions. A four-field
physical-rail contract is inconsistent if an original raw word sends that
input to the complete chosen-zero array. The proof uses only normalization,
same-seed whole-array consistency, output permutations, and literal raw
zero-input padding. Positivity, spectator locality and calibration are absent.
This is a conditional obstruction to a stated contract, not QM closure.
-/

namespace IDT.QMClosure.RawRailVacuumExtensionWall

noncomputable section
open NativeVacuumProbabilityFamily WeightFreeRawProbability
open scoped BigOperators

variable {V : Type*}

def twoSourceInput (z v : V) {ι : Type} [DecidableEq ι] (s t : ι) : ι → V :=
  fun i => if i = s ∨ i = t then v else z

def prepared (T : V × V → V × V) (z v : V) {ι : Type} [DecidableEq ι]
    (s t : ι) (c : Native ι) : ι → V :=
  evalRaw T c (twoSourceInput z v s t)

/-- Outcomes are physical rails, including every fresh zero-input rail. -/
structure TwoSourceLaw (T : V × V → V × V) (z v : V) where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] →
    (s t : ι) → s ≠ t → Native ι → ι → ℝ
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s t : ι) (hst : s ≠ t) (c : Native ι), ∑ i, prob s t hst c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s t : ι) (hst : s ≠ t) (c e : Native ι),
    prepared T z v s t c = prepared T z v s t e → prob s t hst c = prob s t hst e
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s t : ι) (hst : s ≠ t) (c : Native ι) (e : Equiv.Perm ι) i,
    prob s t hst (.seq c (.permute e)) i = prob s t hst c (e i)
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s t : ι) (hst : s ≠ t) (c : Native ι) i,
    prob (.inl s) (.inl t) (fun h => hst (Sum.inl.inj h))
      (padCircuit κ c) (.inl i) = prob s t hst c i

theorem prepared_pad {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (T : V × V → V × V) (z v : V) (s t : ι) (c : Native ι) :
    prepared T z v (.inl s) (.inl t) (padCircuit κ c) =
      Sum.elim (prepared T z v s t c) (fun _ => z) := by
  unfold prepared
  rw [ReferenceOccurrenceCompilation.evalRaw_padCircuit]
  simp only [Function.comp_def, twoSourceInput, Sum.inl.injEq,
    reduceCtorEq, or_self, if_false]
  rfl

/-- A constant complete output is fixed by every output permutation. -/
theorem constant_probability (T : V × V → V × V) (z v : V)
    (L : TwoSourceLaw T z v) {ι : Type} [Fintype ι] [DecidableEq ι]
    (s t : ι) (hst : s ≠ t) (c : Native ι) (a : V)
    (hc : prepared T z v s t c = fun _ => a) (i j : ι) :
    L.prob s t hst c i = L.prob s t hst c j := by
  have he : prepared T z v s t (.seq c (.permute (Equiv.swap i j))) =
      prepared T z v s t c := by
    funext k
    change prepared T z v s t c (Equiv.swap i j k) = prepared T z v s t c k
    rw [hc]
  have hs := congrFun (L.prepared_eq s t hst _ _ he) i
  have hp := L.output_perm s t hst c (Equiv.swap i j) i
  rw [Equiv.swap_apply_left] at hp
  exact hs.symm.trans hp

/-- A two-source word reaching the full chosen-zero array forbids the law.
The width grows by two; no vacuum-only input experiment is used. -/
theorem no_law_of_zero_prepared (T : V × V → V × V) (z v : V)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (s t : ι) (hst : s ≠ t) (c : Native ι)
    (hc : prepared T z v s t c = fun _ => z) :
    ¬ Nonempty (TwoSourceLaw T z v) := by
  rintro ⟨L⟩
  let α := L.prob s t hst c s
  have hold (i : ι) : L.prob s t hst c i = α :=
    constant_probability T z v L s t hst c z hc i s
  have hn := L.normalized s t hst c
  simp only [hold, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hn
  have hpad : prepared T z v (Sum.inl s : ι ⊕ Fin 2) (.inl t)
      (padCircuit (Fin 2) c) = fun _ => z := by
    rw [prepared_pad, hc]
    funext k
    cases k <;> rfl
  have hnew (i : ι ⊕ Fin 2) :
      L.prob (.inl s) (.inl t) (fun h => hst (Sum.inl.inj h))
        (padCircuit (Fin 2) c) i = α := by
    rw [constant_probability T z v L (.inl s) (.inl t)
      (fun h => hst (Sum.inl.inj h)) (padCircuit (Fin 2) c) z hpad i (.inl s)]
    exact L.vacuum s t hst c s
  have hn' := L.normalized (.inl s) (.inl t)
    (fun h => hst (Sum.inl.inj h)) (padCircuit (Fin 2) c)
  simp only [hnew, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hn'
  simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at hn'
  have ha : α = 0 := by linarith
  simp [ha] at hn

/-- The literal even-width witness is one pair on Fin 2, then padding to four. -/
theorem no_law_of_source_pair_zero (T : V × V → V × V) (z v : V)
    (h : T (v, v) = (z, z)) : ¬ Nonempty (TwoSourceLaw T z v) := by
  apply no_law_of_zero_prepared T z v (0 : Fin 2) 1 (by decide)
    (.pair 0 1 (by decide))
  funext i
  fin_cases i <;> simp [prepared, evalRaw, twoSourceInput, h]

/-- Square-swap alone makes the diagonal image of the chosen zero a two-source
extinction witness. No medial law or probability premise is used. -/
theorem diagonal_source_pair_zero_of_square (T : V × V → V × V) (z : V)
    (square : ∀ p, T (T p) = p.swap) :
    T ((T (z, z)).1, (T (z, z)).1) = (z, z) := by
  have hd : T (z, z) = ((T (z, z)).1, (T (z, z)).1) :=
    RawDoubledNormalizationCompiler.diagonal_synchronization_of_square T square z
  calc
    T ((T (z, z)).1, (T (z, z)).1) = T (T (z, z)) := congrArg T hd.symm
    _ = (z, z) := square (z, z)

/-- This excludes the law at the diagonal-image source specifically. It does
not transfer existence or nonexistence to an arbitrary selected source. -/
theorem no_law_at_diagonal_zero_source_of_square (T : V × V → V × V) (z : V)
    (square : ∀ p, T (T p) = p.swap) :
    ¬ Nonempty (TwoSourceLaw T z (T (z, z)).1) :=
  no_law_of_source_pair_zero T z (T (z, z)).1
    (diagonal_source_pair_zero_of_square T z square)

/-- Richness is an extra supplied premise: every source value distinct from
the chosen zero supports the all-width two-source physical-rail law. Under
square-swap this forces the diagonal to fix zero. A law for only one selected
source does not supply this premise; no physical availability is asserted. -/
theorem diagonal_zero_fixed_of_source_richness (T : V × V → V × V) (z : V)
    (square : ∀ p, T (T p) = p.swap)
    (richness : ∀ v, v ≠ z → Nonempty (TwoSourceLaw T z v)) :
    (T (z, z)).1 = z := by
  by_contra h
  exact no_law_at_diagonal_zero_source_of_square T z square (richness _ h)

/-- The same supplied source-richness premise fixes the complete diagonal pair. -/
theorem operation_zero_fixed_of_source_richness (T : V × V → V × V) (z : V)
    (square : ∀ p, T (T p) = p.swap)
    (richness : ∀ v, v ≠ z → Nonempty (TwoSourceLaw T z v)) :
    T (z, z) = (z, z) := by
  have hd : T (z, z) = ((T (z, z)).1, (T (z, z)).1) :=
    RawDoubledNormalizationCompiler.diagonal_synchronization_of_square T square z
  rw [diagonal_zero_fixed_of_source_richness T z square richness] at hd
  exact hd

end
end IDT.QMClosure.RawRailVacuumExtensionWall
