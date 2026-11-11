import Proofs.QMClosure.OriginalMaskLocalKernel

/-!
# Frozen principal-support event apparatuses

Each event has a fixed identity, a fixed original support and a nonnegative
fixed score. It is activated exactly when its support is contained in the mask.
Neither the number of events nor the support cardinalities have a uniform
bound across finite universes. The condition is an operational supplied
premise. It makes no claim to derive the origin of these events.
-/

noncomputable section

namespace IDT.QMClosure.PersistentOriginalEventAtoms

open scoped BigOperators
open NativeInitialHistoryPresentation
open OriginalOccurrenceKernel
open OriginalMaskLocalKernel

attribute [local instance] presentationCommRing presentationCharZero

/-- A frozen apparatus with exact principal-support activation. -/
structure EventApparatus (U : Type) [DecidableEq U] where
  Event : Type
  finiteEvent : Fintype Event
  support : Event → Finset U
  score : Event → ℝ
  score_nonnegative : ∀ e, 0 ≤ score e

attribute [instance] EventApparatus.finiteEvent

/-- All scores and identities remain fixed as the mask changes. -/
def EventApparatus.value {U : Type} [DecidableEq U]
    (A : EventApparatus U) (S : Finset U) : ℝ :=
  ∑ e : A.Event, if A.support e ⊆ S then A.score e else 0

/-- The coefficient at a support groups precisely the events with that support. -/
def EventApparatus.supportScore {U : Type} [DecidableEq U]
    (A : EventApparatus U) (T : Finset U) : ℝ :=
  ∑ e : A.Event, if A.support e = T then A.score e else 0

theorem EventApparatus.supportScore_nonnegative {U : Type} [DecidableEq U]
    (A : EventApparatus U) (T : Finset U) : 0 ≤ A.supportScore T := by
  classical
  apply Finset.sum_nonneg
  intro e he
  split_ifs
  · exact A.score_nonnegative e
  · exact le_rfl

def subsetSum {U : Type} [DecidableEq U] (c : Finset U → ℝ) (S : Finset U) : ℝ :=
  ∑ T ∈ S.powerset, c T

/-- Zeta inversion is unique on every finite principal ideal. -/
theorem subsetSum_injective {U : Type} [DecidableEq U] :
    Function.Injective (subsetSum (U := U)) := by
  classical
  intro c d h
  have hcard : ∀ N : ℕ, ∀ S : Finset U, S.card = N → c S = d S := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro S hS
        have hsum : (∑ T ∈ S.powerset, (c T - d T)) = 0 := by
          rw [Finset.sum_sub_distrib]
          exact sub_eq_zero.mpr (congrFun h S)
        rw [Finset.sum_eq_single S] at hsum
        · exact sub_eq_zero.mp hsum
        · intro T hT hne
          have hsub : T ⊆ S := Finset.mem_powerset.mp hT
          have hlt : T.card < N := by
            rw [← hS]
            exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
          rw [ih T.card hlt T rfl]
          ring
        · simp
  funext S
  exact hcard S.card S rfl

/-- Actual Boolean Möbius inversion of a support sum. -/
theorem mobius_subsetSum {U : Type} [DecidableEq U]
    (c : Finset U → ℝ) : mobius (subsetSum c) = c := by
  apply subsetSum_injective
  funext S
  exact mobius_inversion (subsetSum c) S

theorem EventApparatus.value_eq_subsetSum {U : Type} [DecidableEq U]
    (A : EventApparatus U) : A.value = subsetSum A.supportScore := by
  classical
  funext S
  unfold EventApparatus.value subsetSum EventApparatus.supportScore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hs : A.support e ⊆ S
  · rw [Finset.sum_eq_single (A.support e)]
    · simp [hs]
    · intro T hT hne
      simp [Ne.symm hne]
    · exact fun hnot => False.elim (hnot (Finset.mem_powerset.mpr hs))
  · have hnot : A.support e ∉ S.powerset := by simpa using hs
    simp only [hs, if_false]
    symm
    apply Finset.sum_eq_zero
    intro T hT
    have hne : A.support e ≠ T := by
      intro heq
      exact hnot (heq.symm ▸ hT)
    simp [hne]

/-- Exact support scores identify every canonical event coefficient. -/
theorem EventApparatus.mobius_eq_supportScore {U : Type} [DecidableEq U]
    (A : EventApparatus U) : mobius A.value = A.supportScore := by
  rw [A.value_eq_subsetSum, mobius_subsetSum]

theorem EventApparatus.mobius_nonnegative {U : Type} [DecidableEq U]
    (A : EventApparatus U) (T : Finset U) : 0 ≤ mobius A.value T := by
  rw [A.mobius_eq_supportScore]
  exact A.supportScore_nonnegative T

/-- Principal activation and nonnegative frozen scores imply mask monotonicity. -/
theorem EventApparatus.value_mono {U : Type} [DecidableEq U]
    (A : EventApparatus U) {S T : Finset U} (hST : S ⊆ T) : A.value S ≤ A.value T := by
  classical
  apply Finset.sum_le_sum
  intro e he
  by_cases hs : A.support e ⊆ S
  · have ht : A.support e ⊆ T := hs.trans hST
    simp [hs, ht]
  · simp only [hs, if_false]
    split_ifs
    · exact A.score_nonnegative e
    · exact le_rfl

/-- One supplied readout must agree on every mask, with frozen apparatus fields. -/
def EventAllMaskAgreement (W : Presentation → ℝ) {n m : ℕ}
    (A : EventApparatus (Occurrence n m)) : Prop :=
  ∀ S, W (maskEval S) = A.value S

/-- Every finite universe can have its own finite event apparatus. -/
def AllMaskEventFamily (W : Presentation → ℝ) : Prop :=
  ∀ n m : ℕ, ∃ A : EventApparatus (Occurrence n m), EventAllMaskAgreement W A

/-- Exact event activation compiles to positive canonical count coefficients. -/
theorem countKernel_nonnegative_of_allMaskEventFamily
    {W : Presentation → ℝ} (H : AllMaskEventFamily W) (j k : ℕ) :
    0 ≤ countKernel W j k := by
  classical
  obtain ⟨A, hA⟩ := H j k
  have hagree : A.value = fun S => W (maskEval S) := by
    funext S
    exact (hA S).symm
  have hpos := A.mobius_nonnegative (Finset.univ : Finset (Occurrence j k))
  rw [hagree, mobius_maskEval] at hpos
  simpa using hpos

/-- One event per original subset gives the converse under supplied positivity. -/
def canonicalEvents (W : Presentation → ℝ)
    (hpos : ∀ j k, 0 ≤ countKernel W j k) (n m : ℕ) :
    EventApparatus (Occurrence n m) where
  Event := Finset (Occurrence n m)
  finiteEvent := inferInstance
  support := id
  score := fun T => countKernel W T.toLeft.card T.toRight.card
  score_nonnegative := fun T => hpos _ _

theorem canonicalEvents_agreement (W : Presentation → ℝ)
    (hpos : ∀ j k, 0 ≤ countKernel W j k) (n m : ℕ) :
    EventAllMaskAgreement W (canonicalEvents W hpos n m) := by
  classical
  intro S
  have hinv := mobius_inversion (fun B => W (maskEval B)) S
  symm
  calc
    _ = ∑ T ∈ S.powerset, countKernel W T.toLeft.card T.toRight.card := by
      simp only [EventApparatus.value, canonicalEvents, id_eq]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext T
        simp
      · intro T hT
        rfl
    _ = ∑ T ∈ S.powerset, mobius (fun B => W (maskEval B)) T := by
      apply Finset.sum_congr rfl
      intro T hT
      exact (mobius_maskEval W T).symm
    _ = W (maskEval S) := hinv

/-- The frozen principal-support event premise is characterized operationally. -/
theorem allMaskEventFamily_iff_countKernel_nonnegative (W : Presentation → ℝ) :
    AllMaskEventFamily W ↔ ∀ j k, 0 ≤ countKernel W j k := by
  constructor
  · exact countKernel_nonnegative_of_allMaskEventFamily
  · intro hpos n m
    exact ⟨canonicalEvents W hpos n m, canonicalEvents_agreement W hpos n m⟩

/-- All-mask monotonicity follows from any such positive event apparatus. -/
theorem EventAllMaskAgreement.monotone {W : Presentation → ℝ} {n m : ℕ}
    {A : EventApparatus (Occurrence n m)} (H : EventAllMaskAgreement W A)
    {S T : Finset (Occurrence n m)} (hST : S ⊆ T) :
    W (maskEval S) ≤ W (maskEval T) := by
  rw [H S, H T]
  exact A.value_mono hST

/-- An OR-presence event persists monotonically under adding original bits. -/
def orReadout (S : Finset (Fin 2)) : ℝ := if S.Nonempty then 1 else 0

theorem orReadout_monotone {S T : Finset (Fin 2)} (hST : S ⊆ T) :
    orReadout S ≤ orReadout T := by
  by_cases hS : S.Nonempty
  · have hT := hS.mono hST
    simp [orReadout, hS, hT]
  · simp only [orReadout, hS, if_false]
    split_ifs <;> norm_num

/-- A dependency support means that only the restricted mask affects output. -/
def HasDependencySupport {U : Type} [DecidableEq U]
    (g : Finset U → ℝ) (A : Finset U) : Prop :=
  ∀ S T, S ∩ A = T ∩ A → g S = g T

/-- The OR control has one unique complete dependency footprint, both bits. -/
theorem orReadout_dependencySupport_iff (A : Finset (Fin 2)) :
    HasDependencySupport orReadout A ↔ A = Finset.univ := by
  constructor
  · intro hA
    apply Finset.eq_univ_iff_forall.mpr
    intro t
    by_contra ht
    have hint : ({t} : Finset (Fin 2)) ∩ A = ∅ ∩ A := by
      ext u
      constructor
      · intro hu
        obtain ⟨hut, huA⟩ := Finset.mem_inter.mp hu
        have heq : u = t := Finset.mem_singleton.mp hut
        subst u
        exact False.elim (ht huA)
      · simp
    have h := hA {t} ∅ hint
    norm_num [orReadout] at h
  · intro hA
    subst A
    intro S T hST
    simpa using congrArg orReadout hST

/-- Mere monotone persistence does not supply exact principal-support activation. -/
theorem orReadout_negative_pairMobius :
    mobius orReadout ({0, 1} : Finset (Fin 2)) = -1 := by
  rw [mobius_insert orReadout 0 ({1} : Finset (Fin 2)) (by decide)]
  rw [show ({1} : Finset (Fin 2)) = insert 1 ∅ by simp]
  rw [mobius_insert _ 1 (∅ : Finset (Fin 2)) (by simp)]
  norm_num [mobius, orReadout]

theorem orReadout_no_positive_eventApparatus :
    ¬∃ A : EventApparatus (Fin 2), A.value = orReadout := by
  rintro ⟨A, hA⟩
  have h := A.mobius_nonnegative ({0, 1} : Finset (Fin 2))
  rw [hA, orReadout_negative_pairMobius] at h
  norm_num at h

/-- Positive persistent events cannot carry a positive singleton into zero total
response under a larger mask. This finite obstruction applies to cancellation
whenever the larger original bag evaluates to zero under the same readout. -/
theorem cancellation_obstructs_positive_events {U : Type} [DecidableEq U]
    (g : Finset U → ℝ) {S T : Finset U} (hST : S ⊆ T)
    (hpos : 0 < g S) (hzero : g T = 0) :
    ¬∃ A : EventApparatus U, A.value = g := by
  rintro ⟨A, hA⟩
  have hmono := A.value_mono hST
  rw [hA, hzero] at hmono
  linarith

end IDT.QMClosure.PersistentOriginalEventAtoms
