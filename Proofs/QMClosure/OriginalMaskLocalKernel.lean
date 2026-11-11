import Proofs.QMClosure.OriginalOccurrenceKernel
import Mathlib.Data.Fintype.Sum

/-!
# Frozen original-mask local apparatuses

Every output has a fixed support among the original tagged occurrences. Its
total local function is evaluated only on the intersection with that support.
The output index, functions, and supports are fixed throughout every mask test.
A separate finite apparatus is permitted at every universe size.

The all-mask agreement with one supplied W produces a finite original kernel.
The converse constructs a local apparatus from any compatible kernel. These
contracts therefore characterize the same supplied readout premise.
-/

noncomputable section

namespace IDT.QMClosure.OriginalMaskLocalKernel

open scoped BigOperators
open NativeInitialHistoryPresentation
open OriginalOccurrenceKernel

attribute [local instance] presentationCommRing presentationCharZero

/-- One finite apparatus, with all fields fixed independently of the mask. -/
structure LocalApparatus (U : Type) [Fintype U] [DecidableEq U] (K : ℕ) where
  Output : Type
  finiteOutput : Fintype Output
  support : Output → Finset U
  support_le : ∀ e, (support e).card ≤ K
  localValue : Output → Finset U → ℝ

attribute [instance] LocalApparatus.finiteOutput

/-- The only mask supplied to one local function is its restricted mask. -/
def LocalApparatus.value {U : Type} [Fintype U] [DecidableEq U] {K : ℕ}
    (A : LocalApparatus U K) (S : Finset U) : ℝ :=
  ∑ e : A.Output, A.localValue e (S ∩ A.support e)

/-- Mask evaluation retains the individual original occurrences. -/
def maskEval {n m : ℕ} (S : Finset (Occurrence n m)) : Presentation :=
  bagEval S.toLeft.card S.toRight.card

@[simp] theorem maskEval_univ (n m : ℕ) :
    maskEval (Finset.univ : Finset (Occurrence n m)) = bagEval n m := by
  simp [maskEval]

/-- One and the same readout is tested on every mask of this universe. -/
def AllMaskAgreement (W : Presentation → ℝ) {n m K : ℕ}
    (A : LocalApparatus (Occurrence n m) K) : Prop :=
  ∀ S, W (maskEval S) = A.value S

/-- The order bound is uniform. Each universe may have its own apparatus. -/
def AllMaskLocalFamily (W : Presentation → ℝ) (K : ℕ) : Prop :=
  ∀ n m : ℕ, ∃ A : LocalApparatus (Occurrence n m) K, AllMaskAgreement W A

/-- Boolean Möbius coefficient on actual original subsets. -/
def mobius {U : Type} [DecidableEq U]
    (g : Finset U → ℝ) (T : Finset U) : ℝ :=
  ∑ B ∈ T.powerset, (-1 : ℝ) ^ (T.card - B.card) * g B

/-- Splitting subsets according to one original bit gives a finite difference. -/
theorem mobius_insert {U : Type} [DecidableEq U] (g : Finset U → ℝ)
    (t : U) (T : Finset U) (ht : t ∉ T) :
    mobius g (insert t T) = mobius (fun B => g (insert t B) - g B) T := by
  classical
  unfold mobius
  rw [Finset.sum_powerset_insert ht, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  have hsub : B ⊆ T := Finset.mem_powerset.mp hB
  have hcard : B.card ≤ T.card := Finset.card_le_card hsub
  have htB : t ∉ B := fun h => ht (hsub h)
  rw [Finset.card_insert_of_notMem ht, Finset.card_insert_of_notMem htB]
  have hfirst : T.card + 1 - B.card = (T.card - B.card) + 1 := by omega
  have hsecond : T.card + 1 - (B.card + 1) = T.card - B.card := by omega
  rw [hfirst, hsecond, pow_succ]
  ring

/-- Finite inversion is proved directly by insertion induction. -/
theorem mobius_inversion {U : Type} [DecidableEq U]
    (g : Finset U → ℝ) (S : Finset U) :
    (∑ T ∈ S.powerset, mobius g T) = g S := by
  classical
  induction S using Finset.induction_on generalizing g with
  | empty => simp [mobius]
  | @insert t S ht ih =>
      rw [Finset.sum_powerset_insert ht, ih g]
      have hdiff : (∑ T ∈ S.powerset, mobius g (insert t T)) =
          g (insert t S) - g S := by
        calc
          _ = ∑ T ∈ S.powerset,
              mobius (fun B => g (insert t B) - g B) T := by
            apply Finset.sum_congr rfl
            intro T hT
            apply mobius_insert
            exact fun h => ht ((Finset.mem_powerset.mp hT) h)
          _ = _ := ih (fun B => g (insert t B) - g B)
      rw [hdiff]
      ring

/-- An ignored bit pairs all subsets with their toggled partner. -/
theorem mobius_eq_zero_of_ignored {U : Type} [DecidableEq U]
    (g : Finset U → ℝ) (T : Finset U) (t : U) (ht : t ∈ T)
    (hignore : ∀ B, g (insert t B) = g B) : mobius g T = 0 := by
  classical
  calc
    mobius g T = mobius g (insert t (T.erase t)) := by
      rw [Finset.insert_erase ht]
    _ = mobius (fun B => g (insert t B) - g B) (T.erase t) :=
      mobius_insert g t (T.erase t) (by simp)
    _ = 0 := by simp [mobius, hignore]

/-- A local term has no coefficient above the cardinality of its support. -/
theorem mobius_local_eq_zero {U : Type} [DecidableEq U]
    (A T : Finset U) (f : Finset U → ℝ) (h : A.card < T.card) :
    mobius (fun S => f (S ∩ A)) T = 0 := by
  classical
  obtain ⟨t, ht⟩ := Finset.sdiff_nonempty_of_card_lt_card h
  have htT : t ∈ T := (Finset.mem_sdiff.mp ht).1
  have htA : t ∉ A := (Finset.mem_sdiff.mp ht).2
  apply mobius_eq_zero_of_ignored _ T t htT
  intro B
  have hinter : insert t B ∩ A = B ∩ A := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_insert]
    aesop
  rw [hinter]

/-- Finite summation commutes with the actual-subset coefficient. -/
theorem mobius_sum {U E : Type} [DecidableEq U] [Fintype E]
    (f : E → Finset U → ℝ) (T : Finset U) :
    mobius (fun S => ∑ e, f e S) T = ∑ e, mobius (f e) T := by
  classical
  simp only [mobius, Finset.mul_sum]
  exact Finset.sum_comm

theorem LocalApparatus.mobius_eq_zero {U : Type} [Fintype U] [DecidableEq U]
    {K : ℕ} (A : LocalApparatus U K) (T : Finset U) (hT : K < T.card) :
    mobius A.value T = 0 := by
  classical
  unfold LocalApparatus.value
  rw [mobius_sum]
  apply Finset.sum_eq_zero
  intro e he
  exact mobius_local_eq_zero (A.support e) T (A.localValue e)
    (lt_of_le_of_lt (A.support_le e) hT)

/-- Cardinal grouping of actual subsets, with no polynomial premise. -/
theorem sum_powerset_card {U : Type} [DecidableEq U]
    (T : Finset U) (f : ℕ → ℝ) :
    (∑ B ∈ T.powerset, f B.card) =
      ∑ j ∈ Finset.range (T.card + 1), (T.card.choose j : ℝ) * f j := by
  rw [Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro j hj
  simpa [nsmul_eq_mul] using Finset.sum_powersetCard j T f

/-- Every actual tagged subset is uniquely a left/right pair of subsets. -/
theorem sum_powerset_split {U V : Type} [DecidableEq U] [DecidableEq V]
    (T : Finset (U ⊕ V)) (f : Finset (U ⊕ V) → ℝ) :
    (∑ B ∈ T.powerset, f B) =
      ∑ B ∈ T.toLeft.powerset, ∑ C ∈ T.toRight.powerset, f (B.disjSum C) := by
  classical
  calc
    _ = ∑ p ∈ T.toLeft.powerset ×ˢ T.toRight.powerset,
        f (p.1.disjSum p.2) := by
      apply Finset.sum_bij (fun B _ => (B.toLeft, B.toRight))
      · intro B hB
        have hsub := Finset.mem_powerset.mp hB
        exact Finset.mem_product.mpr
          ⟨Finset.mem_powerset.mpr (Finset.toLeft_subset_toLeft hsub),
            Finset.mem_powerset.mpr (Finset.toRight_subset_toRight hsub)⟩
      · intro B hB C hC hEq
        have hleft : B.toLeft = C.toLeft := congrArg Prod.fst hEq
        have hright : B.toRight = C.toRight := congrArg Prod.snd hEq
        calc
          B = B.toLeft.disjSum B.toRight := Finset.toLeft_disjSum_toRight.symm
          _ = C.toLeft.disjSum C.toRight := by rw [hleft, hright]
          _ = C := Finset.toLeft_disjSum_toRight
      · intro p hp
        have hp' := Finset.mem_product.mp hp
        refine ⟨p.1.disjSum p.2, ?_, ?_⟩
        · apply Finset.mem_powerset.mpr
          exact Finset.disjSum_subset.mpr
            ⟨Finset.mem_powerset.mp hp'.1, Finset.mem_powerset.mp hp'.2⟩
        · simp
      · intro B hB
        rw [Finset.toLeft_disjSum_toRight]
    _ = _ := Finset.sum_product _ _ _

/-- Grouping by both type counts remains grounded in the actual powerset. -/
def cardinalSum (n m : ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
    ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * f j k

theorem sum_powerset_typecounts {U V : Type} [DecidableEq U] [DecidableEq V]
    (T : Finset (U ⊕ V)) (f : ℕ → ℕ → ℝ) :
    (∑ B ∈ T.powerset, f B.toLeft.card B.toRight.card) =
      cardinalSum T.toLeft.card T.toRight.card f := by
  classical
  rw [sum_powerset_split]
  simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum]
  calc
    _ = ∑ B ∈ T.toLeft.powerset,
        ∑ k ∈ Finset.range (T.toRight.card + 1),
          (T.toRight.card.choose k : ℝ) * f B.card k := by
      apply Finset.sum_congr rfl
      intro B hB
      exact sum_powerset_card T.toRight (f B.card)
    _ = _ := sum_powerset_card T.toLeft
      (fun j => ∑ k ∈ Finset.range (T.toRight.card + 1),
        (T.toRight.card.choose k : ℝ) * f j k)

/-- Same-W all-mask agreement supplies the universal coefficient function. -/
def countKernel (W : Presentation → ℝ) : Kernel := fun j k =>
  cardinalSum j k (fun r s =>
    (-1 : ℝ) ^ (j + k - (r + s)) * W (bagEval r s))

theorem mobius_maskEval {n m : ℕ} (W : Presentation → ℝ)
    (T : Finset (Occurrence n m)) :
    mobius (fun S => W (maskEval S)) T = countKernel W T.toLeft.card T.toRight.card := by
  classical
  calc
    _ = ∑ B ∈ T.powerset,
        (-1 : ℝ) ^ (T.card - (B.toLeft.card + B.toRight.card)) *
          W (bagEval B.toLeft.card B.toRight.card) := by
      unfold mobius
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.card_toLeft_add_card_toRight]
      rfl
    _ = cardinalSum T.toLeft.card T.toRight.card (fun r s =>
        (-1 : ℝ) ^ (T.card - (r + s)) * W (bagEval r s)) :=
      sum_powerset_typecounts T (fun r s =>
        (-1 : ℝ) ^ (T.card - (r + s)) * W (bagEval r s))
    _ = _ := by rw [← Finset.card_toLeft_add_card_toRight (u := T)]; rfl

theorem mobius_eq_countKernel {W : Presentation → ℝ} {n m K : ℕ}
    (A : LocalApparatus (Occurrence n m) K) (H : AllMaskAgreement W A)
    (T : Finset (Occurrence n m)) :
    mobius A.value T = countKernel W T.toLeft.card T.toRight.card := by
  calc
    _ = mobius (fun S => W (maskEval S)) T := by
      unfold mobius
      apply Finset.sum_congr rfl
      intro B hB
      exact congrArg (fun x : ℝ => (-1 : ℝ) ^ (T.card - B.card) * x) (H B).symm
    _ = _ := mobius_maskEval W T

/-- Uniform frozen support locality compiles to the existing subset contract. -/
theorem compatible_of_allMaskLocalFamily {W : Presentation → ℝ} {K : ℕ}
    (H : AllMaskLocalFamily W K) : CompatibleOriginalKernel W K (countKernel W) := by
  classical
  intro n m
  obtain ⟨A, hA⟩ := H n m
  calc
    W (bagEval n m) = A.value Finset.univ := by
      simpa using hA Finset.univ
    _ = ∑ T : Finset (Occurrence n m), mobius A.value T := by
      simpa using (mobius_inversion A.value Finset.univ).symm
    _ = originalSubsetCount K (countKernel W) n m := by
      unfold originalSubsetCount
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hcard : T.card ≤ K
      · simp only [hcard, if_true]
        exact mobius_eq_countKernel A hA T
      · simp only [hcard, if_false]
        exact A.mobius_eq_zero T (by omega)

/-- An inherited equality of intersections restricts to every smaller support. -/
theorem inter_eq_of_subset {U : Type} [DecidableEq U]
    {A B S T : Finset U} (hAB : A ⊆ B) (h : S ∩ B = T ∩ B) : S ∩ A = T ∩ A := by
  ext t
  have ht : (t ∈ S ∧ t ∈ B) ↔ (t ∈ T ∧ t ∈ B) := by
    simpa only [Finset.mem_inter] using
      (show t ∈ S ∩ B ↔ t ∈ T ∩ B by rw [h])
  simp only [Finset.mem_inter]
  aesop

/-- The reverse construction has one output for every actual original subset
within the supplied order cutoff. -/
def kernelApparatus (K : ℕ) (κ : Kernel) (n m : ℕ) :
    LocalApparatus (Occurrence n m) K where
  Output := {T : Finset (Occurrence n m) // T.card ≤ K}
  finiteOutput := inferInstance
  support T := T.val
  support_le T := T.property
  localValue T M := if T.val ⊆ M then κ T.val.toLeft.card T.val.toRight.card else 0

theorem kernelApparatus_value (K : ℕ) (κ : Kernel) (n m : ℕ)
    (S : Finset (Occurrence n m)) :
    (kernelApparatus K κ n m).value S =
      ∑ T ∈ S.powerset, if T.card ≤ K then κ T.toLeft.card T.toRight.card else 0 := by
  classical
  have hfilter : (Finset.univ : Finset (Finset (Occurrence n m))).filter
      (fun T => T ⊆ S) = S.powerset := by ext T; simp
  calc
    _ = ∑ T : {T : Finset (Occurrence n m) // T.card ≤ K},
        if T.val ⊆ S then κ T.val.toLeft.card T.val.toRight.card else 0 := by
      unfold LocalApparatus.value kernelApparatus
      apply Finset.sum_congr rfl
      intro T hT
      have hsub : T.val ⊆ S ∩ T.val ↔ T.val ⊆ S := by
        constructor
        · intro h t ht
          exact (Finset.mem_inter.mp (h ht)).1
        · intro h t ht
          exact Finset.mem_inter.mpr ⟨h ht, ht⟩
      simp only [hsub]
    _ = ∑ T ∈ (Finset.univ : Finset (Finset (Occurrence n m))).filter
        (fun T => T.card ≤ K),
        if T ⊆ S then κ T.toLeft.card T.toRight.card else 0 :=
      (Finset.sum_subtype _ (by intro T; simp)
        (fun T => if T ⊆ S then κ T.toLeft.card T.toRight.card else 0)).symm
    _ = ∑ T : Finset (Occurrence n m),
        if T ⊆ S then (if T.card ≤ K then κ T.toLeft.card T.toRight.card else 0)
        else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hcard : T.card ≤ K <;> by_cases hsub : T ⊆ S <;> simp [hcard, hsub]
    _ = _ := by rw [← Finset.sum_filter, hfilter]

/-- Actual-subset sums on a mask equal the sums on its canonical tagged bag. -/
theorem subset_sum_eq_originalSubsetCount (K : ℕ) (κ : Kernel) {n m : ℕ}
    (S : Finset (Occurrence n m)) :
    (∑ T ∈ S.powerset, if T.card ≤ K then κ T.toLeft.card T.toRight.card else 0) =
      originalSubsetCount K κ S.toLeft.card S.toRight.card := by
  classical
  let f : ℕ → ℕ → ℝ := fun j k => if j + k ≤ K then κ j k else 0
  have hgroup {p q : ℕ} (T : Finset (Occurrence p q)) :
      (∑ B ∈ T.powerset, if B.card ≤ K then κ B.toLeft.card B.toRight.card else 0) =
        cardinalSum T.toLeft.card T.toRight.card f := by
    calc
      _ = ∑ B ∈ T.powerset, f B.toLeft.card B.toRight.card := by
        apply Finset.sum_congr rfl
        intro B hB
        simp only [f, Finset.card_toLeft_add_card_toRight]
      _ = _ := sum_powerset_typecounts T f
  rw [hgroup S]
  have hfull := hgroup
    (Finset.univ : Finset (Occurrence S.toLeft.card S.toRight.card))
  simpa [originalSubsetCount] using hfull.symm

/-- Every compatible kernel has a frozen support-local realization on all masks. -/
theorem kernelApparatus_allMaskAgreement {W : Presentation → ℝ} {K : ℕ} {κ : Kernel}
    (H : CompatibleOriginalKernel W K κ) (n m : ℕ) :
    AllMaskAgreement W (kernelApparatus K κ n m) := by
  intro S
  rw [kernelApparatus_value, subset_sum_eq_originalSubsetCount]
  exact H S.toLeft.card S.toRight.card

/-- Operational equivalence of two additional universal readout contracts. -/
theorem allMaskLocalFamily_iff_compatible (W : Presentation → ℝ) (K : ℕ) :
    AllMaskLocalFamily W K ↔ ∃ κ : Kernel, CompatibleOriginalKernel W K κ := by
  constructor
  · intro H
    exact ⟨countKernel W, compatible_of_allMaskLocalFamily H⟩
  · rintro ⟨κ, H⟩ n m
    exact ⟨kernelApparatus K κ n m, kernelApparatus_allMaskAgreement H n m⟩

end IDT.QMClosure.OriginalMaskLocalKernel
