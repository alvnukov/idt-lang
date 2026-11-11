import Proofs.QMClosure.OriginalMaskLocalKernel

/-!
# Pair coverage and original-component participation

The native consequences use calibration only on the empty mask, every
singleton, and every same-type pair. They use the native zero, singleton, and
doubled-singleton values. They require no finite kernel or norm-selection
theorem. The combinatorial coverage statements permit arbitrary real output
values and signs.

An incidence ceiling is supplied explicitly. A graph-fanout interpretation
also needs complete accounting of terminal copies/ports and control edges.
-/

noncomputable section

namespace IDT.QMClosure.OriginalMaskPairCoverage

open scoped BigOperators
open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout
open OriginalOccurrenceKernel
open OriginalMaskLocalKernel

attribute [local instance] presentationCommRing presentationCharZero

@[simp] private theorem singleton_inl_toLeft {n m : ℕ} (i : Fin n) :
    ({Sum.inl i} : Finset (Occurrence n m)).toLeft = {i} := by
  ext j
  simp

@[simp] private theorem singleton_inr_toRight {n m : ℕ} (i : Fin m) :
    ({Sum.inr i} : Finset (Occurrence n m)).toRight = {i} := by
  ext j
  simp

theorem mobius_pair {U : Type} [DecidableEq U] (g : Finset U → ℝ)
    (i j : U) (hij : i ≠ j) :
    mobius g {i, j} = g {i, j} - g {i} - g {j} + g ∅ := by
  rw [mobius_insert g i {j} (by simpa using hij)]
  have hsingle : ({j} : Finset U) = insert j ∅ := by ext t; simp
  rw [hsingle, mobius_insert (fun B => g (insert i B) - g B) j ∅ (by simp)]
  simp [mobius] <;> ring

/-- A coefficient can be nonzero only when some output covers all its bits. -/
theorem support_covers_of_mobius_ne_zero {U : Type} [Fintype U] [DecidableEq U]
    {K : ℕ} (A : LocalApparatus U K) (T : Finset U) (hT : mobius A.value T ≠ 0) :
    ∃ e, T ⊆ A.support e := by
  classical
  by_contra hcover
  push_neg at hcover
  apply hT
  unfold LocalApparatus.value
  rw [mobius_sum]
  apply Finset.sum_eq_zero
  intro e he
  have hnot := hcover e
  change ¬ ∀ t, t ∈ T → t ∈ A.support e at hnot
  push_neg at hnot
  obtain ⟨t, htT, htA⟩ := hnot
  apply mobius_eq_zero_of_ignored _ T t htT
  intro B
  have hinter : insert t B ∩ A.support e = B ∩ A.support e := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_insert]
    aesop
  rw [hinter]

/-- Arbitrary designated original pairs require enough supporting outputs. -/
theorem designated_pair_count_bound {U : Type} [Fintype U] [DecidableEq U] {K : ℕ}
    (A : LocalApparatus U K) (P : Finset (Finset U))
    (hcard : ∀ T ∈ P, T.card = 2)
    (hcoeff : ∀ T ∈ P, mobius A.value T ≠ 0) :
    P.card ≤ Fintype.card A.Output * K.choose 2 := by
  classical
  have hsub : P ⊆ Finset.univ.biUnion (fun e : A.Output => (A.support e).powersetCard 2) := by
    intro T hT
    obtain ⟨e, he⟩ := support_covers_of_mobius_ne_zero A T (hcoeff T hT)
    exact Finset.mem_biUnion.mpr
      ⟨e, Finset.mem_univ e, Finset.mem_powersetCard.mpr ⟨he, hcard T hT⟩⟩
  calc
    P.card ≤ (Finset.univ.biUnion
        (fun e : A.Output => (A.support e).powersetCard 2)).card := Finset.card_le_card hsub
    _ ≤ ∑ e : A.Output, (A.support e).card.choose 2 := by
      simpa only [Finset.card_powersetCard] using
        (Finset.card_biUnion_le (s := Finset.univ)
          (t := fun e : A.Output => (A.support e).powersetCard 2))
    _ ≤ ∑ _e : A.Output, K.choose 2 := by
      apply Finset.sum_le_sum
      intro e he
      exact Nat.choose_le_choose 2 (A.support_le e)
    _ = _ := by simp

/-- Actual same-type unordered pairs inside the given original support. -/
def sameTypePairs {n m : ℕ} (T : Finset (Occurrence n m)) :
    Finset (Finset (Occurrence n m)) :=
  (T.toLeft.powersetCard 2).image (fun s => s.disjSum (∅ : Finset (Fin m))) ∪
    (T.toRight.powersetCard 2).image (fun s => (∅ : Finset (Fin n)).disjSum s)

theorem mem_sameTypePairs {n m : ℕ} (T B : Finset (Occurrence n m)) :
    B ∈ sameTypePairs T ↔
      B ⊆ T ∧ B.card = 2 ∧ (B.toLeft = ∅ ∨ B.toRight = ∅) := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hleft | hright
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hleft
      have hs' := Finset.mem_powersetCard.mp hs
      refine ⟨Finset.disjSum_subset.mpr ⟨hs'.1, Finset.empty_subset _⟩, ?_, ?_⟩
      · simpa using hs'.2
      · exact Or.inr Finset.toRight_disjSum
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hright
      have hs' := Finset.mem_powersetCard.mp hs
      refine ⟨Finset.disjSum_subset.mpr ⟨Finset.empty_subset _, hs'.1⟩, ?_, ?_⟩
      · simpa using hs'.2
      · exact Or.inl Finset.toLeft_disjSum
  · rintro ⟨hsub, hcard, hpure⟩
    rcases hpure with hleft | hright
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨B.toRight, Finset.mem_powersetCard.mpr ⟨Finset.toRight_subset_toRight hsub, ?_⟩, ?_⟩
      · have hc := Finset.card_toLeft_add_card_toRight (u := B)
        simpa [hleft, hcard] using hc
      · simpa [hleft] using (Finset.toLeft_disjSum_toRight (u := B))
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨B.toLeft, Finset.mem_powersetCard.mpr ⟨Finset.toLeft_subset_toLeft hsub, ?_⟩, ?_⟩
      · have hc := Finset.card_toLeft_add_card_toRight (u := B)
        simpa [hright, hcard] using hc
      · simpa [hright] using (Finset.toLeft_disjSum_toRight (u := B))

theorem sameTypePairs_card {n m : ℕ} (T : Finset (Occurrence n m)) :
    (sameTypePairs T).card = T.toLeft.card.choose 2 + T.toRight.card.choose 2 := by
  classical
  have hleft : Function.Injective (fun s : Finset (Fin n) =>
      s.disjSum (∅ : Finset (Fin m))) := by
    intro s t h
    simpa only [Finset.toLeft_disjSum] using congrArg Finset.toLeft h
  have hright : Function.Injective (fun s : Finset (Fin m) =>
      (∅ : Finset (Fin n)).disjSum s) := by
    intro s t h
    simpa only [Finset.toRight_disjSum] using congrArg Finset.toRight h
  have hdisj : Disjoint
      ((T.toLeft.powersetCard 2).image (fun s => s.disjSum (∅ : Finset (Fin m))))
      ((T.toRight.powersetCard 2).image (fun s => (∅ : Finset (Fin n)).disjSum s)) := by
    apply Finset.disjoint_left.mpr
    intro B hB hC
    obtain ⟨s, hs, hsB⟩ := Finset.mem_image.mp hB
    obtain ⟨t, ht, htB⟩ := Finset.mem_image.mp hC
    have hempty : s = ∅ := by
      have h := congrArg Finset.toLeft (hsB.trans htB.symm)
      simpa only [Finset.toLeft_disjSum] using h
    have hc := (Finset.mem_powersetCard.mp hs).2
    simp [hempty] at hc
  unfold sameTypePairs
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hleft,
    Finset.card_image_of_injective _ hright,
    Finset.card_powersetCard, Finset.card_powersetCard]

/-- Exact 0/1/2-mask calibration. Mixed pairs and larger masks are absent. -/
structure LowMaskAgreement (W : Presentation → ℝ) {n m K : ℕ}
    (A : LocalApparatus (Occurrence n m) K) : Prop where
  empty : A.value ∅ = W (maskEval (n := n) (m := m) ∅)
  singleton_left : ∀ i : Fin n,
    A.value {Sum.inl i} = W (maskEval (n := n) (m := m) {Sum.inl i})
  singleton_right : ∀ i : Fin m,
    A.value {Sum.inr i} = W (maskEval (n := n) (m := m) {Sum.inr i})
  pair_left : ∀ i j : Fin n, i ≠ j →
    A.value {Sum.inl i, Sum.inl j} = W (maskEval (n := n) (m := m) {Sum.inl i, Sum.inl j})
  pair_right : ∀ i j : Fin m, i ≠ j →
    A.value {Sum.inr i, Sum.inr j} = W (maskEval (n := n) (m := m) {Sum.inr i, Sum.inr j})

theorem lowMaskAgreement_of_allMaskAgreement {W : Presentation → ℝ} {n m K : ℕ}
    (A : LocalApparatus (Occurrence n m) K) (H : AllMaskAgreement W A) : LowMaskAgreement W A := by
  constructor
  · exact (H ∅).symm
  · intro i; exact (H {Sum.inl i}).symm
  · intro i; exact (H {Sum.inr i}).symm
  · intro i j hij; exact (H {Sum.inl i, Sum.inl j}).symm
  · intro i j hij; exact (H {Sum.inr i, Sum.inr j}).symm

/-- Every order-zero frozen-support apparatus has constant mask response. -/
theorem value_eq_empty_of_zero_order {U : Type} [Fintype U] [DecidableEq U] {K : ℕ}
    (A : LocalApparatus U K) (hK : K = 0) (S : Finset U) : A.value S = A.value ∅ := by
  classical
  unfold LocalApparatus.value
  apply Finset.sum_congr rfl
  intro e he
  have hsupport : A.support e = ∅ := Finset.card_eq_zero.mp (by
    have hbound := A.support_le e
    omega)
  simp [hsupport]

/-- An existing original a singleton excludes order zero under low-mask calibration. -/
theorem native_left_order_pos {W : Presentation → ℝ} (L : NativeTransfer W)
    {n m K : ℕ} (A : LocalApparatus (Occurrence n m) K) (H : LowMaskAgreement W A)
    (i : Fin n) : 0 < K := by
  by_contra hK
  have hzero : K = 0 := by omega
  have hconstant := value_eq_empty_of_zero_order A hzero {Sum.inl i}
  rw [H.singleton_left i, H.empty] at hconstant
  norm_num [maskEval, bagEval, readout_a L, readout_zero L] at hconstant

/-- An existing original b singleton excludes order zero under low-mask calibration. -/
theorem native_right_order_pos {W : Presentation → ℝ} (L : NativeTransfer W)
    {n m K : ℕ} (A : LocalApparatus (Occurrence n m) K) (H : LowMaskAgreement W A)
    (i : Fin m) : 0 < K := by
  by_contra hK
  have hzero : K = 0 := by omega
  have hconstant := value_eq_empty_of_zero_order A hzero {Sum.inr i}
  rw [H.singleton_right i, H.empty] at hconstant
  norm_num [maskEval, bagEval, readout_b L, readout_zero L] at hconstant

theorem native_left_pair_coefficient {W : Presentation → ℝ} (L : NativeTransfer W)
    {n m K : ℕ} (A : LocalApparatus (Occurrence n m) K) (H : LowMaskAgreement W A)
    (i j : Fin n) (hij : i ≠ j) : mobius A.value {Sum.inl i, Sum.inl j} = 1 := by
  rw [mobius_pair _ _ _ (by simpa using hij), H.pair_left i j hij,
    H.singleton_left i, H.singleton_left j, H.empty]
  have hpair : maskEval ({Sum.inl i, Sum.inl j} : Finset (Occurrence n m)) =
      (2 : Presentation) * a := by simp [maskEval, bagEval, hij]
  have hsingle (k : Fin n) :
      maskEval ({Sum.inl k} : Finset (Occurrence n m)) = a := by simp [maskEval, bagEval]
  rw [hpair, hsingle, hsingle, readout_double_mul L, readout_a L]
  have hzero : maskEval (∅ : Finset (Occurrence n m)) = 0 := by simp [maskEval, bagEval]
  rw [hzero, readout_zero L]
  norm_num

theorem native_right_pair_coefficient {W : Presentation → ℝ} (L : NativeTransfer W)
    {n m K : ℕ} (A : LocalApparatus (Occurrence n m) K) (H : LowMaskAgreement W A)
    (i j : Fin m) (hij : i ≠ j) : mobius A.value {Sum.inr i, Sum.inr j} = 1 := by
  rw [mobius_pair _ _ _ (by simpa using hij), H.pair_right i j hij,
    H.singleton_right i, H.singleton_right j, H.empty]
  have hpair : maskEval ({Sum.inr i, Sum.inr j} : Finset (Occurrence n m)) =
      (2 : Presentation) * b := by simp [maskEval, bagEval, hij]
  have hsingle (k : Fin m) :
      maskEval ({Sum.inr k} : Finset (Occurrence n m)) = b := by simp [maskEval, bagEval]
  rw [hpair, hsingle, hsingle, readout_double_mul L, readout_b L]
  have hzero : maskEval (∅ : Finset (Occurrence n m)) = 0 := by simp [maskEval, bagEval]
  rw [hzero, readout_zero L]
  norm_num

theorem native_sameTypePairs_nonzero {W : Presentation → ℝ} (L : NativeTransfer W)
    {n m K : ℕ} (A : LocalApparatus (Occurrence n m) K) (H : LowMaskAgreement W A)
    (T : Finset (Occurrence n m)) (hT : T ∈ sameTypePairs Finset.univ) :
    mobius A.value T ≠ 0 := by
  classical
  rcases Finset.mem_union.mp hT with hleft | hright
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hleft
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hs).2
    have hset : ({i, j} : Finset (Fin n)).disjSum (∅ : Finset (Fin m)) =
        {Sum.inl i, Sum.inl j} := by ext t; cases t <;> simp
    rw [hset, native_left_pair_coefficient L A H i j hij]
    norm_num
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hright
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hs).2
    have hset : (∅ : Finset (Fin n)).disjSum ({i, j} : Finset (Fin m)) =
        {Sum.inr i, Sum.inr j} := by ext t; cases t <;> simp
    rw [hset, native_right_pair_coefficient L A H i j hij]
    norm_num

/-- Pair coverage supplies both the refined and uniform output-count bounds. -/
theorem native_pair_count_bounds {W : Presentation → ℝ} (L : NativeTransfer W)
    {n m K : ℕ} (A : LocalApparatus (Occurrence n m) K) (H : LowMaskAgreement W A) :
    n.choose 2 + m.choose 2 ≤
      ∑ e : A.Output, ((A.support e).toLeft.card.choose 2 + (A.support e).toRight.card.choose 2) ∧
    (∑ e : A.Output, ((A.support e).toLeft.card.choose 2 + (A.support e).toRight.card.choose 2)) ≤
      Fintype.card A.Output * K.choose 2 := by
  classical
  have hsub : sameTypePairs (Finset.univ : Finset (Occurrence n m)) ⊆
      Finset.univ.biUnion (fun e : A.Output => sameTypePairs (A.support e)) := by
    intro T hT
    obtain ⟨e, he⟩ := support_covers_of_mobius_ne_zero A T
      (native_sameTypePairs_nonzero L A H T hT)
    have ht := (mem_sameTypePairs Finset.univ T).mp hT
    exact Finset.mem_biUnion.mpr
      ⟨e, Finset.mem_univ e, (mem_sameTypePairs (A.support e) T).mpr ⟨he, ht.2⟩⟩
  constructor
  · have hc := Finset.card_le_card hsub
    calc
      n.choose 2 + m.choose 2 = (sameTypePairs (Finset.univ : Finset (Occurrence n m))).card := by
        simp [sameTypePairs_card]
      _ ≤ _ := hc
      _ ≤ _ := by simpa only [sameTypePairs_card] using
        (Finset.card_biUnion_le (s := Finset.univ)
          (t := fun e : A.Output => sameTypePairs (A.support e)))
  · calc
      _ = ∑ e : A.Output, (sameTypePairs (A.support e)).card := by simp only [sameTypePairs_card]
      _ ≤ ∑ e : A.Output, K.choose 2 := by
        apply Finset.sum_le_sum
        intro e he
        have hsub' : sameTypePairs (A.support e) ⊆ (A.support e).powersetCard 2 := by
          intro T hT
          have ht := (mem_sameTypePairs (A.support e) T).mp hT
          exact Finset.mem_powersetCard.mpr ⟨ht.1, ht.2.1⟩
        calc
          _ ≤ ((A.support e).powersetCard 2).card := Finset.card_le_card hsub'
          _ = (A.support e).card.choose 2 := Finset.card_powersetCard _ _
          _ ≤ K.choose 2 := Nat.choose_le_choose 2 (A.support_le e)
      _ = _ := by simp

/-- Count components containing the selected original input. -/
def incidenceOutputs {U E : Type} [DecidableEq U] [Fintype E]
    (support : E → Finset U) (i : U) : Finset E :=
  Finset.univ.filter (fun e => i ∈ support e)

/-- Pair coverage around one bit forces its participation in many components. -/
theorem partner_count_le_incidence_sum {U E : Type} [DecidableEq U] [Fintype E]
    (support : E → Finset U) (i : U) (partners : Finset U) (hi : i ∉ partners)
    (hcover : ∀ j ∈ partners, ∃ e, i ∈ support e ∧ j ∈ support e) :
    partners.card ≤ ∑ e ∈ incidenceOutputs support i, ((support e).card - 1) := by
  classical
  have hsub : partners ⊆ (incidenceOutputs support i).biUnion (fun e => (support e).erase i) := by
    intro j hj
    obtain ⟨e, hie, hje⟩ := hcover j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    exact Finset.mem_biUnion.mpr ⟨e, by simp [incidenceOutputs, hie],
      Finset.mem_erase.mpr ⟨hji, hje⟩⟩
  calc
    partners.card ≤ ((incidenceOutputs support i).biUnion (fun e => (support e).erase i)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ e ∈ incidenceOutputs support i, ((support e).erase i).card := Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.card_erase_of_mem (by simpa [incidenceOutputs] using he)

theorem incidence_sum_le_uniform {U E : Type} [DecidableEq U] [Fintype E]
    (support : E → Finset U) (i : U) (K : ℕ) (hK : ∀ e, (support e).card ≤ K) :
    (∑ e ∈ incidenceOutputs support i, ((support e).card - 1)) ≤
      (incidenceOutputs support i).card * (K - 1) := by
  calc
    _ ≤ ∑ _e ∈ incidenceOutputs support i, (K - 1) := by
      apply Finset.sum_le_sum
      intro e he
      have hk := hK e
      omega
    _ = _ := by simp

theorem native_left_participation {W : Presentation → ℝ} (L : NativeTransfer W)
    {n m K : ℕ} (A : LocalApparatus (Occurrence n m) K) (H : LowMaskAgreement W A)
    (i : Fin n) :
    n - 1 ≤ ∑ e ∈ incidenceOutputs (fun e => (A.support e).toLeft) i,
      ((A.support e).toLeft.card - 1) := by
  classical
  have hcover : ∀ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      ∃ e, i ∈ (A.support e).toLeft ∧ j ∈ (A.support e).toLeft := by
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hc := native_left_pair_coefficient L A H i j hji.symm
    obtain ⟨e, he⟩ := support_covers_of_mobius_ne_zero A {Sum.inl i, Sum.inl j}
      (by rw [hc]; norm_num)
    exact ⟨e, by simpa using he (by simp), by simpa using he (by simp)⟩
  simpa using partner_count_le_incidence_sum (fun e => (A.support e).toLeft) i
    ((Finset.univ : Finset (Fin n)).erase i) (by simp) hcover

theorem native_right_participation {W : Presentation → ℝ} (L : NativeTransfer W)
    {n m K : ℕ} (A : LocalApparatus (Occurrence n m) K) (H : LowMaskAgreement W A)
    (i : Fin m) :
    m - 1 ≤ ∑ e ∈ incidenceOutputs (fun e => (A.support e).toRight) i,
      ((A.support e).toRight.card - 1) := by
  classical
  have hcover : ∀ j ∈ (Finset.univ : Finset (Fin m)).erase i,
      ∃ e, i ∈ (A.support e).toRight ∧ j ∈ (A.support e).toRight := by
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hc := native_right_pair_coefficient L A H i j hji.symm
    obtain ⟨e, he⟩ := support_covers_of_mobius_ne_zero A {Sum.inr i, Sum.inr j}
      (by rw [hc]; norm_num)
    exact ⟨e, by simpa using he (by simp), by simpa using he (by simp)⟩
  simpa using partner_count_le_incidence_sum (fun e => (A.support e).toRight) i
    ((Finset.univ : Finset (Fin m)).erase i) (by simp) hcover

/-- The endpoint incidence ceiling is explicit, including every output copy. -/
theorem native_left_incidence_wall {W : Presentation → ℝ} (L : NativeTransfer W)
    {n m K : ℕ} (A : LocalApparatus (Occurrence n m) K) (H : LowMaskAgreement W A)
    (i : Fin n) (M : ℕ)
    (hM : (incidenceOutputs A.support (Sum.inl i)).card ≤ M) : n ≤ 1 + M * (K - 1) := by
  classical
  have hp := native_left_participation L A H i
  have hu := incidence_sum_le_uniform (fun e => (A.support e).toLeft) i K
    (fun e => (Finset.card_toLeft_le).trans (A.support_le e))
  have heq : incidenceOutputs (fun e => (A.support e).toLeft) i =
      incidenceOutputs A.support (Sum.inl i) := by ext e; simp [incidenceOutputs]
  rw [heq] at hp hu
  dsimp only at hu
  have hmul := Nat.mul_le_mul_right (K - 1) hM
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  omega

theorem native_right_incidence_wall {W : Presentation → ℝ} (L : NativeTransfer W)
    {n m K : ℕ} (A : LocalApparatus (Occurrence n m) K) (H : LowMaskAgreement W A)
    (i : Fin m) (M : ℕ)
    (hM : (incidenceOutputs A.support (Sum.inr i)).card ≤ M) : m ≤ 1 + M * (K - 1) := by
  classical
  have hp := native_right_participation L A H i
  have hu := incidence_sum_le_uniform (fun e => (A.support e).toRight) i K
    (fun e => (Finset.card_toRight_le).trans (A.support_le e))
  have heq : incidenceOutputs (fun e => (A.support e).toRight) i =
      incidenceOutputs A.support (Sum.inr i) := by ext e; simp [incidenceOutputs]
  rw [heq] at hp hu
  dsimp only at hu
  have hmul := Nat.mul_le_mul_right (K - 1) hM
  have hm : 0 < m := Nat.zero_lt_of_lt i.isLt
  omega

end IDT.QMClosure.OriginalMaskPairCoverage
