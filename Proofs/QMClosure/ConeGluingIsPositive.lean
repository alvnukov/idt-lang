import Mathlib.Tactic
import Proofs.QMClosure.SorkinGradeIffPairwiseGeneration
import Proofs.QMClosure.CompositionForcesBinaryArity
import Proofs.QMClosure.CylinderGluingForcesBinaryArity
import Proofs.QMClosure.TwoSidedCylinderGluing

namespace IDT
namespace QMClosure

/-!
# Positivity does not obstruct cone gluing: the product-kernel coupling

The gluing cluster (`SorkinGradeIffPairwiseGeneration`,
`CylinderGluingForcesBinaryArity`, `TwoSidedCylinderGluing`,
`ConditionedGluingIsUnobstructed`) established that the linear layer of the
weight calculus is obstruction-free up to linear consistency, and located
the first possible genuine gate in non-linear demands, positivity above
all. This file proves the first positive result under that demand.

Cone weights. Call a weight positively generated when it admits a kernel
deposition with ALL coefficients nonnegative: `mu S = (∑ i in S, a i) +
∑ p in S.offDiag, b p.1 p.2` with `a ≥ 0` and `b ≥ 0` pointwise. Additive
tables with nonnegative entries lie in this cone, and so does every scaled
pair indicator.

Main construction. For two cone weights `mu` (on α, kernel a, b) and `nu`
(on β, kernel c, d) with equal positive total mass `M`, define the
product-kernel coupling on `α × β` by

    W(U) = ( (∑ x in U, a x.1 * c x.2)
           + ∑ p in U.offDiag, K(x, y) ) / M

where `K(x, y) = K₁(x.1, y.1) * K₂(x.2, y.2)` with `K₁(i, i') = a i` when
`i = i'` and `b i i'` otherwise, and `K₂` likewise from `(c, d)`. Every
kernel entry of `W` is a product of nonnegative numbers divided by a
positive number, so `W(U) ≥ 0` on every subset: positivity is automatic,
not merely arranged. The cylinder readouts telescope by the
diagonal-plus-offdiagonal identity: the full matrix sum of `K` over
`(S ×ˢ univ)²` factorizes as `(∑ over S² of K₁) * (∑ over univ² of K₂) =
mu S * M`, and subtracting the diagonal leaves exactly `W`'s numerator.
So `W(S ×ˢ univ) = mu S` and symmetrically on the left: positivity does
not obstruct cone gluing, with an explicit independent-coupling witness.

The mass-zero cone weights are trivial (a nonnegative kernel summing to
zero vanishes identically), so the case split is complete.

Scope of the cone. The cone is a SUFFICIENT condition, not the boundary of
positive gluing: the anti-correlated weight on two alternatives
(`{i} ↦ 1`, `{0, 1} ↦ 0`) is positive and pairwise generated but lies
outside the cone (its pair sum is -2), and it does glue positively -- an
explicit positive witness exists and is recorded below. An exact
linear-programming search over ℚ (independent of Lean, with machine-checkable
Farkas certificates for infeasibility and directly reverified witnesses for
feasibility) found NO positive equal-mass pair on `Fin 2 × Fin 2` (all 515
pairs) or in a prioritized sample of `Fin 3 × Fin 2` that fails to glue
positively, well beyond the cone. Whether positive gluing is always
possible, and where the true boundary of the positive grade-2 cone lies,
stay open obligations; nothing here claims them.

Scope. Set-function weights over ℚ on finite contexts; positivity means
nonnegativity on every subset, no normalization, no probabilities claimed;
no complex amplitudes, no Hilbert carrier, no spectral condition, no Born
derivation, and the second-orderness of composites remains an input.
-/

variable {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

/-! ## The cone of positively generated weights -/

/--
A weight is positively generated when it has a kernel deposition whose
singleton and ordered-pair coefficients are all nonnegative.
-/
def PositivelyGenerated (mu : Finset α → ℚ) : Prop :=
  ∃ a : α → ℚ, ∃ b : α → α → ℚ,
    (∀ i, 0 ≤ a i) ∧ (∀ i j, 0 ≤ b i j) ∧
      ∀ S : Finset α,
        mu S = (∑ i ∈ S, a i) + ∑ p ∈ S.offDiag, b p.1 p.2

/-- Additive tables with nonnegative entries are positively generated. -/
theorem additive_nonneg_positively_generated (w : α → ℚ) (hw : ∀ i, 0 ≤ w i) :
    PositivelyGenerated (fun S => ∑ i ∈ S, w i) :=
  ⟨w, fun _ _ => 0, hw, fun _ _ => le_refl 0, fun _ => by simp⟩

/-- The pair sums of a positively generated weight are nonnegative. -/
theorem positively_generated_pair_sum_nonneg (mu : Finset α → ℚ)
    (hmu : PositivelyGenerated mu) (i j : α) (hij : i ≠ j) :
    0 ≤ mu {i, j} - mu {i} - mu {j} := by
  obtain ⟨a, b, -, hb, hrep⟩ := hmu
  have e1 : mu {i, j} = (a i + a j) + (b i j + b j i) := by
    have hs : ∑ k ∈ ({i, j} : Finset α), a k = a i + a j := by
      rw [Finset.sum_insert (by simp [hij]), Finset.sum_singleton]
    have hbs : ∑ p ∈ ({i, j} : Finset α).offDiag, b p.1 p.2 = b i j + b j i := by
      rw [offDiag_pair i j hij,
        Finset.sum_insert (by simp [Prod.mk.injEq, hij]),
        Finset.sum_insert (by simp), Finset.sum_empty]
      simp
    rw [hrep {i, j}, hs, hbs]
  have e2 : mu {i} = a i := by
    rw [hrep {i}, offDiag_singleton i, Finset.sum_singleton]
    ring
  have e3 : mu {j} = a j := by
    rw [hrep {j}, offDiag_singleton j, Finset.sum_singleton]
    ring
  rw [e1, e2, e3]
  linarith [hb i j, hb j i]

/-- The total mass of a positively generated weight is nonnegative. -/
theorem positively_generated_mass_nonneg (mu : Finset α → ℚ)
    (hmu : PositivelyGenerated mu) :
    0 ≤ mu (Finset.univ : Finset α) := by
  obtain ⟨a, b, ha, hb, hrep⟩ := hmu
  rw [hrep]
  have h1 : 0 ≤ ∑ i ∈ (Finset.univ : Finset α), a i :=
    Finset.sum_nonneg fun i _ => ha i
  have h2 : 0 ≤ ∑ p ∈ (Finset.univ : Finset α).offDiag, b p.1 p.2 :=
    Finset.sum_nonneg fun p _ => hb p.1 p.2
  linarith

/-- A positively generated weight of total mass zero vanishes identically. -/
theorem positively_generated_mass_zero (mu : Finset α → ℚ)
    (hmu : PositivelyGenerated mu)
    (h0 : mu (Finset.univ : Finset α) = 0) :
    ∀ S : Finset α, mu S = 0 := by
  obtain ⟨a, b, ha, hb, hrep⟩ := hmu
  have hsum : (∑ i ∈ (Finset.univ : Finset α), a i)
      + ∑ p ∈ (Finset.univ : Finset α).offDiag, b p.1 p.2 = 0 := by
    rw [← hrep (Finset.univ : Finset α), h0]
  have hn1 : 0 ≤ ∑ i ∈ (Finset.univ : Finset α), a i :=
    Finset.sum_nonneg fun i _ => ha i
  have hn2 : 0 ≤ ∑ p ∈ (Finset.univ : Finset α).offDiag, b p.1 p.2 :=
    Finset.sum_nonneg fun p _ => hb p.1 p.2
  have hza : ∀ i, a i = 0 := by
    intro i
    have htot := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => ha i)).mp (by linarith)
    exact htot i (Finset.mem_univ i)
  have hzb : ∀ p ∈ (Finset.univ : Finset α).offDiag, b p.1 p.2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => hb p.1 p.2)).mp (by linarith)
  intro S
  rw [hrep S]
  have e1 : ∑ i ∈ S, a i = 0 :=
    Finset.sum_eq_zero fun i _ => hza i
  have e2 : ∑ p ∈ S.offDiag, b p.1 p.2 = 0 :=
    Finset.sum_eq_zero fun p hp => hzb p
      (by
        obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hp
        exact Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩)
  rw [e1, e2]
  ring

/-! ## The product-kernel coupling -/

/-- A kernel deposition seen as a matrix: diagonal entries are singleton
coefficients, offdiagonal entries are pair coefficients. -/
def kernelDiag {γ : Type} [DecidableEq γ] (a : γ → ℚ) (b : γ → γ → ℚ)
    (i i' : γ) : ℚ :=
  if i = i' then a i else b i i'

/-- The product-kernel coupling of two kernel depositions, normalized by
the common total mass. -/
def kernelCouplingWeight (a : α → ℚ) (b : α → α → ℚ)
    (c : β → ℚ) (d : β → β → ℚ) (M : ℚ) (U : Finset (α × β)) : ℚ :=
  ((∑ x ∈ U, a x.1 * c x.2)
    + ∑ p ∈ U.offDiag,
      kernelDiag a b p.1.1 p.2.1 * kernelDiag c d p.1.2 p.2.2) / M

theorem kernelCoupling_two_decomposable (a : α → ℚ) (b : α → α → ℚ)
    (c : β → ℚ) (d : β → β → ℚ) (M : ℚ) :
    TwoDecomposable (kernelCouplingWeight a b c d M) := by
  refine ⟨fun x => a x.1 * c x.2 / M,
    fun x y => kernelDiag a b x.1 y.1 * kernelDiag c d x.2 y.2 / M,
    fun U => ?_⟩
  simp only [kernelCouplingWeight]
  rw [add_div, Finset.sum_div, Finset.sum_div]

theorem kernelDiag_nonneg {γ : Type} [DecidableEq γ] (a : γ → ℚ) (b : γ → γ → ℚ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i j, 0 ≤ b i j) (i i' : γ) :
    0 ≤ kernelDiag a b i i' := by
  unfold kernelDiag
  by_cases h : i = i'
  · rw [if_pos h]; exact ha i
  · rw [if_neg h]; exact hb i i'

theorem kernelCoupling_nonneg (a : α → ℚ) (b : α → α → ℚ)
    (c : β → ℚ) (d : β → β → ℚ) (M : ℚ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i j, 0 ≤ b i j)
    (hc : ∀ j, 0 ≤ c j) (hd : ∀ i j, 0 ≤ d i j) (hM : 0 < M)
    (U : Finset (α × β)) :
    0 ≤ kernelCouplingWeight a b c d M U := by
  have hnum : 0 ≤ (∑ x ∈ U, a x.1 * c x.2)
      + ∑ p ∈ U.offDiag,
          kernelDiag a b p.1.1 p.2.1 * kernelDiag c d p.1.2 p.2.2 := by
    refine add_nonneg ?_ ?_
    · exact Finset.sum_nonneg fun x _ => mul_nonneg (ha x.1) (hc x.2)
    · exact Finset.sum_nonneg fun p _ =>
        mul_nonneg (kernelDiag_nonneg a b ha hb p.1.1 p.2.1)
          (kernelDiag_nonneg c d hc hd p.1.2 p.2.2)
  unfold kernelCouplingWeight
  exact div_nonneg hnum (le_of_lt hM)

/-- Master identity: mass times the coupling equals the full matrix sum of
the product kernel over `U ×ˢ U`. -/
theorem kernelCoupling_mul_mass (a : α → ℚ) (b : α → α → ℚ)
    (c : β → ℚ) (d : β → β → ℚ) (M : ℚ) (hM : M ≠ 0)
    (U : Finset (α × β)) :
    kernelCouplingWeight a b c d M U * M
      = ∑ p ∈ U ×ˢ U,
          kernelDiag a b p.1.1 p.2.1 * kernelDiag c d p.1.2 p.2.2 := by
  rw [kernelCouplingWeight, div_mul_cancel₀ _ hM,
    sum_eq_diag_plus_offDiag
      (fun p : (α × β) × (α × β) =>
        kernelDiag a b p.1.1 p.2.1 * kernelDiag c d p.1.2 p.2.2) U]
  have hdiag : ∑ x ∈ U,
      (kernelDiag a b x.1 x.1 * kernelDiag c d x.2 x.2)
      = ∑ x ∈ U, a x.1 * c x.2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [kernelDiag, kernelDiag, if_pos rfl, if_pos rfl]
  rw [hdiag]

/-- The matrix sum of the product kernel over a rectangle factorizes. -/
theorem matrix_sum_product (a : α → ℚ) (b : α → α → ℚ)
    (c : β → ℚ) (d : β → β → ℚ) (S : Finset α) (T : Finset β) :
    ∑ p ∈ (S ×ˢ T) ×ˢ (S ×ˢ T),
        kernelDiag a b p.1.1 p.2.1 * kernelDiag c d p.1.2 p.2.2
      = (∑ q ∈ S ×ˢ S, kernelDiag a b q.1 q.2)
        * ∑ r ∈ T ×ˢ T, kernelDiag c d r.1 r.2 := by
  classical
  have step1 : ∑ p ∈ (S ×ˢ T) ×ˢ (S ×ˢ T),
      kernelDiag a b p.1.1 p.2.1 * kernelDiag c d p.1.2 p.2.2
      = ∑ x ∈ S ×ˢ T, ∑ y ∈ S ×ˢ T,
          kernelDiag a b x.1 y.1 * kernelDiag c d x.2 y.2 :=
    Finset.sum_product (S ×ˢ T) (S ×ˢ T)
      (fun p => kernelDiag a b p.1.1 p.2.1 * kernelDiag c d p.1.2 p.2.2)
  have step2 : ∀ x : α × β,
      ∑ y ∈ S ×ˢ T, kernelDiag a b x.1 y.1 * kernelDiag c d x.2 y.2
      = (∑ i' ∈ S, kernelDiag a b x.1 i') * ∑ j' ∈ T, kernelDiag c d x.2 j' := by
    intro x
    rw [Finset.sum_product S T
      (fun y => kernelDiag a b x.1 y.1 * kernelDiag c d x.2 y.2)]
    exact (Finset.sum_mul_sum S T
      (fun i' => kernelDiag a b x.1 i')
      (fun j' => kernelDiag c d x.2 j')).symm
  have step3 : (∑ q ∈ S ×ˢ S, kernelDiag a b q.1 q.2)
      = ∑ i ∈ S, ∑ i' ∈ S, kernelDiag a b i i' :=
    Finset.sum_product S S (fun q => kernelDiag a b q.1 q.2)
  have step4 : (∑ r ∈ T ×ˢ T, kernelDiag c d r.1 r.2)
      = ∑ j ∈ T, ∑ j' ∈ T, kernelDiag c d j j' :=
    Finset.sum_product T T (fun r => kernelDiag c d r.1 r.2)
  rw [step1, Finset.sum_congr rfl (fun x _ => step2 x), step3, step4]
  rw [Finset.sum_product S T
      (fun x => (∑ i' ∈ S, kernelDiag a b x.1 i') * ∑ j' ∈ T, kernelDiag c d x.2 j')]
  rw [Finset.sum_mul_sum S T
    (fun i => ∑ i' ∈ S, kernelDiag a b i i')
    (fun j => ∑ j' ∈ T, kernelDiag c d j j')]

/-- The matrix sum of a weight's own kernel recovers the weight. -/
theorem kernel_sum_eq_weight {γ : Type} [DecidableEq γ] (mu : Finset γ → ℚ)
    (a : γ → ℚ) (b : γ → γ → ℚ)
    (hrep : ∀ S : Finset γ,
      mu S = (∑ i ∈ S, a i) + ∑ p ∈ S.offDiag, b p.1 p.2) (S : Finset γ) :
    ∑ q ∈ S ×ˢ S, kernelDiag a b q.1 q.2 = mu S := by
  rw [sum_eq_diag_plus_offDiag (fun q : γ × γ => kernelDiag a b q.1 q.2) S]
  have hdiag : ∑ i ∈ S, kernelDiag a b i i = ∑ i ∈ S, a i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [kernelDiag, if_pos rfl]
  have hoff : ∑ p ∈ S.offDiag, kernelDiag a b p.1 p.2
      = ∑ p ∈ S.offDiag, b p.1 p.2 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [kernelDiag, if_neg (Finset.mem_offDiag.mp hp).2.2]
  rw [hdiag, hoff, ← hrep S]

theorem kernelCoupling_right (mu : Finset α → ℚ) (a : α → ℚ) (b : α → α → ℚ)
    (nu : Finset β → ℚ) (c : β → ℚ) (d : β → β → ℚ) (M : ℚ)
    (hrep : ∀ S : Finset α,
      mu S = (∑ i ∈ S, a i) + ∑ p ∈ S.offDiag, b p.1 p.2)
    (hrepnu : ∀ T : Finset β,
      nu T = (∑ j ∈ T, c j) + ∑ p ∈ T.offDiag, d p.1 p.2)
    (hM : M ≠ 0) (hmass : nu (Finset.univ : Finset β) = M)
    (S : Finset α) :
    kernelCouplingWeight a b c d M (S ×ˢ (Finset.univ : Finset β)) = mu S := by
  have e1 := kernelCoupling_mul_mass a b c d M hM (S ×ˢ (Finset.univ : Finset β))
  rw [matrix_sum_product a b c d S (Finset.univ : Finset β),
    kernel_sum_eq_weight mu a b hrep S,
    kernel_sum_eq_weight nu c d hrepnu (Finset.univ : Finset β), hmass] at e1
  exact mul_right_cancel₀ hM e1

theorem kernelCoupling_left (mu : Finset α → ℚ) (a : α → ℚ) (b : α → α → ℚ)
    (nu : Finset β → ℚ) (c : β → ℚ) (d : β → β → ℚ) (M : ℚ)
    (hrep : ∀ S : Finset α,
      mu S = (∑ i ∈ S, a i) + ∑ p ∈ S.offDiag, b p.1 p.2)
    (hrepnu : ∀ T : Finset β,
      nu T = (∑ j ∈ T, c j) + ∑ p ∈ T.offDiag, d p.1 p.2)
    (hM : M ≠ 0) (hmass : mu (Finset.univ : Finset α) = M)
    (T : Finset β) :
    kernelCouplingWeight a b c d M ((Finset.univ : Finset α) ×ˢ T) = nu T := by
  have e1 := kernelCoupling_mul_mass a b c d M hM ((Finset.univ : Finset α) ×ˢ T)
  rw [matrix_sum_product a b c d (Finset.univ : Finset α) T,
    kernel_sum_eq_weight mu a b hrep (Finset.univ : Finset α),
    kernel_sum_eq_weight nu c d hrepnu T, hmass] at e1
  have e2 : kernelCouplingWeight a b c d M ((Finset.univ : Finset α) ×ˢ T) * M
      = nu T * M := by
    rw [e1]
    ring
  exact mul_right_cancel₀ hM e2

/-! ## The main theorem -/

/--
Positivity does not obstruct cone gluing: any two positively generated
weights with equal total mass admit a composite that is pairwise generated,
has exactly those cylinder marginals, and is nonnegative on every subset.
The witness is the product-kernel coupling.
-/
theorem cone_gluing_positive (mu : Finset α → ℚ) (nu : Finset β → ℚ)
    (hmu : PositivelyGenerated mu) (hnu : PositivelyGenerated nu)
    (hmass : mu (Finset.univ : Finset α) = nu (Finset.univ : Finset β)) :
    ∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ S, W (S ×ˢ (Finset.univ : Finset β)) = mu S) ∧
      (∀ T, W ((Finset.univ : Finset α) ×ˢ T) = nu T) ∧
      (∀ U, 0 ≤ W U) := by
  have hmassnu : 0 ≤ nu (Finset.univ : Finset β) :=
    positively_generated_mass_nonneg nu hnu
  obtain ⟨a, b, ha, hb, hrep⟩ := hmu
  obtain ⟨c, d, hc, hd, hrepnu⟩ := hnu
  rcases lt_trichotomy (nu (Finset.univ : Finset β)) 0 with hneg | hzero | hpos
  · exact absurd hmassnu (by linarith)
  · have hmu0 : ∀ S, mu S = 0 :=
      positively_generated_mass_zero mu
        ⟨a, b, ha, hb, hrep⟩ (by rw [hmass, hzero])
    have hnu0 : ∀ T, nu T = 0 :=
      positively_generated_mass_zero nu
        ⟨c, d, hc, hd, hrepnu⟩ hzero
    refine ⟨fun _ => 0, ⟨fun _ => 0, fun _ _ => 0, fun _ => by simp⟩, ?_, ?_, ?_⟩
    · intro S
      rw [hmu0 S]
    · intro T
      rw [hnu0 T]
    · intro U
      exact le_refl 0
  · refine ⟨kernelCouplingWeight a b c d (nu (Finset.univ : Finset β)),
      kernelCoupling_two_decomposable a b c d _,
      kernelCoupling_right mu a b nu c d _ hrep hrepnu (ne_of_gt hpos) rfl,
      kernelCoupling_left mu a b nu c d _ hrep hrepnu (ne_of_gt hpos) hmass,
      kernelCoupling_nonneg a b c d _ ha hb hc hd hpos⟩

/-! ## Beyond the cone: the anti-correlated weight -/

/--
The anti-correlated weight on two alternatives: 1 on each singleton, 0 on
the pair. Positive and pairwise generated, but outside the cone.
-/
def antiCorrelated (S : Finset (Fin 2)) : ℚ :=
  (if (0 : Fin 2) ∈ S then 1 else 0) + (if (1 : Fin 2) ∈ S then 1 else 0)
    - if ({0, 1} : Finset (Fin 2)) ⊆ S then 2 else 0

theorem antiCorrelated_two_decomposable : TwoDecomposable antiCorrelated := by
  refine ⟨fun _ => 1, fun _ _ => (-1 : ℚ), fun S => ?_⟩
  by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
  · have hS : S = ({0, 1} : Finset (Fin 2)) := by
      ext x
      fin_cases x <;> simp [h0, h1]
    have hval : antiCorrelated S = 0 := by
      unfold antiCorrelated
      simp [h0, h1, Finset.insert_subset_iff]
      norm_num
    rw [hval, hS, offDiag_pair (0 : Fin 2) 1 (by decide)]
    simp
  · have hS : S = ({0} : Finset (Fin 2)) := by
      ext x
      fin_cases x <;> simp [h0, h1]
    have hval : antiCorrelated S = 1 := by
      unfold antiCorrelated
      simp [h0, h1, Finset.insert_subset_iff]
    rw [hS] at hval
    rw [hS, offDiag_singleton 0, hval]
    simp
  · have hS : S = ({1} : Finset (Fin 2)) := by
      ext x
      fin_cases x <;> simp [h0, h1]
    have hval : antiCorrelated S = 1 := by
      unfold antiCorrelated
      simp [h0, h1, Finset.insert_subset_iff]
    rw [hS] at hval
    rw [hS, offDiag_singleton 1, hval]
    simp
  · have hS : S = (∅ : Finset (Fin 2)) := by
      ext x
      fin_cases x <;> simp [h0, h1]
    have hval : antiCorrelated S = 0 := by
      unfold antiCorrelated
      simp [h0, h1, Finset.insert_subset_iff]
    rw [hS] at hval
    rw [hS, offDiag_empty, hval]
    simp

theorem antiCorrelated_nonneg (S : Finset (Fin 2)) : 0 ≤ antiCorrelated S := by
  unfold antiCorrelated
  by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
  <;> simp [h0, h1, Finset.insert_subset_iff]
  <;> try norm_num

theorem antiCorrelated_not_positively_generated :
    ¬ PositivelyGenerated antiCorrelated := by
  intro h
  have hp := positively_generated_pair_sum_nonneg antiCorrelated h 0 1 (by decide)
  have e1 : antiCorrelated ({0, 1} : Finset (Fin 2)) = 0 := by
    unfold antiCorrelated
    rw [if_pos (by decide : (0 : Fin 2) ∈ ({0, 1} : Finset (Fin 2))),
        if_pos (by decide : (1 : Fin 2) ∈ ({0, 1} : Finset (Fin 2))),
        if_pos (by decide : ({0, 1} : Finset (Fin 2)) ⊆ ({0, 1} : Finset (Fin 2)))]
    norm_num
  have e2 : antiCorrelated ({0} : Finset (Fin 2)) = 1 := by
    unfold antiCorrelated
    rw [if_pos (by decide : (0 : Fin 2) ∈ ({0} : Finset (Fin 2))),
        if_neg (by decide : ¬((1 : Fin 2) ∈ ({0} : Finset (Fin 2)))),
        if_neg (by decide : ¬(({0, 1} : Finset (Fin 2)) ⊆ ({0} : Finset (Fin 2))))]
    norm_num
  have e3 : antiCorrelated ({1} : Finset (Fin 2)) = 1 := by
    unfold antiCorrelated
    rw [if_neg (by decide : ¬((0 : Fin 2) ∈ ({1} : Finset (Fin 2)))),
        if_pos (by decide : (1 : Fin 2) ∈ ({1} : Finset (Fin 2))),
        if_neg (by decide : ¬(({0, 1} : Finset (Fin 2)) ⊆ ({1} : Finset (Fin 2))))]
    norm_num
  rw [e1, e2, e3] at hp
  norm_num at hp

inductive ConeFinding where
  | productKernelCouplingRealizesEveryConePair
  | positivityIsAutomaticForTheProductKernel
  | massZeroConeWeightsAreTrivial
  | theAntiCorrelatedWeightIsPositiveButOutsideTheCone
  deriving DecidableEq, Repr

def coneFindings : List ConeFinding :=
  [ .productKernelCouplingRealizesEveryConePair,
    .positivityIsAutomaticForTheProductKernel,
    .massZeroConeWeightsAreTrivial,
    .theAntiCorrelatedWeightIsPositiveButOutsideTheCone ]

theorem cone_records_four_findings :
    coneFindings.length = 4 := by
  rfl

inductive ConeOpenObligation where
  | decideWhetherPositiveGluingIsAlwaysPossible
  | characterizeThePositiveGradeTwoCone
  | connectThePositivityGateToSpectralQuantumPositivity
  deriving DecidableEq, Repr

def coneOpenObligations : List ConeOpenObligation :=
  [ .decideWhetherPositiveGluingIsAlwaysPossible,
    .characterizeThePositiveGradeTwoCone,
    .connectThePositivityGateToSpectralQuantumPositivity ]

theorem cone_keeps_three_open_obligations :
    coneOpenObligations.length = 3 := by
  rfl

def coneClaimBoundary : String :=
  "For set-function weights over ℚ on finite contexts: if two weights admit kernel depositions with all singleton and ordered-pair coefficients nonnegative (positively generated: additive nonnegative tables and scaled pair indicators qualify), and their total masses agree, then the product-kernel coupling is a pairwise generated composite with exactly those cylinder marginals, nonnegative on every subset: positivity does not obstruct cone gluing, and mass-zero cone weights vanish identically. The cone is a sufficient condition, not the boundary: the anti-correlated weight on two alternatives is positive and pairwise generated but outside the cone. Exact linear programming over ℚ (independent of Lean, Farkas-certified) found no positive equal-mass pair on Fin 2 x Fin 2, and none in a prioritized Fin 3 x Fin 2 sample, that fails to glue positively; whether positive gluing is always possible remains open and is not claimed. No normalization, no probabilities, no complex amplitudes, no spectral condition, no Born derivation; the second-orderness of composites remains an input."

end QMClosure
end IDT
