import Proofs.QMClosure.ContextualActualizationControl

/-!
# A generated coordinate-event cone control

This supplied coordinate model uses the nonnegative real conic span of three
projectors P_i and their three complements. Its domain consists of cone elements
whose complements also belong to the cone. The global coordinate-linear
functional below is normalized, positive on this domain, calibrated on the
first-basis-vector projector P_0, and additive on every admitted sum. Arbitrary
real classical mixing is allowed.

The domain is not saturated in the positive-semidefinite order: two admitted
effects have a positive-contraction sum outside the domain. The value 17/16 is
on that excluded mathematical sum, never a probability of an admitted outcome.
All normalized cone-valued families are supplied as an algebraic domain; no
physical generation or continuous-operator Effect adapter is asserted. This is
effect noncontextuality, not fixed-preparation numerical-weight noncontextuality,
a non-Born full quantum state, actualization, no-signalling, or QM closure.
-/

namespace IDT.QMClosure.GeneratedEventConeControl

noncomputable section

open ContextualActualizationControl
open scoped BigOperators

def zeroCoordinates : SymmetricCoordinates := ⟨0, 0, 0⟩

/-- Finite conic generation: no topological closure or PSD saturation is added. -/
inductive InCone : SymmetricCoordinates → Prop where
  | zero : InCone zeroCoordinates
  | projector (i : Context) : InCone (projector i)
  | complement (i : Context) : InCone (complementCoordinates (projector i))
  | add {A B} : InCone A → InCone B → InCone (add A B)
  | scale {A} (t : ℝ) : 0 ≤ t → InCone A → InCone (scale t A)

def InDomain (A : SymmetricCoordinates) : Prop :=
  InCone A ∧ InCone (complementCoordinates A)

def L (A : SymmetricCoordinates) : ℝ := A.d₀ + A.off / Real.sqrt 3

theorem L_add (A B : SymmetricCoordinates) : L (add A B) = L A + L B := by
  simp only [L, add]
  ring

theorem L_scale (t : ℝ) (A : SymmetricCoordinates) : L (scale t A) = t * L A := by
  simp only [L, scale]
  ring

theorem L_identity : L identity = 1 := by norm_num [L, identity]
theorem L_zero : L zeroCoordinates = 0 := by norm_num [L, zeroCoordinates]

theorem L_complement (A : SymmetricCoordinates) :
    L (complementCoordinates A) = 1 - L A := by
  simp only [L, complementCoordinates]
  ring

theorem L_projector (i : Context) :
    L (projector i) = match i with | .zero => 1 | .plus => 1 | .minus => 1 / 2 := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  cases i <;> simp [L, projector] <;> field_simp <;> ring

theorem L_projector_nonnegative (i : Context) : 0 ≤ L (projector i) := by
  rw [L_projector]
  cases i <;> norm_num

theorem L_complement_projector_nonnegative (i : Context) :
    0 ≤ L (complementCoordinates (projector i)) := by
  rw [L_complement, L_projector]
  cases i <;> norm_num

theorem cone_L_nonnegative {A : SymmetricCoordinates} (h : InCone A) : 0 ≤ L A := by
  induction h with
  | zero => rw [L_zero]
  | projector i => exact L_projector_nonnegative i
  | complement i => exact L_complement_projector_nonnegative i
  | add _ _ hA hB => rw [L_add]; exact add_nonneg hA hB
  | scale t ht _ hA => rw [L_scale]; exact mul_nonneg ht hA

theorem projector_quadratic (i : Context) (x y : ℝ) :
    quadratic (projector i) x y = firstSquare i x y := by
  have h : projector i = embeddingAt i 1 0 := by
    ext <;> simp [embeddingAt]
  rw [h, embedding_quadratic]
  ring

theorem complement_projector_quadratic (i : Context) (x y : ℝ) :
    quadratic (complementCoordinates (projector i)) x y = secondSquare i x y := by
  have h : complementCoordinates (projector i) = embeddingAt i 0 1 := by
    ext <;> simp [embeddingAt, complementCoordinates]
  rw [h, embedding_quadratic]
  ring

theorem quadratic_add (A B : SymmetricCoordinates) (x y : ℝ) :
    quadratic (add A B) x y = quadratic A x y + quadratic B x y := by
  simp only [quadratic, add]
  ring

theorem quadratic_scale (t : ℝ) (A : SymmetricCoordinates) (x y : ℝ) :
    quadratic (scale t A) x y = t * quadratic A x y := by
  simp only [quadratic, scale]
  ring

theorem quadratic_complement (A : SymmetricCoordinates) (x y : ℝ) :
    quadratic (complementCoordinates A) x y = x ^ 2 + y ^ 2 - quadratic A x y := by
  simp only [quadratic, complementCoordinates]
  ring

theorem cone_positive {A : SymmetricCoordinates} (h : InCone A) (x y : ℝ) :
    0 ≤ quadratic A x y := by
  induction h with
  | zero => norm_num [quadratic, zeroCoordinates]
  | projector i => rw [projector_quadratic]; exact firstSquare_nonnegative i x y
  | complement i =>
      rw [complement_projector_quadratic]; exact secondSquare_nonnegative i x y
  | add _ _ hA hB => rw [quadratic_add]; exact add_nonneg hA hB
  | scale t ht _ hA => rw [quadratic_scale]; exact mul_nonneg ht hA

theorem cone_complex_positive {A : SymmetricCoordinates} (h : InCone A) (z w : ℂ) :
    0 ≤ (complexExpectation A z w).re ∧ (complexExpectation A z w).im = 0 := by
  exact ⟨by rw [complexExpectation_real];
            exact add_nonneg (cone_positive h _ _) (cone_positive h _ _),
    complexExpectation_imaginary A z w⟩

theorem complement_twice (A : SymmetricCoordinates) :
    complementCoordinates (complementCoordinates A) = A := by
  ext <;> simp [complementCoordinates]

theorem identity_inCone : InCone identity := by
  have h := InCone.add (InCone.projector .zero) (InCone.complement .zero)
  convert h using 1
  ext <;> norm_num [identity, add, complementCoordinates, projector]

theorem identity_inDomain : InDomain identity := by
  refine ⟨identity_inCone, ?_⟩
  convert InCone.zero using 1
  ext <;> norm_num [complementCoordinates, identity, zeroCoordinates]

theorem projector_inDomain (i : Context) : InDomain (projector i) :=
  ⟨InCone.projector i, InCone.complement i⟩

theorem domain_complement {A : SymmetricCoordinates} (h : InDomain A) :
    InDomain (complementCoordinates A) := by
  exact ⟨h.2, by rw [complement_twice]; exact h.1⟩

/-- The original three-context events embed into the supplied generated domain. -/
theorem context_event_inDomain (e : Event) : InDomain (embedding e) := by
  have hc (i : Context) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      InCone (embeddingAt i a b) := by
    have he : embeddingAt i a b =
        add (scale a (projector i)) (scale b (complementCoordinates (projector i))) := by
      ext <;> simp [embeddingAt, add, scale, complementCoordinates]
      ring
    rw [he]
    exact InCone.add (InCone.scale a ha (InCone.projector i))
      (InCone.scale b hb (InCone.complement i))
  refine ⟨hc e.context e.a e.b e.a_bounds.1 e.b_bounds.1, ?_⟩
  rw [← complement_embedding]
  exact hc (complement e).context (complement e).a (complement e).b
    (complement e).a_bounds.1 (complement e).b_bounds.1

theorem domain_bounds {A : SymmetricCoordinates} (h : InDomain A) :
    L A ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨cone_L_nonnegative h.1, ?_⟩
  have hc := cone_L_nonnegative h.2
  rw [L_complement] at hc
  linarith

theorem domain_positive_contraction {A : SymmetricCoordinates} (h : InDomain A)
    (x y : ℝ) : 0 ≤ quadratic A x y ∧ quadratic A x y ≤ x ^ 2 + y ^ 2 := by
  refine ⟨cone_positive h.1 x y, ?_⟩
  have hc := cone_positive h.2 x y
  rw [quadratic_complement] at hc
  linarith

theorem domain_complex_positive_contraction {A : SymmetricCoordinates} (h : InDomain A)
    (z w : ℂ) :
    0 ≤ (complexExpectation A z w).re ∧
    (complexExpectation A z w).re ≤ z.re ^ 2 + w.re ^ 2 + (z.im ^ 2 + w.im ^ 2) ∧
    (complexExpectation A z w).im = 0 := by
  rw [complexExpectation_real]
  exact ⟨add_nonneg (domain_positive_contraction h _ _).1
      (domain_positive_contraction h _ _).1,
    add_le_add (domain_positive_contraction h _ _).2
      (domain_positive_contraction h _ _).2,
    complexExpectation_imaginary A z w⟩

theorem domain_attenuation {A : SymmetricCoordinates} (h : InDomain A) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : InDomain (scale t A) := by
  refine ⟨InCone.scale t ht.1 h.1, ?_⟩
  have he : complementCoordinates (scale t A) =
      add (scale t (complementCoordinates A)) (scale (1 - t) identity) := by
    ext <;> simp [complementCoordinates, scale, add, identity] <;> ring
  rw [he]
  exact InCone.add (InCone.scale t ht.1 h.2)
    (InCone.scale (1 - t) (by linarith [ht.2]) identity_inCone)

def coordinateSum {α : Type*} (s : Finset α) (f : α → SymmetricCoordinates) :
    SymmetricCoordinates := ⟨∑ i ∈ s, (f i).d₀, ∑ i ∈ s, (f i).d₁, ∑ i ∈ s, (f i).off⟩

theorem cone_sum {α : Type*} (s : Finset α) (f : α → SymmetricCoordinates)
    (h : ∀ i ∈ s, InCone (f i)) : InCone (coordinateSum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [coordinateSum, zeroCoordinates] using InCone.zero
  | @insert i s hi ih =>
      have he : coordinateSum (insert i s) f = add (f i) (coordinateSum s f) := by
        ext <;> simp [coordinateSum, add, hi]
      rw [he]
      exact InCone.add (h i (by simp)) (ih (by intro j hj; exact h j (by simp [hj])))

theorem L_sum {α : Type*} (s : Finset α) (f : α → SymmetricCoordinates) :
    L (coordinateSum s f) = ∑ i ∈ s, L (f i) := by
  simp [L, coordinateSum, Finset.sum_add_distrib, Finset.sum_div]

/-- Finite arbitrary-real convex mixtures, not merely dyadic randomization. -/
theorem domain_convex_mixture {α : Type*} (s : Finset α)
    (w : α → ℝ) (f : α → SymmetricCoordinates)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hn : ∑ i ∈ s, w i = 1)
    (hf : ∀ i ∈ s, InDomain (f i)) :
    InDomain (coordinateSum s (fun i => scale (w i) (f i))) := by
  refine ⟨cone_sum s _ (by intro i hi; exact InCone.scale _ (hw i hi) (hf i hi).1), ?_⟩
  have he : complementCoordinates (coordinateSum s (fun i => scale (w i) (f i))) =
      coordinateSum s (fun i => scale (w i) (complementCoordinates (f i))) := by
    ext <;> simp [coordinateSum, complementCoordinates, scale, mul_sub,
      Finset.sum_sub_distrib, hn, Finset.sum_neg_distrib]
  rw [he]
  exact cone_sum s _ (by intro i hi; exact InCone.scale _ (hw i hi) (hf i hi).2)

theorem sum_erase_add {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → SymmetricCoordinates) (i : α) (hi : i ∈ s) :
    add (f i) (coordinateSum (s.erase i) f) = coordinateSum s f := by
  ext <;> simp only [add, coordinateSum]
  · simpa [add_comm] using Finset.sum_erase_add s (fun j => (f j).d₀) hi
  · simpa [add_comm] using Finset.sum_erase_add s (fun j => (f j).d₁) hi
  · simpa [add_comm] using Finset.sum_erase_add s (fun j => (f j).off) hi

/-- Every supplied finite normalized cone-valued family already has domain-valued outcomes. -/
theorem normalized_family_inDomain {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → SymmetricCoordinates) (hf : ∀ i ∈ s, InCone (f i))
    (hn : coordinateSum s f = identity) (i : α) (hi : i ∈ s) : InDomain (f i) := by
  refine ⟨hf i hi, ?_⟩
  have he := (sum_erase_add s f i hi).trans hn
  have hc : complementCoordinates (f i) = coordinateSum (s.erase i) f := by
    have h₀ := congrArg SymmetricCoordinates.d₀ he
    have h₁ := congrArg SymmetricCoordinates.d₁ he
    have ho := congrArg SymmetricCoordinates.off he
    ext <;> simp_all [add, identity, complementCoordinates] <;> linarith
  rw [hc]
  exact cone_sum _ _ (by intro j hj; exact hf j (Finset.mem_of_mem_erase hj))

theorem normalized_family_accounting {α : Type*} (s : Finset α)
    (f : α → SymmetricCoordinates) (hn : coordinateSum s f = identity) :
    ∑ i ∈ s, L (f i) = 1 := by
  rw [← L_sum, hn, L_identity]

/-- Equality of coordinates gives equality of assigned values, without a context tag. -/
theorem effect_noncontextual (A B : SymmetricCoordinates) (h : A = B) : L A = L B :=
  congrArg L h

theorem admitted_sum_additive (A B : SymmetricCoordinates)
    (_hA : InDomain A) (_hB : InDomain B) (_hs : InDomain (add A B)) :
    L (add A B) = L A + L B := L_add A B

theorem calibration : L (projector .zero) = 1 := by rw [L_projector]

theorem disagreement_with_first_basis_vector_expectation :
    L (projector .plus) = 1 ∧ quadratic (projector .plus) 1 0 = 3 / 4 := by
  constructor
  · rw [L_projector]
  · norm_num [quadratic, projector]

def A : SymmetricCoordinates := scale (1 / 16) identity
def B : SymmetricCoordinates := scale (1 / 2) (add (projector .zero) (projector .plus))
def S : SymmetricCoordinates := add A B
def T : SymmetricCoordinates := ⟨1 / 16, 13 / 16, -Real.sqrt 3 / 8⟩

theorem A_inDomain : InDomain A := domain_attenuation identity_inDomain _ (by norm_num)

theorem B_inDomain : InDomain B := by
  have h := domain_convex_mixture (Finset.univ : Finset (Fin 2)) (fun _ => (1 / 2 : ℝ))
    (fun i => if i = 0 then projector .zero else projector .plus)
    (by intro i hi; norm_num) (by norm_num)
    (by intro i hi; dsimp only; split_ifs <;> exact projector_inDomain _)
  convert h using 1
  ext <;> norm_num [B, coordinateSum, scale, add, Fin.sum_univ_two] <;> ring

theorem S_complement : complementCoordinates S = T := by
  ext <;> norm_num [S, A, B, T, complementCoordinates, scale, add, identity, projector]
  ring

theorem T_quadratic (x y : ℝ) :
    quadratic T x y = ((x - 2 * Real.sqrt 3 * y) ^ 2 + y ^ 2) / 16 := by
  simp only [quadratic, T]
  ring_nf
  norm_num [Real.sq_sqrt]
  ring

theorem T_positive (x y : ℝ) : 0 ≤ quadratic T x y := by
  rw [T_quadratic]
  positivity

theorem S_inCone : InCone S := InCone.add A_inDomain.1 B_inDomain.1

/-- A genuine positive-contraction sum, universally on real vectors. -/
theorem S_positive_contraction (x y : ℝ) :
    0 ≤ quadratic S x y ∧ quadratic S x y ≤ x ^ 2 + y ^ 2 := by
  refine ⟨cone_positive S_inCone x y, ?_⟩
  have h := T_positive x y
  rw [← S_complement, quadratic_complement] at h
  linarith

/-- The same excluded mathematical sum is checked on every complex vector. -/
theorem S_complex_positive_contraction (z w : ℂ) :
    0 ≤ (complexExpectation S z w).re ∧
    (complexExpectation S z w).re ≤ z.re ^ 2 + w.re ^ 2 + (z.im ^ 2 + w.im ^ 2) ∧
    (complexExpectation S z w).im = 0 := by
  rw [complexExpectation_real]
  exact ⟨add_nonneg (S_positive_contraction _ _).1 (S_positive_contraction _ _).1,
    add_le_add (S_positive_contraction _ _).2 (S_positive_contraction _ _).2,
    complexExpectation_imaginary S z w⟩

theorem L_S : L S = 17 / 16 := by
  rw [S, L_add, A, L_scale, L_identity, B, L_scale, L_add,
    L_projector, L_projector]
  norm_num

theorem L_T : L T = -1 / 16 := by
  rw [← S_complement, L_complement, L_S]
  norm_num

theorem T_not_inCone : ¬ InCone T := by
  intro h
  have hp := cone_L_nonnegative h
  rw [L_T] at hp
  norm_num at hp

theorem S_not_inDomain : ¬ InDomain S := by
  intro h
  exact T_not_inCone (S_complement ▸ h.2)

/-- Mixing closure and all admitted-sum additivity do not imply PSD-order closure. -/
theorem absent_sum_control :
    InDomain A ∧ InDomain B ∧ InCone S ∧ ¬ InDomain S ∧ L S = 17 / 16 :=
  ⟨A_inDomain, B_inDomain, S_inCone, S_not_inDomain, L_S⟩

end

end IDT.QMClosure.GeneratedEventConeControl
