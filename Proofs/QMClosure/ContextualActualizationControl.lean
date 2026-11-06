import Mathlib

/-!
# A three-context actualization control

This is a supplied coordinate effect model, not a reconstruction of a carrier.
The symmetric coordinates are exactly the real symmetric two-by-two matrices;
`complexExpectation` verifies their quadratic forms on complex vectors explicitly.
No conversion to the continuous-operator `Effect` interface is claimed here.

Every real coefficient in [0,1] is admitted in each context. Probability descends
through equality of embedded effects, and respects arbitrary finite compatible
same-context refinements. It nevertheless fails cross-context additivity even
when the sum is an admitted effect. Thus neither operator membership nor scalar
richness is the missing condition in this control. This does not assert fixed-
preparation numerical-weight noncontextuality, physical actualization, a
no-signalling result, or closure of QM.
-/

namespace IDT.QMClosure.ContextualActualizationControl

noncomputable section

open scoped BigOperators

inductive Context where
  | zero | plus | minus
  deriving DecidableEq

@[ext] structure SymmetricCoordinates where
  d₀ : ℝ
  d₁ : ℝ
  off : ℝ

def identity : SymmetricCoordinates := ⟨1, 1, 0⟩

def add (A B : SymmetricCoordinates) : SymmetricCoordinates :=
  ⟨A.d₀ + B.d₀, A.d₁ + B.d₁, A.off + B.off⟩

def scale (t : ℝ) (A : SymmetricCoordinates) : SymmetricCoordinates :=
  ⟨t * A.d₀, t * A.d₁, t * A.off⟩

def complementCoordinates (A : SymmetricCoordinates) : SymmetricCoordinates :=
  ⟨1 - A.d₀, 1 - A.d₁, -A.off⟩

def projector : Context → SymmetricCoordinates
  | .zero => ⟨1, 0, 0⟩
  | .plus => ⟨3 / 4, 1 / 4, Real.sqrt 3 / 4⟩
  | .minus => ⟨3 / 4, 1 / 4, -Real.sqrt 3 / 4⟩

def embeddingAt (i : Context) (a b : ℝ) : SymmetricCoordinates :=
  ⟨a * (projector i).d₀ + b * (1 - (projector i).d₀),
   a * (projector i).d₁ + b * (1 - (projector i).d₁),
   (a - b) * (projector i).off⟩

def contextProbability : Context → ℝ
  | .zero => 1
  | .plus | .minus => 9 / 16

def probabilityAt (i : Context) (a b : ℝ) : ℝ :=
  a * contextProbability i + b * (1 - contextProbability i)

structure Event where
  context : Context
  a : ℝ
  b : ℝ
  a_bounds : a ∈ Set.Icc (0 : ℝ) 1
  b_bounds : b ∈ Set.Icc (0 : ℝ) 1

def embedding (e : Event) : SymmetricCoordinates := embeddingAt e.context e.a e.b
def probability (e : Event) : ℝ := probabilityAt e.context e.a e.b

def quadratic (A : SymmetricCoordinates) (x y : ℝ) : ℝ :=
  A.d₀ * x ^ 2 + 2 * A.off * x * y + A.d₁ * y ^ 2

def firstSquare : Context → ℝ → ℝ → ℝ
  | .zero, x, _ => x ^ 2
  | .plus, x, y => (Real.sqrt 3 * x + y) ^ 2 / 4
  | .minus, x, y => (Real.sqrt 3 * x - y) ^ 2 / 4

def secondSquare : Context → ℝ → ℝ → ℝ
  | .zero, _, y => y ^ 2
  | .plus, x, y => (x - Real.sqrt 3 * y) ^ 2 / 4
  | .minus, x, y => (x + Real.sqrt 3 * y) ^ 2 / 4

theorem firstSquare_nonnegative (i : Context) (x y : ℝ) :
    0 ≤ firstSquare i x y := by
  cases i <;> simp only [firstSquare] <;> positivity

theorem secondSquare_nonnegative (i : Context) (x y : ℝ) :
    0 ≤ secondSquare i x y := by
  cases i <;> simp only [secondSquare] <;> positivity

theorem squares_sum (i : Context) (x y : ℝ) :
    firstSquare i x y + secondSquare i x y = x ^ 2 + y ^ 2 := by
  cases i <;> simp only [firstSquare, secondSquare]
  all_goals ring_nf; norm_num [Real.sq_sqrt]; ring

theorem embedding_quadratic (i : Context) (a b x y : ℝ) :
    quadratic (embeddingAt i a b) x y =
      a * firstSquare i x y + b * secondSquare i x y := by
  cases i <;> simp only [quadratic, embeddingAt, projector, firstSquare, secondSquare]
  · ring
  all_goals ring_nf; norm_num [Real.sq_sqrt]; ring

/-- Universal positivity and contraction, on every real vector. -/
theorem embedding_positive_contraction (e : Event) (x y : ℝ) :
    0 ≤ quadratic (embedding e) x y ∧
      quadratic (embedding e) x y ≤ x ^ 2 + y ^ 2 := by
  rw [embedding, embedding_quadratic]
  have h₁ := firstSquare_nonnegative e.context x y
  have h₂ := secondSquare_nonnegative e.context x y
  constructor
  · exact add_nonneg (mul_nonneg e.a_bounds.1 h₁) (mul_nonneg e.b_bounds.1 h₂)
  · rw [← squares_sum e.context x y]
    exact add_le_add (mul_le_of_le_one_left h₁ e.a_bounds.2)
      (mul_le_of_le_one_left h₂ e.b_bounds.2)

/-- Actual Hermitian quadratic expression for the coordinate matrix on C². -/
def complexExpectation (A : SymmetricCoordinates) (z w : ℂ) : ℂ :=
  star z * ((A.d₀ : ℂ) * z + (A.off : ℂ) * w) +
  star w * ((A.off : ℂ) * z + (A.d₁ : ℂ) * w)

theorem complexExpectation_real (A : SymmetricCoordinates) (z w : ℂ) :
    (complexExpectation A z w).re =
      quadratic A z.re w.re + quadratic A z.im w.im := by
  simp [complexExpectation, quadratic, Complex.mul_re, Complex.mul_im]
  ring

theorem complexExpectation_imaginary (A : SymmetricCoordinates) (z w : ℂ) :
    (complexExpectation A z w).im = 0 := by
  simp [complexExpectation, Complex.mul_re, Complex.mul_im]
  ring

/-- The same bounds on all complex vectors; there is no unseen complex adapter. -/
theorem embedding_complex_positive_contraction (e : Event) (z w : ℂ) :
    0 ≤ (complexExpectation (embedding e) z w).re ∧
      (complexExpectation (embedding e) z w).re ≤
        z.re ^ 2 + w.re ^ 2 + (z.im ^ 2 + w.im ^ 2) := by
  rw [complexExpectation_real]
  exact ⟨add_nonneg (embedding_positive_contraction e z.re w.re).1
      (embedding_positive_contraction e z.im w.im).1,
    add_le_add (embedding_positive_contraction e z.re w.re).2
      (embedding_positive_contraction e z.im w.im).2⟩

theorem contextProbability_bounds (i : Context) :
    contextProbability i ∈ Set.Icc (0 : ℝ) 1 := by
  cases i <;> norm_num [contextProbability]

theorem probability_bounds (e : Event) : probability e ∈ Set.Icc (0 : ℝ) 1 := by
  have hc := contextProbability_bounds e.context
  dsimp [probability, probabilityAt]
  constructor
  · exact add_nonneg (mul_nonneg e.a_bounds.1 hc.1)
      (mul_nonneg e.b_bounds.1 (by linarith [hc.2]))
  · nlinarith [mul_nonneg (sub_nonneg.mpr e.a_bounds.2) hc.1,
      mul_nonneg (sub_nonneg.mpr e.b_bounds.2) (sub_nonneg.mpr hc.2)]

theorem diagonal_probability (i : Context) (a b : ℝ)
    (h : (embeddingAt i a b).off = 0) :
    probabilityAt i a b = (embeddingAt i a b).d₀ := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  cases i
  · simp [probabilityAt, contextProbability, embeddingAt, projector]
  · have hab : a - b = 0 := by
      have hm : (a - b) * Real.sqrt 3 = 0 := by
        dsimp [embeddingAt, projector] at h
        nlinarith [h]
      exact (mul_eq_zero.mp hm).resolve_right hs
    simp [probabilityAt, contextProbability, embeddingAt, projector]
    linarith
  · have hab : a - b = 0 := by
      have hm : (a - b) * Real.sqrt 3 = 0 := by
        dsimp [embeddingAt, projector] at h
        nlinarith [h]
      exact (mul_eq_zero.mp hm).resolve_right hs
    simp [probabilityAt, contextProbability, embeddingAt, projector]
    linarith

/-- Effect equality, including different context tags, preserves probability.
This is operator/effect noncontextuality, not numerical-weight noncontextuality. -/
theorem probability_of_embedding_eq (e f : Event) (h : embedding e = embedding f) :
    probability e = probability f := by
  have h₀ := congrArg SymmetricCoordinates.d₀ h
  have h₁ := congrArg SymmetricCoordinates.d₁ h
  change probabilityAt e.context e.a e.b = probabilityAt f.context f.a f.b
  by_cases he : e.context = .zero
  · have ho : (embedding e).off = 0 := by
      simp [embedding, embeddingAt, he, projector]
    have hf : (embedding f).off = 0 := by rw [← h]; exact ho
    rw [diagonal_probability e.context e.a e.b ho,
      diagonal_probability f.context f.a f.b hf]
    exact h₀
  by_cases hf : f.context = .zero
  · have ho : (embedding f).off = 0 := by
      simp [embedding, embeddingAt, hf, projector]
    have he' : (embedding e).off = 0 := by rw [h]; exact ho
    rw [diagonal_probability e.context e.a e.b he',
      diagonal_probability f.context f.a f.b ho]
    exact h₀
  have hp (i : Context) (hi : i ≠ .zero) (a b : ℝ) :
      probabilityAt i a b =
        (5 * (embeddingAt i a b).d₀ + 3 * (embeddingAt i a b).d₁) / 8 := by
    cases i <;> simp_all [probabilityAt, contextProbability, embeddingAt, projector]
    <;> ring
  rw [hp e.context he e.a e.b, hp f.context hf f.a f.b]
  change (5 * (embedding e).d₀ + 3 * (embedding e).d₁) / 8 =
    (5 * (embedding f).d₀ + 3 * (embedding f).d₁) / 8
  rw [h₀, h₁]

def scalarEvent (i : Context) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : Event :=
  ⟨i, t, t, ht, ht⟩

theorem scalar_embedding (i : Context) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    embedding (scalarEvent i t ht) = scale t identity := by
  ext <;> simp [embedding, scalarEvent, embeddingAt, scale, identity] <;> ring

theorem scalar_probability (i : Context) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    probability (scalarEvent i t ht) = t := by
  simp [probability, scalarEvent, probabilityAt]
  ring

theorem normalized (i : Context) :
    probability (scalarEvent i 1 (by norm_num)) = 1 := scalar_probability _ _ _

def complement (e : Event) : Event :=
  ⟨e.context, 1 - e.a, 1 - e.b,
    ⟨by linarith [e.a_bounds.2], by linarith [e.a_bounds.1]⟩,
    ⟨by linarith [e.b_bounds.2], by linarith [e.b_bounds.1]⟩⟩

theorem complement_embedding (e : Event) :
    embedding (complement e) = complementCoordinates (embedding e) := by
  ext <;> simp [embedding, complement, complementCoordinates, embeddingAt] <;> ring

theorem complement_probability (e : Event) :
    probability (complement e) = 1 - probability e := by
  simp [probability, complement, probabilityAt]
  ring

def attenuate (e : Event) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : Event :=
  ⟨e.context, t * e.a, t * e.b,
    ⟨mul_nonneg ht.1 e.a_bounds.1,
      (mul_le_of_le_one_left e.a_bounds.1 ht.2).trans e.a_bounds.2⟩,
    ⟨mul_nonneg ht.1 e.b_bounds.1,
      (mul_le_of_le_one_left e.b_bounds.1 ht.2).trans e.b_bounds.2⟩⟩

theorem attenuation_embedding (e : Event) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    embedding (attenuate e t ht) = scale t (embedding e) := by
  ext <;> simp [embedding, attenuate, embeddingAt, scale] <;> ring

theorem attenuation_probability (e : Event) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    probability (attenuate e t ht) = t * probability e := by
  simp [probability, attenuate, probabilityAt]
  ring

theorem halves (e : Event) :
    probability (attenuate e (1 / 2) (by norm_num)) = probability e / 2 := by
  rw [attenuation_probability]
  ring

/-- Any finite compatible family within a fixed context has an admitted sum. -/
def finiteMerge {α : Type*} (i : Context) (s : Finset α) (e : α → Event)
    (ha : ∑ k ∈ s, (e k).a ≤ 1) (hb : ∑ k ∈ s, (e k).b ≤ 1) : Event :=
  ⟨i, ∑ k ∈ s, (e k).a, ∑ k ∈ s, (e k).b,
    ⟨Finset.sum_nonneg (fun k _ => (e k).a_bounds.1), ha⟩,
    ⟨Finset.sum_nonneg (fun k _ => (e k).b_bounds.1), hb⟩⟩

theorem finite_same_context_probability {α : Type*} (i : Context)
    (s : Finset α) (e : α → Event) (hi : ∀ k ∈ s, (e k).context = i)
    (ha : ∑ k ∈ s, (e k).a ≤ 1) (hb : ∑ k ∈ s, (e k).b ≤ 1) :
    probability (finiteMerge i s e ha hb) = ∑ k ∈ s, probability (e k) := by
  calc
    probability (finiteMerge i s e ha hb) =
        ∑ k ∈ s, probabilityAt i (e k).a (e k).b := by
      simp [probability, probabilityAt, finiteMerge, Finset.sum_add_distrib,
        Finset.sum_mul]
    _ = ∑ k ∈ s, probability (e k) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [probability, hi k hk]

theorem finite_same_context_embedding {α : Type*} (i : Context)
    (s : Finset α) (e : α → Event) (hi : ∀ k ∈ s, (e k).context = i)
    (ha : ∑ k ∈ s, (e k).a ≤ 1) (hb : ∑ k ∈ s, (e k).b ≤ 1) :
    embedding (finiteMerge i s e ha hb) =
      ⟨∑ k ∈ s, (embedding (e k)).d₀,
       ∑ k ∈ s, (embedding (e k)).d₁,
       ∑ k ∈ s, (embedding (e k)).off⟩ := by
  ext
  · change (∑ k ∈ s, (e k).a) * (projector i).d₀ +
        (∑ k ∈ s, (e k).b) * (1 - (projector i).d₀) = _
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp [embedding, embeddingAt, hi k hk]
  · change (∑ k ∈ s, (e k).a) * (projector i).d₁ +
        (∑ k ∈ s, (e k).b) * (1 - (projector i).d₁) = _
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp [embedding, embeddingAt, hi k hk]
  · change ((∑ k ∈ s, (e k).a) - ∑ k ∈ s, (e k).b) *
        (projector i).off = _
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    simp [embedding, embeddingAt, hi k hk]

def plusHalf : Event := ⟨.plus, 1 / 2, 0, by norm_num, by norm_num⟩
def minusHalf : Event := ⟨.minus, 1 / 2, 0, by norm_num, by norm_num⟩
def remainder : Event := ⟨.zero, 1 / 4, 3 / 4, by norm_num, by norm_num⟩
def pairSum : Event := ⟨.zero, 3 / 4, 1 / 4, by norm_num, by norm_num⟩
def preparationProjector : Event := ⟨.zero, 1, 0, by norm_num, by norm_num⟩

theorem preparation_certain : probability preparationProjector = 1 := by
  norm_num [probability, preparationProjector, probabilityAt, contextProbability]

theorem cross_context_pair_is_admitted :
    add (embedding plusHalf) (embedding minusHalf) = embedding pairSum := by
  ext <;> simp [add, embedding, plusHalf, minusHalf, pairSum, embeddingAt, projector]
  <;> ring

theorem cross_context_sum_identity :
    add (add (embedding plusHalf) (embedding minusHalf)) (embedding remainder) =
      identity := by
  rw [cross_context_pair_is_admitted]
  ext <;> norm_num [add, embedding, pairSum, remainder, embeddingAt, projector, identity]

theorem cross_context_pair_failure :
    probability pairSum = 3 / 4 ∧
    probability plusHalf + probability minusHalf = 9 / 16 ∧
    probability pairSum ≠ probability plusHalf + probability minusHalf := by
  norm_num [probability, probabilityAt, contextProbability, pairSum, plusHalf, minusHalf]

theorem cross_context_normalization_failure :
    probability plusHalf + probability minusHalf + probability remainder = 13 / 16 ∧
    probability plusHalf + probability minusHalf + probability remainder ≠ 1 := by
  norm_num [probability, probabilityAt, contextProbability, remainder, plusHalf, minusHalf]

end

end IDT.QMClosure.ContextualActualizationControl
