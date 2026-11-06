import Mathlib

namespace IDT.QMClosure.RestrictedActualizationControls

noncomputable section

/-!
# Fixed-preparation actualization control on rational-coordinate events

This supplied event algebra has the coordinates of rational diagonal two-port
effects. No physical event adapter, operator-algebra reconstruction, universal
preparation-independent scalar response, or no-signalling result is asserted.

For one fixed irrational preparation parameter `t`, its weight map is injective.
Consequently a different numeric probability assignment respects equal weights,
normalization, positivity, every available finite partial sum, and every rational
scalar calibration, without agreeing with the preparation weights. Numerical
density of calibrated scalar weights does not supply cross-weight order or
missing common refinements. This is a restricted-event countermodel only; it
does not upgrade any IDT, Born-rule, or full-QM closure claim.
-/

/-- Supplied event coordinates, with both rational entries in the unit interval. -/
def EffectCoords :=
  {ab : ℚ × ℚ // 0 ≤ ab.1 ∧ ab.1 ≤ 1 ∧ 0 ≤ ab.2 ∧ ab.2 ≤ 1}

def first (e : EffectCoords) : ℚ := e.val.1
def second (e : EffectCoords) : ℚ := e.val.2

def zero : EffectCoords := ⟨(0, 0), by norm_num⟩
def identity : EffectCoords := ⟨(1, 1), by norm_num⟩
def portZero : EffectCoords := ⟨(1, 0), by norm_num⟩

/-- A scalar event is available for every rational scalar in `[0,1]`. -/
def scalar (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : EffectCoords :=
  ⟨(q, q), h0, h1, h0, h1⟩

def complement (e : EffectCoords) : EffectCoords :=
  ⟨(1 - first e, 1 - second e), by
    have h := e.property
    dsimp [first, second]
    constructor
    · linarith [h.2.1]
    constructor
    · linarith [h.1]
    constructor
    · linarith [h.2.2.2]
    · linarith [h.2.2.1]⟩

/-- Exactly the componentwise upper-bound contract for a partial sum. -/
def Compatible (e f : EffectCoords) : Prop :=
  first e + first f ≤ 1 ∧ second e + second f ≤ 1

def merge (e f : EffectCoords) (h : Compatible e f) : EffectCoords :=
  ⟨(first e + first f, second e + second f),
    add_nonneg e.property.1 f.property.1, h.1,
    add_nonneg e.property.2.2.1 f.property.2.2.1, h.2⟩

def FiniteCompatible {ι : Type*} [Fintype ι] (events : ι → EffectCoords) : Prop :=
  (∑ i, first (events i)) ≤ 1 ∧ (∑ i, second (events i)) ≤ 1

/-- Every finite componentwise-bounded refinement has its actual coordinate sum. -/
def mergeFinite {ι : Type*} [Fintype ι] (events : ι → EffectCoords)
    (h : FiniteCompatible events) : EffectCoords :=
  ⟨(∑ i, first (events i), ∑ i, second (events i)),
    Finset.sum_nonneg (fun i _ => (events i).property.1), h.1,
    Finset.sum_nonneg (fun i _ => (events i).property.2.2.1), h.2⟩

/-- Rational attenuation stays inside the supplied event algebra. -/
def refine (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (e : EffectCoords) : EffectCoords :=
  ⟨(q * first e, q * second e), by
    have h := e.property
    refine ⟨mul_nonneg h0 h.1, ?_, mul_nonneg h0 h.2.2.1, ?_⟩
    · exact le_trans (mul_le_mul_of_nonneg_left h.2.1 h0) (by simpa using h1)
    · exact le_trans (mul_le_mul_of_nonneg_left h.2.2.2 h0) (by simpa using h1)⟩

def weight (t : ℝ) (e : EffectCoords) : ℝ :=
  (first e : ℝ) * t + (second e : ℝ) * (1 - t)

/-- An explicit alternative assignment, not inferred empirical event semantics. -/
def probability (e : EffectCoords) : ℝ := weight (1 / 2) e

theorem weight_bounds (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (e : EffectCoords) :
    0 ≤ weight t e ∧ weight t e ≤ 1 := by
  have ha0 : 0 ≤ (first e : ℝ) := by exact_mod_cast e.property.1
  have ha1 : (first e : ℝ) ≤ 1 := by exact_mod_cast e.property.2.1
  have hb0 : 0 ≤ (second e : ℝ) := by exact_mod_cast e.property.2.2.1
  have hb1 : (second e : ℝ) ≤ 1 := by exact_mod_cast e.property.2.2.2
  have ht : 0 ≤ 1 - t := sub_nonneg.mpr h1
  constructor
  · exact add_nonneg (mul_nonneg ha0 h0) (mul_nonneg hb0 ht)
  · have ha := mul_le_mul_of_nonneg_right ha1 h0
    have hb := mul_le_mul_of_nonneg_right hb1 ht
    dsimp [weight]
    nlinarith

theorem probability_bounds (e : EffectCoords) :
    0 ≤ probability e ∧ probability e ≤ 1 :=
  weight_bounds (1 / 2) (by norm_num) (by norm_num) e

@[simp] theorem weight_zero (t : ℝ) : weight t zero = 0 := by
  simp [weight, zero, first, second]

@[simp] theorem weight_identity (t : ℝ) : weight t identity = 1 := by
  simp [weight, identity, first, second]

@[simp] theorem weight_portZero (t : ℝ) : weight t portZero = t := by
  simp [weight, portZero, first, second]

theorem weight_complement (t : ℝ) (e : EffectCoords) :
    weight t (complement e) = 1 - weight t e := by
  dsimp [weight, complement, first, second]
  push_cast
  ring

theorem weight_merge (t : ℝ) (e f : EffectCoords) (h : Compatible e f) :
    weight t (merge e f h) = weight t e + weight t f := by
  dsimp [weight, merge, first, second]
  push_cast
  ring

theorem weight_mergeFinite (t : ℝ) {ι : Type*} [Fintype ι]
    (events : ι → EffectCoords) (h : FiniteCompatible events) :
    weight t (mergeFinite events h) = ∑ i, weight t (events i) := by
  simp [weight, mergeFinite, first, second, Finset.sum_add_distrib, Finset.sum_mul]

theorem weight_refine (t : ℝ) (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (e : EffectCoords) :
    weight t (refine q h0 h1 e) = (q : ℝ) * weight t e := by
  dsimp [weight, refine, first, second]
  push_cast
  ring

theorem rational_scalar_calibration (t : ℝ) (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    weight t (scalar q h0 h1) = q ∧ probability (scalar q h0 h1) = q := by
  constructor <;> dsimp [probability, weight, scalar, first, second] <;> ring

theorem probability_accounting :
    probability zero = 0 ∧ probability identity = 1 ∧
    (∀ e, probability (complement e) = 1 - probability e) ∧
    (∀ e f (h : Compatible e f),
      probability (merge e f h) = probability e + probability f) := by
  exact ⟨weight_zero _, weight_identity _, weight_complement _, weight_merge _⟩

theorem probability_finite_accounting {ι : Type*} [Fintype ι]
    (events : ι → EffectCoords) (h : FiniteCompatible events) :
    probability (mergeFinite events h) = ∑ i, probability (events i) :=
  weight_mergeFinite _ events h

/-- A complete finite event refinement is normalized by its coordinate sums. -/
theorem complete_refinement_normalization {ι : Type*} [Fintype ι]
    (events : ι → EffectCoords)
    (ha : ∑ i, first (events i) = 1) (hb : ∑ i, second (events i) = 1)
    (t : ℝ) :
    (∑ i, weight t (events i)) = 1 ∧ (∑ i, probability (events i)) = 1 := by
  have h : FiniteCompatible events := ⟨ha.le, hb.le⟩
  have he : mergeFinite events h = identity := by
    apply Subtype.ext
    exact Prod.ext ha hb
  constructor
  · rw [← weight_mergeFinite t events h, he, weight_identity]
  · rw [← probability_finite_accounting events h, he]
    exact probability_accounting.2.1

theorem probability_rational_refinement (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (e : EffectCoords) :
    probability (refine q h0 h1 e) = (q : ℝ) * probability e :=
  weight_refine _ q h0 h1 e

/-- Irrationality makes weight equality on rational pairs rigid. This theorem
is for one preparation, not one response shared across all preparations. -/
theorem irrational_weight_injective (t : ℝ) (ht : Irrational t) :
    Function.Injective (weight t) := by
  intro e f hw
  have hcoeff : first e - second e = first f - second f := by
    by_contra h
    have hc : first e - second e - (first f - second f) ≠ 0 := sub_ne_zero.mpr h
    apply (ht.ratCast_mul hc).ne_rat (second f - second e)
    push_cast
    dsimp [weight] at hw
    nlinarith [hw]
  have hcr : (first e : ℝ) - (second e : ℝ) =
      (first f : ℝ) - (second f : ℝ) := by exact_mod_cast hcoeff
  have hbr : (second e : ℝ) = (second f : ℝ) := by
    have hmult := congrArg (fun x : ℝ => x * t) hcr
    dsimp [weight] at hw
    nlinarith [hw, hmult]
  have hb : second e = second f := by exact_mod_cast hbr
  have ha : first e = first f := by linarith [hcoeff]
  apply Subtype.ext
  exact Prod.ext ha hb

/-- The image of this particular rational event algebra is not closed under
the inverse of rational halving at the first port weight. Restricted domains
with the appropriate inverse-branch closure can still support rigidity. -/
theorem no_event_weight_twice_preparation (t : ℝ) (ht : Irrational t) :
    ¬ ∃ e : EffectCoords, weight t e = 2 * t := by
  rintro ⟨e, he⟩
  have hw : weight t (refine (1 / 2) (by norm_num) (by norm_num) e) =
      weight t portZero := by
    rw [weight_refine, he, weight_portZero]
    ring
  have hcoords := congrArg first (irrational_weight_injective t ht hw)
  change (1 / 2 : ℚ) * first e = 1 at hcoords
  have hbound : first e ≤ 1 := e.property.2.1
  linarith

/-- The complementary inverse branch is absent as well, even when its target
weight lies in the numerical unit interval. This is an event-image obstruction,
not a claim that all restricted scalar domains are insufficient. -/
theorem no_event_weight_twice_complement (t : ℝ) (ht : Irrational t) :
    ¬ ∃ e : EffectCoords, weight t e = 2 * (1 - t) := by
  rintro ⟨e, he⟩
  have hw : weight t (refine (1 / 2) (by norm_num) (by norm_num) e) =
      weight t (complement portZero) := by
    rw [weight_refine, he, weight_complement, weight_portZero]
    ring
  have hcoords := congrArg second (irrational_weight_injective t ht hw)
  change (1 / 2 : ℚ) * second e = 1 - 0 at hcoords
  have hbound : second e ≤ 1 := e.property.2.2.2
  linarith

theorem fixed_preparation_weight_noncontextual (t : ℝ) (ht : Irrational t)
    (e f : EffectCoords) (h : weight t e = weight t f) :
    probability e = probability f :=
  congrArg probability (irrational_weight_injective t ht h)

theorem alternative_disagrees (t : ℝ) (ht : Irrational t) :
    probability portZero ≠ weight t portZero := by
  simp only [probability, weight_portZero]
  exact fun h => ht.ne_rat (1 / 2) (by norm_num at h ⊢; exact h.symm)

/-- An explicit fixed preparation, avoiding a mere nonempty-parameter premise. -/
def fixedPreparation : ℝ := Real.sqrt 2 / 2

theorem fixedPreparation_irrational : Irrational fixedPreparation := by
  simpa [fixedPreparation] using irrational_sqrt_two.div_ratCast (q := 2) (by norm_num)

theorem fixedPreparation_interval : 0 < fixedPreparation ∧ fixedPreparation < 1 := by
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : Real.sqrt 2 < 2 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  dsimp [fixedPreparation]
  constructor <;> linarith

/-- The actual countermodel combines a bounded preparation weight, a normalized
positive alternative law, fixed-preparation weight noncontextuality, and a
concrete disagreement. The preceding theorems cover all available rational
refinements and every finite coordinate-compatible sum. -/
theorem fixed_preparation_countermodel :
    (∀ e, 0 ≤ weight fixedPreparation e ∧ weight fixedPreparation e ≤ 1) ∧
    (∀ e, 0 ≤ probability e ∧ probability e ≤ 1) ∧
    probability zero = 0 ∧ probability identity = 1 ∧
    (∀ e f, weight fixedPreparation e = weight fixedPreparation f →
      probability e = probability f) ∧
    probability portZero ≠ weight fixedPreparation portZero := by
  exact ⟨weight_bounds _ fixedPreparation_interval.1.le fixedPreparation_interval.2.le,
    probability_bounds, probability_accounting.1, probability_accounting.2.1,
    fixed_preparation_weight_noncontextual _ fixedPreparation_irrational,
    alternative_disagrees _ fixedPreparation_irrational⟩

end

end IDT.QMClosure.RestrictedActualizationControls
