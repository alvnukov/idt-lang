import Proofs.QMClosure.NativeGeneratorMixtureReadout
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Native calibration and bounded firing-occurrence budgets

The native calibration yields W(2^k)=4^k. In the abstract resource model, t is
a preparation-family parameter. An affine initial firing-occurrence budget in
t, fixed depth/fanout, a fixed background budget, and uniformly bounded weighted
events give a uniform affine upper bound in t. Identifying or dominating raw W
by that bound is an ADDITIONAL preparation/readout bridge and is incompatible
with native calibration when the prepared value is the natural cast of t.

The diagonal original a/b bag has value n*a+n*b=n and exactly 2*n tagged input
occurrences. Its explicit corollary therefore uses events(2*n), with resource
bounds indexed by actual tagged input count. Reindexing t=2*n preserves an
affine budget, with initial slope 2*A and the same fixed background H.

Original history occurrences are syntactic alternatives. Their identification
with physical inputs, and an affine cost for preparing their coherent sum,
are supplied only by the bridge in this wall. Coherent addition has no
physical cost semantics in the presentation. The normalized native mixer does
not assert a free physical implementation of unattenuated p+q. This wall makes
no assertion that physical detectors are impossible or that QM violates a
resource bound. It identifies a missing preparation/readout bridge.

Each level counts reachable FIRING OCCURRENCES at that depth in the supplied
bounded-depth/fanout graph. Repeated uses of the same physical apparatus are
separate firing occurrences. Every firing and every counted output event must
be included in the accounting. A reusable resource counted once cannot stand
in for an unbounded number of firings. Repeat/autonomous firings remain subject
to the same occurrence budget, depth, fanout, and events-per-firing bounds.
The event-weight ceiling is fixed and nonnegative. A finite original-ancestry
order alone supplies none of these participation or preparation-cost bounds.
-/

noncomputable section

namespace IDT.QMClosure.NativeBoundedResourceWall

open scoped BigOperators
open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout

attribute [local instance] presentationCommRing presentationCharZero

/-- Native calibration alone, with no polynomial/kernel regularity premise. -/
theorem readout_two_pow
    {W : Presentation → ℝ} (L : NativeTransfer W) (k : ℕ) :
    W ((2 : Presentation) ^ k) = (4 : ℝ) ^ k := by
  induction k with
  | zero => simpa using L.unit
  | succ k ih =>
      rw [pow_succ', readout_double_mul L, ih, pow_succ']

/-- Even the dyadic counts rule out a uniform linear upper bound. -/
theorem no_uniform_linear_bound
    {W : Presentation → ℝ} (L : NativeTransfer W) (C : ℝ) :
    ¬∀ n : ℕ, W (n : Presentation) ≤ C * (n : ℝ) := by
  intro hbound
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
  have hdyadic : (4 : ℝ) ^ k ≤ C * (2 : ℝ) ^ k := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, readout_two_pow L] using hbound (2 ^ k)
  have hfour : (4 : ℝ) ^ k = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  rw [hfour] at hdyadic
  have hle : (2 : ℝ) ^ k ≤ C :=
    le_of_mul_le_mul_right hdyadic (pow_pos (by norm_num : (0 : ℝ) < 2) k)
  exact (not_lt_of_ge hle) hk

/-- Fixed background resources are allowed. Native calibration excludes a
uniform affine upper bound as well as a uniform linear bound. -/
theorem no_uniform_affine_bound
    {W : Presentation → ℝ} (L : NativeTransfer W) (C D : ℝ) :
    ¬∀ n : ℕ, W (n : Presentation) ≤ C * (n : ℝ) + D := by
  intro hbound
  apply no_uniform_linear_bound L (C + |D|)
  intro n
  by_cases hn : n = 0
  · subst n
    simp [readout_zero L]
  · have hn' : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hD : D ≤ |D| * (n : ℝ) := by
      have h1 : D ≤ |D| := le_abs_self D
      have h2 : 0 ≤ |D| * ((n : ℝ) - 1) :=
        mul_nonneg (abs_nonneg D) (sub_nonneg.mpr hn')
      nlinarith
    have h := hbound n
    nlinarith

/-- Numeric budget for a supplied bounded-depth/fanout firing-occurrence graph.
`levels t r` counts all reachable firing occurrences at depth r for preparation
family parameter t. Repeated firing of one physical component contributes a
separate occurrence each time. Every firing and counted event must be covered.
All constants are uniform over t. H is a fixed background/ancilla firing budget
and B bounds counted events per accounted firing occurrence. -/
structure UniformResourceBounds
    (levels : ℕ → ℕ → ℕ) (events : ℕ → ℕ) (A H B F D : ℕ) : Prop where
  initial : ∀ t, levels t 0 ≤ A * t + H
  next : ∀ t r, r < D → levels t (r + 1) ≤ F * levels t r
  accounted : ∀ t, events t ≤ B * ∑ r ∈ Finset.range (D + 1), levels t r

namespace UniformResourceBounds

variable {levels : ℕ → ℕ → ℕ} {events : ℕ → ℕ} {A H B F D : ℕ}
    (R : UniformResourceBounds levels events A H B F D)

include R in
/-- Fixed-depth fanout bounds firing occurrences at each accounted level. -/
theorem level_le (t r : ℕ) (hr : r ≤ D) :
    levels t r ≤ (A * t + H) * F ^ r := by
  suffices h : ∀ r, r ≤ D → levels t r ≤ (A * t + H) * F ^ r from h r hr
  intro r
  induction r with
  | zero => intro _; simpa using R.initial t
  | succ r ih =>
      intro hr
      have hprev : r ≤ D := by omega
      have hstep : r < D := by omega
      calc
        levels t (r + 1) ≤ F * levels t r := R.next t r hstep
        _ ≤ F * ((A * t + H) * F ^ r) := Nat.mul_le_mul_left F (ih hprev)
        _ = (A * t + H) * F ^ (r + 1) := by rw [pow_succ]; ring

include R in
/-- The geometric-sum event budget is affine in preparation-family parameter t. -/
theorem events_le (t : ℕ) :
    events t ≤ B * (A * t + H) * ∑ r ∈ Finset.range (D + 1), F ^ r := by
  calc
    events t ≤ B * ∑ r ∈ Finset.range (D + 1), levels t r := R.accounted t
    _ ≤ B * ∑ r ∈ Finset.range (D + 1), (A * t + H) * F ^ r := by
      apply Nat.mul_le_mul_left
      apply Finset.sum_le_sum
      intro r hr
      exact R.level_le t r (by have h := Finset.mem_range.mp hr; omega)
    _ = _ := by rw [← Finset.mul_sum]; ring

end UniformResourceBounds

/-- Abstract conditional resource wall. The preparation-family parameter t is
mapped to the presented value (t : Presentation) by the additional bridge.
It uniformly dominates raw W by weighted accounted event count in a supplied
affine-cost firing-occurrence model. Exact identification is a special case. -/
theorem no_uniform_weighted_resource_bridge
    {W : Presentation → ℝ} (L : NativeTransfer W)
    (levels : ℕ → ℕ → ℕ) (events : ℕ → ℕ) (A H B F D : ℕ)
    (R : UniformResourceBounds levels events A H B F D)
    (ω : ℝ) (hω : 0 ≤ ω)
    (hbridge : ∀ t : ℕ, W (t : Presentation) ≤ ω * (events t : ℝ)) : False := by
  let S : ℕ := ∑ r ∈ Finset.range (D + 1), F ^ r
  let C : ℝ := ω * (B : ℝ) * (A : ℝ) * (S : ℝ)
  let E : ℝ := ω * (B : ℝ) * (H : ℝ) * (S : ℝ)
  apply no_uniform_affine_bound L C E
  intro t
  have hcount : (events t : ℝ) ≤
      (B : ℝ) * ((A : ℝ) * (t : ℝ) + (H : ℝ)) * (S : ℝ) := by
    have hnat : events t ≤ B * (A * t + H) * S := R.events_le t
    exact_mod_cast hnat
  calc
    W (t : Presentation) ≤ ω * (events t : ℝ) := hbridge t
    _ ≤ ω * ((B : ℝ) * ((A : ℝ) * (t : ℝ) + (H : ℝ)) * (S : ℝ)) :=
      mul_le_mul_of_nonneg_left hcount hω
    _ = C * (t : ℝ) + E := by dsimp [C, E]; ring


/-- The original diagonal bag is evaluated before any readout is applied. -/
def diagonalBag (n : ℕ) : Presentation :=
  (n : Presentation) * a + (n : Presentation) * b

/-- The two original token types remain disjoint in the input indexing. -/
abbrev DiagonalOccurrence (n : ℕ) := Fin n ⊕ Fin n

def diagonalOccurrenceValue {n : ℕ} : DiagonalOccurrence n → Presentation
  | Sum.inl _ => a
  | Sum.inr _ => b

/-- The coherent diagonal bag is the sum of its original tagged occurrences. -/
theorem diagonalBag_eq_sum_occurrences (n : ℕ) :
    diagonalBag n = ∑ t : DiagonalOccurrence n, diagonalOccurrenceValue t := by
  simp [diagonalBag, DiagonalOccurrence, diagonalOccurrenceValue,
    Fintype.sum_sum_type, nsmul_eq_mul]

/-- The parameter n gives exactly 2*n original tagged inputs in this family. -/
theorem diagonalBag_original_input_count (n : ℕ) :
    Fintype.card (DiagonalOccurrence n) = 2 * n := by
  simp [DiagonalOccurrence, two_mul]

/-- Transparency identifies the diagonal bag's value with the natural cast. -/
theorem diagonalBag_eq_nat (n : ℕ) : diagonalBag n = (n : Presentation) := by
  unfold diagonalBag
  calc
    (n : Presentation) * a + (n : Presentation) * b =
        (n : Presentation) * (a + b) := by ring
    _ = (n : Presentation) := by rw [transparent, mul_one]

/-- Equality of the prepared value transports every supplied readout. -/
theorem readout_diagonalBag_eq_nat (W : Presentation → ℝ) (n : ℕ) :
    W (diagonalBag n) = W (n : Presentation) := by
  rw [diagonalBag_eq_nat]

/-- Original diagonal-bag resource wall with bounds indexed by actual original
input count. There are 2*n tagged inputs, so the additional bridge uses
`events (2*n)`. Reindexing the complete firing-occurrence accounting doubles
only the initial slope A. The background H and fixed event ceiling ω persist.
This corollary uses no kernel regularity or full norm-selection result. -/
theorem no_original_diagonal_bag_resource_bridge
    {W : Presentation → ℝ} (L : NativeTransfer W)
    (levels : ℕ → ℕ → ℕ) (events : ℕ → ℕ) (A H B F D : ℕ)
    (R : UniformResourceBounds levels events A H B F D)
    (ω : ℝ) (hω : 0 ≤ ω)
    (hbridge : ∀ n : ℕ,
      W ((n : Presentation) * a + (n : Presentation) * b) ≤
        ω * (events (2 * n) : ℝ)) : False := by
  let levels2 : ℕ → ℕ → ℕ := fun n r => levels (2 * n) r
  let events2 : ℕ → ℕ := fun n => events (2 * n)
  have R2 : UniformResourceBounds levels2 events2 (2 * A) H B F D := by
    constructor
    · intro n
      change levels (2 * n) 0 ≤ (2 * A) * n + H
      calc
        levels (2 * n) 0 ≤ A * (2 * n) + H := R.initial (2 * n)
        _ = (2 * A) * n + H := by ring
    · intro n r hr
      exact R.next (2 * n) r hr
    · intro n
      exact R.accounted (2 * n)
  apply no_uniform_weighted_resource_bridge L levels2 events2 (2 * A) H B F D R2 ω hω
  intro n
  change W (n : Presentation) ≤ ω * (events (2 * n) : ℝ)
  have hbag : (n : Presentation) * a + (n : Presentation) * b =
      (n : Presentation) := diagonalBag_eq_nat n
  simpa only [hbag] using hbridge n

end IDT.QMClosure.NativeBoundedResourceWall
