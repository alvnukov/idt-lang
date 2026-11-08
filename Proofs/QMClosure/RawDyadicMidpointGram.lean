import Proofs.QMClosure.RawMidpointGramGeometry
import Proofs.QMClosure.RawFourPointGramBridge
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.NhdsWithin

/-!
# Dyadic midpoint compatibility and finite real Gram positivity

The carrier has a row-halving map, an antiphase map, and an arbitrary midpoint
operation. Squared midpoint convexity together with compatibility of halving
and midpoint rows is equivalent to complete-row averaging. The proof uses an
Archimedean bound on real powers and assumes no topology on preparations.

Signed repeated inputs and iterated halving synthesize normalized integer row
combinations. Nonnegative diagonals give integer Gram tests. Clearing rational
denominators and continuity of the finite coefficient polynomial extend these
tests to all real coefficients. This coefficient-space argument supplies no
preparation for an arbitrary real multiple of a row.
-/

namespace IDT.QMClosure.RawDyadicMidpointGram

open scoped BigOperators
open RawMidpointGramGeometry

noncomputable section

variable {V : Type*} {G : V → V → ℝ}

def HalfMidpointCompatible (G : V → V → ℝ) (A : V → V)
    (mid : V → V → V) : Prop :=
  ∀ x y z, G (mid (A x) (A y)) z = G (mid x y) z / 2

def halfIterate (A : V → V) : ℕ → V → V
  | 0, x => x
  | n + 1, x => A (halfIterate A n x)

theorem halfIterate_row (A : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2) (n : ℕ) (x z : V) :
    G (halfIterate A n x) z = (1 / 2 : ℝ) ^ n * G x z := by
  induction n with
  | zero => simp [halfIterate]
  | succ n ih =>
      rw [halfIterate, hhalf, ih, pow_succ]
      ring

theorem midpoint_halfIterate_row (A : V → V) (mid : V → V → V)
    (hcompat : HalfMidpointCompatible G A mid) (n : ℕ) (x y z : V) :
    G (mid (halfIterate A n x) (halfIterate A n y)) z =
      (1 / 2 : ℝ) ^ n * G (mid x y) z := by
  induction n with
  | zero => simp [halfIterate]
  | succ n ih =>
      rw [halfIterate, halfIterate, hcompat, ih, pow_succ]
      ring

theorem halfIterate_kernel (hsym : ∀ x y, G x y = G y x) (A : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2) (n : ℕ) (x y : V) :
    G (halfIterate A n x) (halfIterate A n y) =
      ((1 / 2 : ℝ) ^ n) ^ 2 * G x y := by
  rw [halfIterate_row A hhalf, hsym x (halfIterate A n y),
    halfIterate_row A hhalf, hsym y x]
  ring

theorem midpoint_halfIterate_diagonal (hsym : ∀ x y, G x y = G y x)
    (A : V → V) (mid : V → V → V) (hcompat : HalfMidpointCompatible G A mid)
    (n : ℕ) (x y : V) :
    G (mid (halfIterate A n x) (halfIterate A n y))
        (mid (halfIterate A n x) (halfIterate A n y)) =
      ((1 / 2 : ℝ) ^ n) ^ 2 * G (mid x y) (mid x y) := by
  rw [midpoint_halfIterate_row A mid hcompat,
    hsym (mid x y) (mid (halfIterate A n x) (halfIterate A n y)),
    midpoint_halfIterate_row A mid hcompat]
  ring

theorem le_zero_of_le_dyadic_mul (C delta : ℝ)
    (h : ∀ n : ℕ, delta ≤ (1 / 2 : ℝ) ^ n * C) : delta ≤ 0 := by
  by_contra hd
  have hdpos : 0 < delta := lt_of_not_ge hd
  by_cases hC : 0 < C
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hdpos hC)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have ht : (1 / 2 : ℝ) ^ n * C < delta := (lt_div_iff₀ hC).mp hn
    linarith [h n]
  · have hzero := h 0
    norm_num at hzero
    linarith

theorem midpoint_slack_nonnegative (mid : V → V → V)
    (hconv : SquaredMidpointConvex G mid) (z x y : V) :
    0 ≤ (G x x + G y y) / 2 - G (mid x y) (mid x y) +
      2 * G z (mid x y) - G z x - G z y := by
  have ht := hconv z x y
  dsimp [squaredDistance] at ht
  linarith

/-- Contracted target pairs and the two references z and N z bound both signs
of the midpoint row defect by a dyadic multiple of one fixed real constant. -/
theorem midpointRowAverage_of_squaredMidpointConvex
    (hsym : ∀ x y, G x y = G y x) (A N : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (mid : V → V → V) (hcompat : HalfMidpointCompatible G A mid)
    (hconv : SquaredMidpointConvex G mid) : MidpointRowAverage G mid := by
  intro x y z
  let C := (G x x + G y y) / 2 - G (mid x y) (mid x y)
  let delta := 2 * G z (mid x y) - G z x - G z y
  have hright (n : ℕ) (w : V) :
      G z (halfIterate A n w) = (1 / 2 : ℝ) ^ n * G z w := by
    rw [hsym, halfIterate_row A hhalf, hsym w z]
  have hmright (n : ℕ) :
      G z (mid (halfIterate A n x) (halfIterate A n y)) =
        (1 / 2 : ℝ) ^ n * G z (mid x y) := by
    rw [hsym, midpoint_halfIterate_row A mid hcompat, hsym (mid x y) z]
  have hplus (n : ℕ) :
      0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * C + (1 / 2 : ℝ) ^ n * delta := by
    have ht := midpoint_slack_nonnegative mid hconv z
      (halfIterate A n x) (halfIterate A n y)
    rw [halfIterate_kernel hsym A hhalf, halfIterate_kernel hsym A hhalf,
      midpoint_halfIterate_diagonal hsym A mid hcompat, hmright, hright, hright] at ht
    dsimp [C, delta]
    nlinarith
  have hminus (n : ℕ) :
      0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * C - (1 / 2 : ℝ) ^ n * delta := by
    have ht := midpoint_slack_nonnegative mid hconv (N z)
      (halfIterate A n x) (halfIterate A n y)
    simp only [hneg] at ht
    rw [halfIterate_kernel hsym A hhalf, halfIterate_kernel hsym A hhalf,
      midpoint_halfIterate_diagonal hsym A mid hcompat, hmright, hright, hright] at ht
    dsimp [C, delta]
    nlinarith
  have hup (n : ℕ) : delta ≤ (1 / 2 : ℝ) ^ n * C := by
    apply le_of_mul_le_mul_left (a := (1 / 2 : ℝ) ^ n) ?_
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
    nlinarith [hminus n]
  have hlo (n : ℕ) : -delta ≤ (1 / 2 : ℝ) ^ n * C := by
    apply le_of_mul_le_mul_left (a := (1 / 2 : ℝ) ^ n) ?_
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
    nlinarith [hplus n]
  have hd : delta = 0 := by
    have hu := le_zero_of_le_dyadic_mul C delta hup
    have hl := le_zero_of_le_dyadic_mul C (-delta) hlo
    linarith
  dsimp [delta] at hd
  rw [hsym z (mid x y), hsym z x, hsym z y] at hd
  linarith

theorem halfMidpointCompatible_of_preparationEquality (A : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2) (mid : V → V → V)
    (heq : ∀ x y, mid (A x) (A y) = A (mid x y)) :
    HalfMidpointCompatible G A mid := by
  intro x y z
  rw [heq, hhalf]

theorem midpointRowAverage_iff_squaredMidpointConvex_and_compatible
    (hsym : ∀ x y, G x y = G y x) (A N : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V) :
    MidpointRowAverage G mid ↔
      SquaredMidpointConvex G mid ∧ HalfMidpointCompatible G A mid := by
  constructor
  · intro hrow
    refine ⟨squaredMidpointConvex_of_midpointRowAverage hsym hnonneg mid hrow, ?_⟩
    intro x y z
    rw [hrow, hhalf, hhalf, hrow]
    ring
  · rintro ⟨hconv, hcompat⟩
    exact midpointRowAverage_of_squaredMidpointConvex hsym A N hhalf hneg mid hcompat hconv

theorem diagonal_nonnegative (hsym : ∀ x y, G x y = G y x) (A : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2)
    (hnonneg : NonnegativeSquaredDistances G) (x : V) : 0 ≤ G x x := by
  have hr : G x (A x) = G x x / 2 := by rw [hsym, hhalf]
  have ha : G (A x) (A x) = G x x / 4 := by rw [hhalf, hr]; ring
  have hp := hnonneg x (A x)
  dsimp [squaredDistance] at hp
  rw [hr, ha] at hp
  linarith

theorem midpoint_antiphase_zero_row (N : V → V)
    (hneg : ∀ x z, G (N x) z = -G x z) (mid : V → V → V)
    (hrow : MidpointRowAverage G mid) (x z : V) : G (mid x (N x)) z = 0 := by
  rw [hrow, hneg]
  ring

/-- A list of length n is synthesized with the positive normalization 2⁻ⁿ.
The empty list uses a midpoint with an antiphase preparation as a zero row. -/
theorem exists_list_row_sum (A N : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z) (mid : V → V → V)
    (hrow : MidpointRowAverage G mid) (anchor : V) (L : List V) :
    ∃ v : V, ∀ z, G v z = (1 / 2 : ℝ) ^ L.length * (L.map (fun x => G x z)).sum := by
  induction L with
  | nil =>
      refine ⟨mid anchor (N anchor), ?_⟩
      intro z
      simp only [midpoint_antiphase_zero_row N hneg mid hrow, List.length_nil,
        pow_zero, List.map_nil, List.sum_nil, mul_zero]
  | cons x L ih =>
      obtain ⟨v, hv⟩ := ih
      refine ⟨mid (halfIterate A L.length x) v, ?_⟩
      intro z
      rw [hrow, halfIterate_row A hhalf, hv]
      simp only [List.length_cons, List.map_cons, List.sum_cons, pow_succ]
      ring

def signedCopies (N : V → V) (c : ℤ) (x : V) : List V :=
  match c with
  | .ofNat n => List.replicate n x
  | .negSucc n => List.replicate (n + 1) (N x)

theorem signedCopies_row_sum (N : V → V)
    (hneg : ∀ x z, G (N x) z = -G x z) (c : ℤ) (x z : V) :
    ((signedCopies N c x).map (fun w => G w z)).sum = (c : ℝ) * G x z := by
  cases c with
  | ofNat n => simp [signedCopies]
  | negSucc n => simp [signedCopies, hneg, Int.cast_negSucc]; ring

def integerRows (N : V → V) : (n : ℕ) → (Fin n → V) → (Fin n → ℤ) → List V
  | 0, _, _ => []
  | n + 1, p, c => signedCopies N (c 0) (p 0) ++
      integerRows N n (fun i => p i.succ) (fun i => c i.succ)

theorem integerRows_row_sum (N : V → V)
    (hneg : ∀ x z, G (N x) z = -G x z) (n : ℕ)
    (p : Fin n → V) (c : Fin n → ℤ) (z : V) :
    ((integerRows N n p c).map (fun w => G w z)).sum =
      ∑ i, (c i : ℝ) * G (p i) z := by
  induction n with
  | zero => simp [integerRows]
  | succ n ih =>
      rw [integerRows, List.map_append, List.sum_append, signedCopies_row_sum N hneg,
        ih, Fin.sum_univ_succ]

theorem exists_integer_row_sum (A N : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z) (mid : V → V → V)
    (hrow : MidpointRowAverage G mid) (anchor : V) (n : ℕ)
    (p : Fin n → V) (c : Fin n → ℤ) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : V, ∀ z, G v z = r * ∑ i, (c i : ℝ) * G (p i) z := by
  let L := integerRows N n p c
  obtain ⟨v, hv⟩ := exists_list_row_sum A N hhalf hneg mid hrow anchor L
  refine ⟨(1 / 2 : ℝ) ^ L.length, pow_pos (by norm_num) _, v, ?_⟩
  intro z
  rw [hv, integerRows_row_sum N hneg]

theorem quadratic_scaled {n : ℕ} (p : Fin n → V) (c : Fin n → ℝ) (r : ℝ) :
    RawGramGeometry.quadratic G p (fun i => r * c i) =
      r ^ 2 * RawGramGeometry.quadratic G p c := by
  unfold RawGramGeometry.quadratic
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integer_quadratic_nonnegative (hsym : ∀ x y, G x y = G y x) (A N : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hrow : MidpointRowAverage G mid) (n : ℕ) (p : Fin n → V) (c : Fin n → ℤ) :
    0 ≤ RawGramGeometry.quadratic G p (fun i => (c i : ℝ)) := by
  cases n with
  | zero => simp [RawGramGeometry.quadratic]
  | succ n =>
      obtain ⟨r, hr, v, hv⟩ := exists_integer_row_sum A N hhalf hneg mid hrow
        (p 0) (n + 1) p c
      have hright (i : Fin (n + 1)) :
          G (p i) v = r * ∑ j, (c j : ℝ) * G (p i) (p j) := by
        rw [hsym (p i) v, hv]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym (p j) (p i)]
      have he : G v v = r ^ 2 *
          RawGramGeometry.quadratic G p (fun i => (c i : ℝ)) := by
        rw [hv]
        simp only [hright, Finset.mul_sum, RawGramGeometry.quadratic]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hd := diagonal_nonnegative hsym A hhalf hnonneg v
      have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
      rw [he] at hd
      exact (mul_nonneg_iff_of_pos_left hr2).mp hd

/-- A finite rational vector has one nonzero natural denominator and an integer
numerator vector. The construction concerns coefficients only. -/
theorem exists_common_denominator : ∀ (n : ℕ) (q : Fin n → ℚ),
    ∃ D : ℕ, D ≠ 0 ∧ ∃ a : Fin n → ℤ,
      ∀ i, (a i : ℝ) = (D : ℝ) * (q i : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro q
      exact ⟨1, by decide, Fin.elim0, by intro i; exact Fin.elim0 i⟩
  | succ n ih =>
      intro q
      obtain ⟨D, hD, a, ha⟩ := ih (fun i => q i.succ)
      refine ⟨D * (q 0).den, mul_ne_zero hD (q 0).den_nz,
        Fin.cons ((D : ℤ) * (q 0).num) (fun i => a i * (q 0).den), ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
        rw [Rat.cast_def]
        have hd : ((q 0).den : ℝ) ≠ 0 := by exact_mod_cast (q 0).den_nz
        field_simp
      · simp only [Fin.cons_succ, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, ha]
        ring

/-- Integer tests determine a finite real Gram quadratic polynomial through
rational denominator clearing and coefficient-space density. -/
theorem gramNonnegative_of_integer_tests {n : ℕ} (p : Fin n → V)
    (hint : ∀ a : Fin n → ℤ,
      0 ≤ RawGramGeometry.quadratic G p (fun i => (a i : ℝ))) :
    ∀ c : Fin n → ℝ, 0 ≤ RawGramGeometry.quadratic G p c := by
  have hrat (q : Fin n → ℚ) :
      0 ≤ RawGramGeometry.quadratic G p (fun i => (q i : ℝ)) := by
    obtain ⟨D, hD, a, ha⟩ := exists_common_denominator n q
    have htest := hint a
    have hfun : (fun i => (a i : ℝ)) = (fun i => (D : ℝ) * (q i : ℝ)) :=
      funext ha
    rw [hfun, quadratic_scaled] at htest
    have hDreal : (D : ℝ) ≠ 0 := by exact_mod_cast hD
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero hDreal)).mp htest
  have hcont : Continuous (fun c : Fin n → ℝ => RawGramGeometry.quadratic G p c) := by
    unfold RawGramGeometry.quadratic
    fun_prop
  have hdense : DenseRange (fun q : Fin n → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  exact isClosed_property hdense (isClosed_le continuous_const hcont) hrat

/-- All finite real Gram inequalities follow without a preparation map for
arbitrary real scaling. Empty tuples and empty carriers are included. -/
theorem gramNonnegative_of_midpointRowAverage
    (hsym : ∀ x y, G x y = G y x) (A N : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hrow : MidpointRowAverage G mid) : ∀ n, RawGramGeometry.GramNonnegative G n := by
  intro n p
  exact gramNonnegative_of_integer_tests p
    (integer_quadratic_nonnegative hsym A N hhalf hneg hnonneg mid hrow n p)

theorem gramNonnegative_of_squaredMidpointConvex
    (hsym : ∀ x y, G x y = G y x) (A N : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hcompat : HalfMidpointCompatible G A mid) (hconv : SquaredMidpointConvex G mid) :
    ∀ n, RawGramGeometry.GramNonnegative G n :=
  gramNonnegative_of_midpointRowAverage hsym A N hhalf hneg hnonneg mid
    (midpointRowAverage_of_squaredMidpointConvex hsym A N hhalf hneg mid hcompat hconv)

open RawSparseConservationSelection RawFourPointGramBridge

/-- Existing local kernel compatibility remains explicit. The dyadic midpoint
premises derive four-point positivity and hence the existing sparse conclusions. -/
theorem conclusions_of_squaredMidpointConvex (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (A N : V → V)
    (hhalf : ∀ x z, G (A x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hcompat : HalfMidpointCompatible G A mid) (hconv : SquaredMidpointConvex G mid) :
    (∀ n, RawGramGeometry.GramNonnegative G n) ∧
      (∀ x, 0 ≤ D.weight x) ∧ PairConserved D ∧ ObservedMedial D ∧
      SparseMarginalLaw D ∧ RawSparseConservationTests.Tests D := by
  have hgram := gramNonnegative_of_squaredMidpointConvex hk.symmetric A N hhalf hneg
    hnonneg mid hcompat hconv
  exact ⟨hgram, conclusions_of_fourPointPositive D G hk (hgram 4)⟩

end

end IDT.QMClosure.RawDyadicMidpointGram
