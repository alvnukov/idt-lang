import Proofs.QMClosure.InitialCountGeometry
import Proofs.QMClosure.InitialPairedCountBounds

/-!
Prepared count comparisons on the literal initial carrier.
Every scalar cancellation below is an identity of initial elements, and every
order comparison takes place at an actual preparation.
-/

namespace IDT.QMClosure.InitialPreparedCountOrder

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open InitialCountGeometry
open InitialPairedCountBounds

/-- Natural count order at every actual initial preparation. -/
def PreparedCountOrder (W : P → ℝ) : Prop :=
  ∀ p n m n' m', n ≤ n' → m ≤ m' →
    W (bag n m * p) ≤ W (bag n' m' * p)

variable {W : P → ℝ}

/-- Serial response increase at every initial preparation. -/
def ResponseIncreasing (W : P → ℝ) (M : P) : Prop :=
  ∀ p, W p ≤ W (M * p)

theorem increasing_one : ResponseIncreasing W 1 := by
  intro p
  simp

theorem ResponseIncreasing.mul {M N : P}
    (hM : ResponseIncreasing W M) (hN : ResponseIncreasing W N) :
    ResponseIncreasing W (M * N) := by
  intro p
  exact (hN p).trans (by simpa [mul_assoc] using hM (N * p))

theorem ResponseIncreasing.pow {M : P} (hM : ResponseIncreasing W M) (n : ℕ) :
    ResponseIncreasing W (M ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (increasing_one (W := W))
  | succ n ih => simpa [pow_succ] using ih.mul hM

theorem plusOverhead_increasing (hOrd : PreparedCountOrder W) (k m n : ℕ) (hn : 2 ^ k ≤ n) :
    ResponseIncreasing W (plusOverhead k m n) := by
  intro p
  have ho := hOrd (twoInv ^ k * bInv * p) 0 (2 ^ k) m n
    (Nat.zero_le m) hn
  have hid : bag 0 (2 ^ k) * (twoInv ^ k * bInv * p) = p := by
    simp only [bag, Nat.cast_zero, zero_mul, zero_add, Nat.cast_pow, Nat.cast_ofNat]
    calc
      (2 : P) ^ k * b * (twoInv ^ k * bInv * p) =
          ((2 : P) ^ k * twoInv ^ k) * (b * bInv) * p := by ring
      _ = p := by rw [two_power_cancel, b_mul_bInv]; simp
  rw [hid] at ho
  simpa only [plusOverhead, mul_assoc] using ho

theorem minusOverhead_increasing (hOrd : PreparedCountOrder W) (k m n : ℕ) (hn : 2 ^ k ≤ n) :
    ResponseIncreasing W (minusOverhead k m n) := by
  intro p
  have ho := hOrd (twoInv ^ k * aInv * p) (2 ^ k) 0 n m
    hn (Nat.zero_le m)
  have hid : bag (2 ^ k) 0 * (twoInv ^ k * aInv * p) = p := by
    simp only [bag, Nat.cast_zero, zero_mul, add_zero, Nat.cast_pow, Nat.cast_ofNat]
    calc
      (2 : P) ^ k * a * (twoInv ^ k * aInv * p) =
          ((2 : P) ^ k * twoInv ^ k) * (a * aInv) * p := by ring
      _ = p := by rw [two_power_cancel, a_mul_aInv]; simp
  rw [hid] at ho
  simpa only [minusOverhead, mul_assoc] using ho

theorem plusWord_increasing (hOrd : PreparedCountOrder W) (k m : ℕ) : ResponseIncreasing W (plusWord k m) :=
  plusOverhead_increasing hOrd k m (2 ^ k) le_rfl

theorem minusWord_increasing (hOrd : PreparedCountOrder W) (k m : ℕ) : ResponseIncreasing W (minusWord k m) :=
  minusOverhead_increasing hOrd k m (2 ^ k) le_rfl

theorem pairedWord_increasing (hOrd : PreparedCountOrder W) (k m n : ℕ) :
    ResponseIncreasing W (pairedWord k m n) :=
  ((plusWord_increasing hOrd k m).mul (minusWord_increasing hOrd k m)).pow n

/-- The selected numerical cofinal sequence is realized by an actual finite
initial-P paired word at every index. -/
def selectedPairedWord (target : ℝ) (hTarget : 1 < target) (k : ℕ) : P :=
  pairedWord k 1 (pairedIndex target hTarget k)

theorem selectedPairedWord_increasing {W : P → ℝ} (hOrd : PreparedCountOrder W)
    (target : ℝ) (hTarget : 1 < target) (k : ℕ) :
    ResponseIncreasing W (selectedPairedWord target hTarget k) :=
  pairedWord_increasing hOrd k 1 (pairedIndex target hTarget k)

theorem selectedPairedWord_coordinates (target : ℝ) (hTarget : 1 < target) (k : ℕ) :
    complexEvaluation (selectedPairedWord target hTarget k) = ((realAmplification target hTarget k : ℝ) : ℂ) ∧
    realShadow (selectedPairedWord target hTarget k) = shadowAmplification target hTarget k := by
  simpa only [selectedPairedWord, realAmplification, shadowAmplification,
    dyadicStep_eq, Nat.cast_one] using pairedWord_coordinates k 1 (pairedIndex target hTarget k)

/-- Vacuum normalization is needed only for this nonnegativity conclusion. -/
theorem response_nonnegative (h0 : W 0 = 0) (hOrd : PreparedCountOrder W) (p : P) :
    0 ≤ W p := by
  have ho := hOrd p 0 0 1 1 (by decide) (by decide)
  simpa only [bag_zero_zero, zero_mul, bag_diagonal, Nat.cast_zero, Nat.cast_one, one_mul, h0] using ho

/-- Dyadic comparison changes the actual preparation to the common inverse
binary scale. It assumes no rule for evaluating a scaled response. -/
theorem prepared_dyadic_order (hOrd : PreparedCountOrder W)
    (s t s' t' : DyadicCount) (hs : (s : ℝ) ≤ (s' : ℝ))
    (ht : (t : ℝ) ≤ (t' : ℝ)) (p : P) :
    W (raw s t * p) ≤ W (raw s' t' * p) := by
  obtain ⟨k, n, m, n', m', hn, hm, hn', hm'⟩ :=
    common_four_nonnegative_dyadic_counts s t s' t'
  have hd : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hnn' : n ≤ n' := by
    have hr : (n : ℝ) ≤ (n' : ℝ) := by
      apply (div_le_div_iff_of_pos_right hd).mp
      simpa only [← hn, ← hn'] using hs
    exact_mod_cast hr
  have hmm' : m ≤ m' := by
    have hr : (m : ℝ) ≤ (m' : ℝ) := by
      apply (div_le_div_iff_of_pos_right hd).mp
      simpa only [← hm, ← hm'] using ht
    exact_mod_cast hr
  have hsgrid : s = dyadicCount k n := Subtype.ext hn
  have htgrid : t = dyadicCount k m := Subtype.ext hm
  have hs'grid : s' = dyadicCount k n' := Subtype.ext hn'
  have ht'grid : t' = dyadicCount k m' := Subtype.ext hm'
  rw [hsgrid, htgrid, hs'grid, ht'grid, raw_grid, raw_grid]
  have ho := hOrd (twoInv ^ k * p) n m n' m' hnn' hmm'
  simpa only [mul_assoc, mul_comm, mul_left_comm] using ho

/-- A finite exact transport gives a lower comparison by shifting the actual
preparation. The endpoint is exactly p after binary cancellation. -/
theorem prepared_dyadic_lower_transfer_of_identity (hOrd : PreparedCountOrder W)
    {M x p : P} (hM : ResponseIncreasing W M) (A B : ℕ)
    (htransport : M * x = bag A B * p) (j k : ℕ)
    (hA : j * A ≤ 2 ^ k) (hB : j * B ≤ 2 ^ k) :
    W (twoInv ^ k * ((j : P) * x)) ≤ W p := by
  have hshift :
      M * (twoInv ^ k * ((j : P) * x)) =
        bag (j * A) (j * B) * (twoInv ^ k * p) := by
    calc
      M * (twoInv ^ k * ((j : P) * x)) =
          (j : P) * (twoInv ^ k * (M * x)) := by ring
      _ = (j : P) * (twoInv ^ k * (bag A B * p)) := by rw [htransport]
      _ = bag (j * A) (j * B) * (twoInv ^ k * p) := by
        rw [← nat_mul_bag]
        ring
  have hcancel : bag (2 ^ k) (2 ^ k) * (twoInv ^ k * p) = p := by
    rw [bag_diagonal, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc,
      two_power_cancel, one_mul]
  calc
    W (twoInv ^ k * ((j : P) * x)) ≤
        W (M * (twoInv ^ k * ((j : P) * x))) := hM _
    _ = W (bag (j * A) (j * B) * (twoInv ^ k * p)) := by rw [hshift]
    _ ≤ W (bag (2 ^ k) (2 ^ k) * (twoInv ^ k * p)) :=
      hOrd (twoInv ^ k * p) _ _ _ _ hA hB
    _ = W p := by rw [hcancel]

theorem prepared_dyadic_lower_transfer (hOrd : PreparedCountOrder W)
    {M p : P} (hM : ResponseIncreasing W M) (d : ExactRawTransport M p)
    (j k : ℕ) (hA : j * d.targetA ≤ 2 ^ k) (hB : j * d.targetB ≤ 2 ^ k) :
    W (twoInv ^ k * bag (j * d.rawA) (j * d.rawB)) ≤ W p := by
  rw [← nat_mul_bag]
  exact prepared_dyadic_lower_transfer_of_identity hOrd hM
    d.targetA d.targetB d.identity j k hA hB

/-- The serial-shifted source uses the same comparison theorem and an exact
initial-element identity, with target p fixed. -/
theorem prepared_serial_shifted_lower_transfer (hOrd : PreparedCountOrder W)
    {M p : P} (hM : ResponseIncreasing W M) (r : ℕ)
    (d : ExactRawTransport M (cInv ^ r * p))
    (j k : ℕ) (hA : j * d.targetA ≤ 2 ^ k) (hB : j * d.targetB ≤ 2 ^ k) :
    W (twoInv ^ k * (c ^ r * bag (j * d.rawA) (j * d.rawB))) ≤ W p := by
  have hsource : c ^ r * bag (j * d.rawA) (j * d.rawB) =
      (j : P) * (c ^ r * bag d.rawA d.rawB) := by
    rw [← nat_mul_bag]
    ring
  rw [hsource]
  exact prepared_dyadic_lower_transfer_of_identity hOrd hM
    d.targetA d.targetB (serial_shifted_transport r d) j k hA hB

/-- Exact upper landing needs only increase of its actual program. -/
theorem prepared_dyadic_upper_transfer {M p : P}
    (hM : ResponseIncreasing W M) (k n m : ℕ)
    (hland : M * p = twoInv ^ k * bag n m) :
    W p ≤ W (twoInv ^ k * bag n m) := by
  simpa only [hland] using hM p

end
end IDT.QMClosure.InitialPreparedCountOrder
