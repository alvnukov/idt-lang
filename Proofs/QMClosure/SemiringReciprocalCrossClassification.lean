import Proofs.QMClosure.CountCrossIncrementRigidity
import Proofs.QMClosure.IntegerReciprocalCountClassification

/-!
The main conditional adapter uses an arbitrary Semiring.
Transparency, integer reciprocal cross, individual half transfer and a uniform
mixed-increment sign are supplied inputs. All conclusions are conditional.
The only IDT imports are the pure grid and pure sequence modules.
-/

noncomputable section

namespace IDT.QMClosure.SemiringReciprocalCrossClassification

open CountCrossIncrementRigidity

variable {S : Type*} [Semiring S]

structure Laws (a b : S) (d : ℕ) (W : S → ℝ) : Prop where
  transparent : a + b = 1
  reciprocal : (d : S) * (a * b) = 1
  unit : W 1 = 1
  halfA : ∀ p, W (a * p) = W p / 2
  halfB : ∀ p, W (b * p) = W p / 2

def bag (a b : S) (n m : ℕ) : S := (n : S) * a + (m : S) * b

def grid (a b : S) (W : S → ℝ) : Grid := fun n m => W (bag a b n m)

def axis (W : S → ℝ) (n : ℕ) : ℝ := W (n : S) / 2

def UniformMixedSign (a b : S) (W : S → ℝ) : Prop :=
  (∀ n m, 0 ≤ mixed (grid a b W) n m) ∨
    (∀ n m, mixed (grid a b W) n m ≤ 0)

theorem vacuum {a b : S} {d : ℕ} {W : S → ℝ} (h : Laws a b d W) :
    W 0 = 0 := by
  have he := h.halfA 0
  simp only [mul_zero] at he
  linarith

theorem natural_halfA {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) (n : ℕ) : W ((n : S) * a) = axis W n := by
  have he : (n : S) * a = a * (n : S) := (Nat.cast_commute n a).eq
  rw [he, h.halfA]
  rfl

theorem natural_halfB {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) (n : ℕ) : W ((n : S) * b) = axis W n := by
  have he : (n : S) * b = b * (n : S) := (Nat.cast_commute n b).eq
  rw [he, h.halfB]
  rfl

theorem diagonal {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) (n : ℕ) : grid a b W n n = W (n : S) := by
  have he : bag a b n n = (n : S) := by
    dsimp [bag]
    rw [← mul_add, h.transparent, mul_one]
  change W (bag a b n n) = _
  rw [he]

theorem saturated {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) : SaturatedSquares (grid a b W) := by
  intro n
  have hdiag := diagonal h n
  have ha : grid a b W n 0 = axis W n := by
    simpa [grid, bag] using natural_halfA h n
  have hb : grid a b W 0 n = axis W n := by
    simpa [grid, bag] using natural_halfB h n
  have hz : grid a b W 0 0 = 0 := by simpa [grid, bag] using vacuum h
  dsimp [axis] at ha hb
  linarith

theorem count_separable {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) (hs : UniformMixedSign a b W) (n m : ℕ) :
    grid a b W n m = axis W n + axis W m := by
  have hm : ∀ n m, mixed (grid a b W) n m = 0 := by
    rcases hs with hs | hs
    · exact mixed_zero_of_nonnegative (saturated h) hs
    · exact mixed_zero_of_nonpositive (saturated h) hs
  have he := separable_of_mixed_zero hm n m
  have ha : grid a b W n 0 = axis W n := by
    simpa [grid, bag] using natural_halfA h n
  have hb : grid a b W 0 m = axis W m := by
    simpa [grid, bag] using natural_halfB h m
  have hz : grid a b W 0 0 = 0 := by simpa [grid, bag] using vacuum h
  linarith

/-- Natural scalars are central in every semiring. -/
theorem cast_mul_left (n : ℕ) (x y : S) :
    x * ((n : S) * y) = (n : S) * (x * y) := by
  calc
    _ = (x * (n : S)) * y := (mul_assoc _ _ _).symm
    _ = ((n : S) * x) * y := by rw [← (Nat.cast_commute n x).eq]
    _ = _ := mul_assoc _ _ _

/-- Reciprocal cross is used without dividing by d or requiring d to be nonzero. -/
theorem scale_d {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) (p : S) : W ((d : S) * p) = 4 * W p := by
  have he : a * (b * ((d : S) * p)) = p := by
    calc
      _ = ((d : S) * (a * b)) * p := by
        rw [cast_mul_left d b p, cast_mul_left d a (b * p)]
        simp only [mul_assoc]
      _ = p := by rw [h.reciprocal, one_mul]
  have ha := h.halfA (b * ((d : S) * p))
  have hb := h.halfB ((d : S) * p)
  rw [he] at ha
  linarith

theorem scale_da {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) (p : S) : W (((d : S) * a) * p) = 2 * W p := by
  have he : ((d : S) * a) * p = a * ((d : S) * p) := by
    rw [cast_mul_left d a p, mul_assoc]
  rw [he, h.halfA, scale_d h]
  ring

/-- This algebra identity uses no subtraction, additive cancellation or ab=ba. -/
theorem bag_transport {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) (n k : ℕ) :
    ((d : S) * a) * bag a b n (n + k) = bag a b (d * n + k) k := by
  have hb : bag a b n (n + k) = (n : S) + (k : S) * b := by
    calc
      _ = (n : S) * (a + b) + (k : S) * b := by
        dsimp [bag]
        push_cast
        noncomm_ring
      _ = _ := by rw [h.transparent, mul_one]
  rw [hb]
  calc
    _ = ((d * n : ℕ) : S) * a + (k : S) * ((d : S) * (a * b)) := by
      have hn : ((d : S) * a) * (n : S) = ((d : S) * (n : S)) * a := by
        rw [mul_assoc, ← (Nat.cast_commute n a).eq, ← mul_assoc]
      have hk : ((d : S) * a) * ((k : S) * b) =
          (k : S) * ((d : S) * (a * b)) := by
        rw [cast_mul_left k ((d : S) * a) b, mul_assoc]
      rw [mul_add, hn, hk, Nat.cast_mul]
    _ = ((d * n : ℕ) : S) * a + (k : S) := by rw [h.reciprocal, mul_one]
    _ = ((d * n : ℕ) : S) * a + (k : S) * (a + b) := by rw [h.transparent, mul_one]
    _ = bag a b (d * n + k) k := by
      dsimp [bag]
      push_cast
      noncomm_ring

theorem axis_recurrence {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) (hs : UniformMixedSign a b W) :
    IntegerReciprocalCountClassification.Recurrence d (axis W) := by
  intro n k
  have he := scale_da h (bag a b n (n + k))
  rw [bag_transport h n k] at he
  change grid a b W (d * n + k) k = 2 * grid a b W n (n + k) at he
  rw [count_separable h hs, count_separable h hs] at he
  linarith

theorem classification {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) (hs : UniformMixedSign a b W) :
    (d = 2 ∧ ∀ n m, grid a b W n m = ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2) ∨
      (d = 4 ∧ ∀ n m, grid a b W n m = ((n : ℝ) + (m : ℝ)) / 2) := by
  have h0 : axis W 0 = 0 := by simp [axis, vacuum h]
  have h1 : axis W 1 = 1 / 2 := by simp [axis, h.unit]
  obtain hq | hl := IntegerReciprocalCountClassification.classification
    h0 h1 (axis_recurrence h hs)
  · left
    refine ⟨hq.1, fun n m => ?_⟩
    rw [count_separable h hs, hq.2 n, hq.2 m]
    ring
  · right
    refine ⟨hl.1, fun n m => ?_⟩
    rw [count_separable h hs, hl.2 n, hl.2 m]
    ring

/-- A finite operational inequality excludes the linear branch. -/
theorem quadratic_of_finite_contrast {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) (hs : UniformMixedSign a b W)
    (hc : W ((2 : S) * a) ≠ W 1) :
    d = 2 ∧ ∀ n m, grid a b W n m = ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2 := by
  obtain hq | hl := classification h hs
  · exact hq
  · exfalso
    apply hc
    have he := hl.2 2 0
    simpa [grid, bag, h.unit] using he

theorem cubic_impossible {a b : S} {W : S → ℝ}
    (h : Laws a b 3 W) (hs : UniformMixedSign a b W) : False := by
  obtain hq | hl := classification h hs <;> omega

/-- Transparency alone gives this absorption when reciprocal cross is two. -/
theorem square_absorption {a b : S} {W : S → ℝ} (h : Laws a b 2 W) :
    (a ^ 2 + b ^ 2) + 1 = 1 := by
  have hr : (2 : S) * (a * b) = 1 := by simpa using h.reciprocal
  have ha : a ^ 2 + a * b = a := by
    calc
      _ = a * (a + b) := by noncomm_ring
      _ = a := by rw [h.transparent, mul_one]
  have hb : a * b + b ^ 2 = b := by
    calc
      _ = (a + b) * b := by noncomm_ring
      _ = b := by rw [h.transparent, one_mul]
  calc
    _ = (a ^ 2 + a * b) + (a * b + b ^ 2) := by
      rw [← hr]
      noncomm_ring
    _ = 1 := by rw [ha, hb, h.transparent]

/-- Faithfulness at zero is an additional readout premise for destructive closure. -/
theorem square_sum_zero_of_faithful {a b : S} {W : S → ℝ}
    (h : Laws a b 2 W) (hf : ∀ x, W x = 0 → x = 0) :
    a ^ 2 + b ^ 2 = 0 := by
  have hr : (2 : S) * (a * b) = 1 := by simpa using h.reciprocal
  let T : S := a ^ 2 + b ^ 2
  let U : S := a ^ 3 + b ^ 3
  have ha : a ^ 3 + a ^ 2 * b = a ^ 2 := by
    calc
      _ = a ^ 2 * (a + b) := by noncomm_ring
      _ = a ^ 2 := by rw [h.transparent, mul_one]
  have hb : a * b ^ 2 + b ^ 3 = b ^ 2 := by
    calc
      _ = (a + b) * b ^ 2 := by noncomm_ring
      _ = b ^ 2 := by rw [h.transparent, one_mul]
  have hab : a ^ 2 * b + a * b ^ 2 = a * b := by
    calc
      _ = a * ((a + b) * b) := by noncomm_ring
      _ = a * b := by rw [h.transparent, one_mul]
  have hTU : T = U + a * b := by
    calc
      _ = (a ^ 3 + a ^ 2 * b) + (a * b ^ 2 + b ^ 3) := by
        dsimp [T]
        rw [ha, hb]
      _ = U + (a ^ 2 * b + a * b ^ 2) := by dsimp [U]; noncomm_ring
      _ = U + a * b := by rw [hab]
  have htwo : (2 : S) * T = 1 + (2 : S) * U := by
    rw [hTU, mul_add, hr]
    noncomm_ring
  have habs : T + 1 = 1 := square_absorption h
  have hthree : (3 : S) * T = (2 : S) * T := by
    calc
      _ = T + (2 : S) * T := by noncomm_ring
      _ = T + (1 + (2 : S) * U) := by rw [htwo]
      _ = (T + 1) + (2 : S) * U := by noncomm_ring
      _ = 1 + (2 : S) * U := by rw [habs]
      _ = (2 : S) * T := htwo.symm
  have hfour : (4 : S) * T = (2 : S) * T := by
    calc
      _ = (3 : S) * T + T := by noncomm_ring
      _ = (2 : S) * T + T := by rw [hthree]
      _ = (3 : S) * T := by noncomm_ring
      _ = (2 : S) * T := hthree
  have hcollapse : (2 : S) * T = T := by
    calc
      _ = ((4 : S) * T) * (a * b) := by
        calc
          _ = ((2 : S) * T) * ((2 : S) * (a * b)) := by rw [hr, mul_one]
          _ = _ := by noncomm_ring
      _ = ((2 : S) * T) * (a * b) := by rw [hfour]
      _ = T * ((2 : S) * (a * b)) := by noncomm_ring
      _ = T := by rw [hr, mul_one]
  have hw : W ((2 : S) * T) = 4 * W T := by simpa using scale_d h T
  rw [hcollapse] at hw
  exact hf T (by linarith)

/-- A destructive pair commutes even in the ambient noncommutative semiring. -/
theorem generators_commute_of_square_sum_zero {a b : S}
    (ht : a + b = 1) (hz : a ^ 2 + b ^ 2 = 0) : a * b = b * a := by
  have ha : a ^ 2 + a * b = a := by
    calc
      _ = a * (a + b) := by noncomm_ring
      _ = a := by rw [ht, mul_one]
  have hb : a ^ 2 + b * a = a := by
    calc
      _ = (a + b) * a := by noncomm_ring
      _ = a := by rw [ht, one_mul]
  calc
    _ = (a ^ 2 + b ^ 2) + a * b := by rw [hz, zero_add]
    _ = (a ^ 2 + a * b) + b ^ 2 := by noncomm_ring
    _ = a + b ^ 2 := by rw [ha]
    _ = (a ^ 2 + b * a) + b ^ 2 := by rw [hb]
    _ = (a ^ 2 + b ^ 2) + b * a := by noncomm_ring
    _ = b * a := by rw [hz, zero_add]

/-- This is an explicit additive negative-one witness, derived after destructive closure. -/
theorem negative_one_of_faithful {a b : S} {W : S → ℝ}
    (h : Laws a b 2 W) (hf : ∀ x, W x = 0 → x = 0) :
    (4 : S) * a ^ 4 + 1 = 0 := by
  have hr : (2 : S) * (a * b) = 1 := by simpa using h.reciprocal
  have hz := square_sum_zero_of_faithful h hf
  have hc := generators_commute_of_square_sum_zero h.transparent hz
  have hab : (a * b) * (a * b) = a ^ 2 * b ^ 2 := by
    calc
      _ = a * (b * a) * b := by noncomm_ring
      _ = a * (a * b) * b := by rw [← hc]
      _ = a ^ 2 * b ^ 2 := by noncomm_ring
  have hu : (4 : S) * (a ^ 2 * b ^ 2) = 1 := by
    calc
      _ = (4 : S) * ((a * b) * (a * b)) := by rw [hab]
      _ = ((2 : S) * (a * b)) * ((2 : S) * (a * b)) := by noncomm_ring
      _ = 1 := by simp only [hr, one_mul]
  calc
    _ = (4 : S) * a ^ 4 + (4 : S) * (a ^ 2 * b ^ 2) := by rw [hu]
    _ = ((4 : S) * a ^ 2) * (a ^ 2 + b ^ 2) := by noncomm_ring
    _ = 0 := by rw [hz, mul_zero]

/-- Every element has an additive inverse once the explicit negative-one witness exists. -/
theorem additive_inverse_exists_of_faithful {a b : S} {W : S → ℝ}
    (h : Laws a b 2 W) (hf : ∀ x, W x = 0 → x = 0) (x : S) :
    ∃ y : S, x + y = 0 := by
  refine ⟨((4 : S) * a ^ 4) * x, ?_⟩
  calc
    _ = ((4 : S) * a ^ 4 + 1) * x := by noncomm_ring
    _ = 0 := by rw [negative_one_of_faithful h hf, zero_mul]

/-- Sign and finite contrast select d=2. Faithfulness then supplies destructive closure. -/
theorem selected_destructive {a b : S} {d : ℕ} {W : S → ℝ}
    (h : Laws a b d W) (hs : UniformMixedSign a b W)
    (hc : W ((2 : S) * a) ≠ W 1) (hf : ∀ x, W x = 0 → x = 0) :
    d = 2 ∧ a ^ 2 + b ^ 2 = 0 ∧ (4 : S) * a ^ 4 + 1 = 0 := by
  have hd := (quadratic_of_finite_contrast h hs hc).1
  subst d
  exact ⟨rfl, square_sum_zero_of_faithful h hf, negative_one_of_faithful h hf⟩

/-- A cubic destructive relation yields reciprocal cross without commutativity. -/
theorem cubic_reciprocal_noncommutative {a b : S} (ht : a + b = 1) (hc : a ^ 3 + b ^ 3 = 0) :
    (3 : S) * (a * b) = 1 := by
  have ha2 : a ^ 2 + a * b = a := by
    calc
      _ = a * (a + b) := by noncomm_ring
      _ = a := by rw [ht, mul_one]
  have hb2 : a * b + b ^ 2 = b := by
    calc
      _ = (a + b) * b := by noncomm_ring
      _ = b := by rw [ht, one_mul]
  have ha3 : a ^ 3 + a ^ 2 * b = a ^ 2 := by
    calc
      _ = a ^ 2 * (a + b) := by noncomm_ring
      _ = a ^ 2 := by rw [ht, mul_one]
  have hb3 : a * b ^ 2 + b ^ 3 = b ^ 2 := by
    calc
      _ = (a + b) * b ^ 2 := by noncomm_ring
      _ = b ^ 2 := by rw [ht, one_mul]
  have hab : a ^ 2 * b + a * b ^ 2 = a * b := by
    calc
      _ = a * ((a + b) * b) := by noncomm_ring
      _ = a * b := by rw [ht, one_mul]
  have hT : a ^ 2 + b ^ 2 = a * b := by
    calc
      _ = (a ^ 3 + a ^ 2 * b) + (a * b ^ 2 + b ^ 3) := by rw [ha3, hb3]
      _ = (a ^ 3 + b ^ 3) + (a ^ 2 * b + a * b ^ 2) := by noncomm_ring
      _ = a * b := by rw [hc, zero_add, hab]
  calc
    _ = (a ^ 2 + b ^ 2) + (2 : S) * (a * b) := by rw [hT]; noncomm_ring
    _ = (a ^ 2 + a * b) + (a * b + b ^ 2) := by noncomm_ring
    _ = 1 := by rw [ha2, hb2, ht]

section Commutative

variable [CommSemiring S]

/-- The cubic relator supplies reciprocal cross 3. Remaining readout laws are separate. -/
theorem cubic_reciprocal {a b : S} (ht : a + b = 1) (hc : a ^ 3 + b ^ 3 = 0) :
    (3 : S) * (a * b) = 1 := by
  exact cubic_reciprocal_noncommutative ht hc

end Commutative

end IDT.QMClosure.SemiringReciprocalCrossClassification
