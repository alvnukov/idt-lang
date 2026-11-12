import Proofs.QMClosure.TwoPortConservationPairing
import Proofs.QMClosure.TransparentSurjectiveMixingGroup
import Mathlib.Data.Real.Archimedean

/-!
# Nonnegative quadratic readout from transparent surjective mixing

The main theorem derives its symmetric biadditive pairing from full two-input
conservation. Both branch coverages and first-axis recovery
remain explicit. Carrier addition and zero are the supplied monoid operations.

The proof uses finite positive words and Archimedean estimates in the real
codomain. Every inverse of a branch used below is an existential right-preimage.
-/

noncomputable section

namespace IDT.QMClosure.SurjectiveMixingQuadraticReadout

open TwoPortConservationPairing

section Group

variable {V : Type*} [AddCommGroup V]

/-- A diagonal of a real biadditive pairing. -/
def diagonal (B : V →+ V →+ ℝ) (x : V) : ℝ := B x x

namespace Diagonal

variable (B : V →+ V →+ ℝ)

@[simp] theorem zero : diagonal B 0 = 0 := by simp [diagonal]

@[simp] theorem neg (x : V) : diagonal B (-x) = diagonal B x := by
  simp [diagonal]

theorem add (symmetric : ∀ x y, B x y = B y x) (x y : V) :
    diagonal B (x + y) = diagonal B x + 2 * B x y + diagonal B y := by
  simp only [diagonal, map_add, AddMonoidHom.add_apply]
  rw [symmetric y x]
  ring

theorem sub (symmetric : ∀ x y, B x y = B y x) (x y : V) :
    diagonal B (x - y) = diagonal B x - 2 * B x y + diagonal B y := by
  rw [sub_eq_add_neg, add B symmetric]
  simp only [map_neg, neg B]
  ring

theorem double (symmetric : ∀ x y, B x y = B y x) (x : V) : diagonal B (x + x) = 4 * diagonal B x := by
  rw [add B symmetric]
  dsimp only [diagonal]
  ring

theorem parallelogram (symmetric : ∀ x y, B x y = B y x) (x y : V) :
    diagonal B (x + y) + diagonal B (x - y) =
      2 * diagonal B x + 2 * diagonal B y := by
  rw [add B symmetric, sub B symmetric]
  ring

theorem nsmul_left (n : ℕ) (x y : V) :
    B (n • x) y = (n : ℝ) * B x y := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [succ_nsmul, map_add, AddMonoidHom.add_apply, ih]
      push_cast
      ring

theorem nsmul_right (symmetric : ∀ x y, B x y = B y x) (n : ℕ) (x y : V) :
    B x (n • y) = (n : ℝ) * B x y := by
  rw [symmetric x (n • y), nsmul_left B, symmetric y x]

theorem nsmul (symmetric : ∀ x y, B x y = B y x) (n : ℕ) (x : V) :
    diagonal B (n • x) = (n : ℝ) ^ 2 * diagonal B x := by
  dsimp only [diagonal]
  rw [nsmul_left B, nsmul_right B symmetric]
  ring

theorem zsmul (symmetric : ∀ x y, B x y = B y x) (n : ℤ) (x : V) :
    diagonal B (n • x) = (n : ℝ) ^ 2 * diagonal B x := by
  have left (x y : V) : B (n • x) y = (n : ℝ) * B x y := by
    simp [zsmul_eq_mul]
  have right (x y : V) : B x (n • y) = (n : ℝ) * B x y := by
    rw [symmetric x (n • y), left, symmetric y x]
  dsimp only [diagonal]
  rw [left, right]
  ring

theorem add_le (symmetric : ∀ x y, B x y = B y x)
    (nonnegative : ∀ x, 0 ≤ diagonal B x) (x y : V) :
    diagonal B (x + y) ≤ 2 * diagonal B x + 2 * diagonal B y := by
  have hp := nonnegative (x - y)
  rw [sub B symmetric] at hp
  rw [add B symmetric]
  linarith

end Diagonal

private theorem power_apply_succ (a : AddMonoid.End V) (n : ℕ) (x : V) :
    (a ^ (n + 1)) x = a ((a ^ n) x) := by
  rw [pow_succ']
  rfl

private theorem power_commute_apply (a b : AddMonoid.End V)
    (commute : Commute a b) (n : ℕ) (x : V) :
    (a ^ n) (b x) = b ((a ^ n) x) := by
  have h := congrArg (fun f : AddMonoid.End V => f x) (commute.pow_left n).eq
  exact h

/-- Finite telescoping, with the last endpoint counted n+1 times. -/
theorem endpoint_bound (B : V →+ V →+ ℝ)
    (nonnegative : ∀ x, 0 ≤ diagonal B x)
    (a b : AddMonoid.End V) (commute : Commute a b)
    (column : ∀ x, diagonal B (a x) + diagonal B (b x) = diagonal B x)
    (u : V) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * diagonal B ((a ^ n) (b u)) ≤ diagonal B u := by
  have contract (x : V) : diagonal B (a x) ≤ diagonal B x := by
    have h := column x
    linarith [nonnegative (b x)]
  have strong : ∀ n : ℕ,
      diagonal B ((a ^ (n + 1)) u) +
        ((n + 1 : ℕ) : ℝ) * diagonal B ((a ^ n) (b u)) ≤ diagonal B u := by
    intro n
    induction n with
    | zero =>
        simpa using (le_of_eq (column u))
    | succ n ih =>
        have hc := column ((a ^ (n + 1)) u)
        rw [← power_apply_succ a (n + 1) u,
          ← power_commute_apply a b commute (n + 1) u] at hc
        have hmono := contract ((a ^ n) (b u))
        rw [← power_apply_succ a n (b u)] at hmono
        have hn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
        have hm := mul_le_mul_of_nonneg_left hmono hn
        push_cast at ih hc hm ⊢
        linarith
  have hn := nonnegative ((a ^ (n + 1)) u)
  linarith [strong n]

/-- Endpoint decay uses only a right-preimage under the opposite branch. -/
theorem endpoint_bound_of_preimage (B : V →+ V →+ ℝ)
    (nonnegative : ∀ x, 0 ≤ diagonal B x)
    (a b : AddMonoid.End V) (commute : Commute a b)
    (column : ∀ x, diagonal B (a x) + diagonal B (b x) = diagonal B x)
    (x u : V) (preimage : b u = x) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * diagonal B ((a ^ n) x) ≤ diagonal B u := by
  simpa only [preimage] using endpoint_bound B nonnegative a b commute column u n

/-- The two pure endpoint words at dyadic word length. -/
def residualWord (a b : AddMonoid.End V) (n : ℕ) : AddMonoid.End V :=
  a ^ (2 ^ n) + b ^ (2 ^ n)

/-- A finite positive-word witness for the interior binomial half.
No division of a carrier element or natural coefficient is used. -/
def halfWord (a b : AddMonoid.End V) : ℕ → AddMonoid.End V
  | 0 => 0
  | n + 1 => halfWord a b n + residualWord a b n * halfWord a b n +
      a ^ (2 ^ n) * b ^ (2 ^ n)

private theorem residualWord_square (a b : AddMonoid.End V)
    (commute : Commute a b) (n : ℕ) :
    residualWord a b n * residualWord a b n =
      residualWord a b (n + 1) + 2 • (a ^ (2 ^ n) * b ^ (2 ^ n)) := by
  have hn : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
    rw [pow_succ]
    omega
  have hc : b ^ (2 ^ n) * a ^ (2 ^ n) = a ^ (2 ^ n) * b ^ (2 ^ n) :=
    (commute.pow_pow _ _).eq.symm
  simp only [residualWord, hn, pow_add, add_mul, mul_add, hc, two_nsmul]
  abel

/-- Exact positive-word approximate halving identity at every finite stage. -/
theorem halfWord_identity (a b : AddMonoid.End V)
    (transparent : a + b = 1) (commute : Commute a b) (n : ℕ) :
    2 • halfWord a b n + residualWord a b n = 1 := by
  induction n with
  | zero => simpa [halfWord, residualWord] using transparent
  | succ n ih =>
      have hs := residualWord_square a b commute n
      calc
        2 • halfWord a b (n + 1) + residualWord a b (n + 1) =
            2 • halfWord a b n +
              (2 • (residualWord a b n * halfWord a b n) +
                (2 • (a ^ (2 ^ n) * b ^ (2 ^ n)) + residualWord a b (n + 1))) := by
          simp only [halfWord, two_nsmul]
          abel
        _ = 2 • halfWord a b n +
              (2 • (residualWord a b n * halfWord a b n) +
                residualWord a b n * residualWord a b n) := by
          rw [hs]
          abel
        _ = 2 • halfWord a b n +
              residualWord a b n * (2 • halfWord a b n + residualWord a b n) := by
          simp only [two_nsmul, mul_add]
        _ = 2 • halfWord a b n + residualWord a b n := by simp only [ih, mul_one]
        _ = 1 := ih

theorem halfWord_apply (a b : AddMonoid.End V)
    (transparent : a + b = 1) (commute : Commute a b) (n : ℕ) (x : V) :
    x = halfWord a b n x + halfWord a b n x + residualWord a b n x := by
  have h := congrArg (fun f : AddMonoid.End V => f x)
    (halfWord_identity a b transparent commute n)
  simpa only [two_nsmul, AddMonoidHom.add_apply, AddMonoid.End.one_apply] using h.symm

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 0 < 2 ^ n := by positivity
      rw [pow_succ]
      omega

/-- The residual energy can be made arbitrarily small in the real codomain. -/
theorem residual_arbitrarily_small (B : V →+ V →+ ℝ)
    (symmetric : ∀ x y, B x y = B y x)
    (nonnegative : ∀ x, 0 ≤ diagonal B x)
    (a b : AddMonoid.End V) (commute : Commute a b)
    (ontoA : Function.Surjective a) (ontoB : Function.Surjective b)
    (column : ∀ x, diagonal B (a x) + diagonal B (b x) = diagonal B x)
    (x : V) (δ : ℝ) (positive : 0 < δ) :
    ∃ n : ℕ, diagonal B (residualWord a b n x) < δ := by
  obtain ⟨u, hu⟩ := ontoB x
  obtain ⟨v, hv⟩ := ontoA x
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (diagonal B u + diagonal B v) / δ)
  have hbig : 2 * (diagonal B u + diagonal B v) < (n : ℝ) * δ :=
    (div_lt_iff₀ positive).mp hn
  have ha := endpoint_bound_of_preimage B nonnegative a b commute column x u hu (2 ^ n)
  have column' (z : V) : diagonal B (b z) + diagonal B (a z) = diagonal B z := by
    rw [add_comm]
    exact column z
  have hb := endpoint_bound_of_preimage B nonnegative b a commute.symm column'
    x v hv (2 ^ n)
  have hr := Diagonal.add_le B symmetric nonnegative ((a ^ (2 ^ n)) x)
    ((b ^ (2 ^ n)) x)
  change diagonal B (residualWord a b n x) ≤
    2 * diagonal B ((a ^ (2 ^ n)) x) + 2 * diagonal B ((b ^ (2 ^ n)) x) at hr
  have hN : (0 : ℝ) ≤ ((2 ^ n + 1 : ℕ) : ℝ) := by positivity
  have hs := mul_le_mul_of_nonneg_left hr hN
  have hnN : (n : ℝ) ≤ ((2 ^ n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_trans (nat_le_two_pow n) (Nat.le_succ _)
  have hh := mul_le_mul_of_nonneg_right hnN (le_of_lt positive)
  refine ⟨n, ?_⟩
  by_contra h
  have hδ : δ ≤ diagonal B (residualWord a b n x) := le_of_not_gt h
  have hm := mul_le_mul_of_nonneg_left hδ hN
  nlinarith

/-- Derived approximate halving, quantified solely through real error bounds. -/
theorem approximate_halving (B : V →+ V →+ ℝ)
    (symmetric : ∀ x y, B x y = B y x)
    (nonnegative : ∀ x, 0 ≤ diagonal B x)
    (a b : AddMonoid.End V) (transparent : a + b = 1) (commute : Commute a b)
    (ontoA : Function.Surjective a) (ontoB : Function.Surjective b)
    (column : ∀ x, diagonal B (a x) + diagonal B (b x) = diagonal B x)
    (x : V) (ε : ℝ) (positive : 0 < ε) :
    ∃ y r : V, x = y + y + r ∧ diagonal B r < ε ∧
      |4 * diagonal B y - diagonal B x| < ε := by
  let η : ℝ := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (diagonal B x / η)
  let M : ℕ := m + 1
  have hM : 0 < (M : ℝ) := by dsimp [M]; positivity
  have hmM : (m : ℝ) < (M : ℝ) := by
    dsimp [M]
    exact_mod_cast Nat.lt_succ_self m
  have hsmall : diagonal B x < η * (M : ℝ) := by
    have h := (div_lt_iff₀ hη).mp hm
    nlinarith
  let δ : ℝ := min η (η / (M : ℝ))
  have hδ : 0 < δ := lt_min hη (div_pos hη hM)
  obtain ⟨n, hn⟩ := residual_arbitrarily_small B symmetric nonnegative
    a b commute ontoA ontoB column x δ hδ
  let y : V := halfWord a b n x
  let r : V := residualWord a b n x
  have hqr : diagonal B r < η := lt_of_lt_of_le hn (min_le_left _ _)
  have hqrM : (M : ℝ) * diagonal B r < η := by
    have ht : diagonal B r < η / (M : ℝ) := lt_of_lt_of_le hn (min_le_right _ _)
    have hh := (lt_div_iff₀ hM).mp ht
    nlinarith
  have hplus := nonnegative (x + M • r)
  have hminus := nonnegative (x - M • r)
  rw [Diagonal.add B symmetric, Diagonal.nsmul B symmetric,
    Diagonal.nsmul_right B symmetric] at hplus
  rw [Diagonal.sub B symmetric, Diagonal.nsmul B symmetric,
    Diagonal.nsmul_right B symmetric] at hminus
  have hscaled := mul_lt_mul_of_pos_left hqrM hM
  have hcross : -η < B x r ∧ B x r < η := by
    constructor
    · by_contra h
      have he : B x r ≤ -η := le_of_not_gt h
      have hh := mul_le_mul_of_nonneg_left he (le_of_lt hM)
      nlinarith
    · by_contra h
      have he : η ≤ B x r := le_of_not_gt h
      have hh := mul_le_mul_of_nonneg_left he (le_of_lt hM)
      nlinarith
  have hx : x = y + y + r := halfWord_apply a b transparent commute n x
  have harg : x - r = y + y := by rw [hx]; abel
  have hq : 4 * diagonal B y = diagonal B x - 2 * B x r + diagonal B r := by
    have h := Diagonal.sub B symmetric x r
    rw [harg, Diagonal.double B symmetric] at h
    exact h
  refine ⟨y, r, hx, ?_, abs_lt.mpr ⟨?_, ?_⟩⟩
  · dsimp [η] at hqr
    linarith
  · have hr0 := nonnegative r
    dsimp [η] at hcross
    linarith
  · dsimp [η] at hqr hcross
    linarith

/-- A global domination constant improves by a factor of two.
The bound is quantified over every carrier element before x is fixed. -/
theorem improve_global_bound (B : V →+ V →+ ℝ)
    (symmetric : ∀ x y, B x y = B y x)
    (nonnegative : ∀ x, 0 ≤ diagonal B x)
    (a b : AddMonoid.End V) (transparent : a + b = 1) (commute : Commute a b)
    (ontoA : Function.Surjective a) (ontoB : Function.Surjective b)
    (column : ∀ x, diagonal B (a x) + diagonal B (b x) = diagonal B x)
    (L : V →+ ℝ) (C : ℝ) (constant_nonnegative : 0 ≤ C)
    (bound : ∀ z, |L z| ≤ C * diagonal B z) :
    ∀ x, |L x| ≤ (C / 2) * diagonal B x := by
  intro x
  by_contra h
  have hgap : 0 < |L x| - (C / 2) * diagonal B x := by linarith
  let ε : ℝ := (|L x| - (C / 2) * diagonal B x) / (4 * (C + 1))
  have hden : 0 < 4 * (C + 1) := by linarith
  have hε : 0 < ε := div_pos hgap hden
  have heq : 4 * (C + 1) * ε = |L x| - (C / 2) * diagonal B x := by
    dsimp [ε]
    have hC : C + 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp [hC]
  obtain ⟨y, r, hx, hr, hq⟩ := approximate_halving B symmetric nonnegative
    a b transparent commute ontoA ontoB column x ε hε
  have triangle : |L x| ≤ |L y| + |L y| + |L r| := by
    calc
      |L x| = |L y + L y + L r| := by rw [hx]; simp only [map_add]
      _ ≤ |L y + L y| + |L r| := abs_add_le _ _
      _ ≤ |L y| + |L y| + |L r| := add_le_add (abs_add_le _ _) le_rfl
  have hupper : 4 * diagonal B y ≤ diagonal B x + ε := by
    have ht := (abs_lt.mp hq).2
    linarith
  have hyC := mul_le_mul_of_nonneg_left hupper constant_nonnegative
  have hrC := mul_le_mul_of_nonneg_left (le_of_lt hr) constant_nonnegative
  have hprod : 0 ≤ C * ε := mul_nonneg constant_nonnegative (le_of_lt hε)
  have bound_y := bound y
  have bound_r := bound r
  nlinarith

/-- Standalone additive-remainder rigidity for a nonnegative biadditive diagonal. -/
theorem additive_remainder_zero (B : V →+ V →+ ℝ)
    (symmetric : ∀ x y, B x y = B y x)
    (nonnegative : ∀ x, 0 ≤ diagonal B x)
    (a b : AddMonoid.End V) (transparent : a + b = 1) (commute : Commute a b)
    (ontoA : Function.Surjective a) (ontoB : Function.Surjective b)
    (column : ∀ x, diagonal B (a x) + diagonal B (b x) = diagonal B x)
    (L : V →+ ℝ) (dominated : ∀ x, |L x| ≤ diagonal B x) :
    ∀ x, L x = 0 := by
  have bounds : ∀ n : ℕ, ∀ z, |L z| ≤ diagonal B z / (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simpa using dominated
    | succ n ih =>
        have cn : 0 ≤ 1 / (2 : ℝ) ^ n := by positivity
        have old : ∀ z, |L z| ≤ (1 / (2 : ℝ) ^ n) * diagonal B z := by
          intro z
          simpa only [div_eq_mul_inv, one_mul, mul_comm] using ih z
        have next := improve_global_bound B symmetric nonnegative a b transparent
          commute ontoA ontoB column L (1 / (2 : ℝ) ^ n) cn old
        intro z
        calc
          |L z| ≤ ((1 / (2 : ℝ) ^ n) / 2) * diagonal B z := next z
          _ = diagonal B z / (2 : ℝ) ^ (n + 1) := by
            rw [pow_succ]
            field_simp
  intro x
  apply abs_eq_zero.mp
  by_contra h
  have hpos : 0 < |L x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h)
  obtain ⟨n, hn⟩ := exists_nat_gt (diagonal B x / |L x|)
  have hbig : diagonal B x < (n : ℝ) * |L x| :=
    (div_lt_iff₀ hpos).mp hn
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hsmall := (le_div_iff₀ hpow).mp (bounds n x)
  have hnat : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast nat_le_two_pow n
  have hh := mul_le_mul_of_nonneg_right hnat (abs_nonneg (L x))
  nlinarith

/-- Conservation supplies the pairing and positivity kills its additive remainder.
All helper proof parameters above are derived inside this theorem. -/
theorem reconstruct_group (a b : AddMonoid.End V)
    (transparent : a + b = 1)
    (ontoA : Function.Surjective a) (ontoB : Function.Surjective b)
    (axis : FirstAxisReachable a b b a)
    (W : V → ℝ) (vacuum : W 0 = 0) (nonnegative : ∀ x, 0 ≤ W x)
    (conserve : ∀ x y, W (a x + b y) + W (b x + a y) = W x + W y) :
    ∃ B : V →+ V →+ ℝ,
      (∀ x y, B x y = B y x) ∧ (∀ x, W x = B x x) := by
  have independent := base_independent_of_conservation a b b a ontoA ontoB axis W conserve
  let B : V →+ V →+ ℝ := {
    toFun := fun x => Polarization.rightAddHom independent x
    map_zero' := by
      ext y
      exact Polarization.zero_left W y
    map_add' := by
      intro x y
      ext z
      exact Polarization.add_left independent x y z }
  let L : V →+ ℝ := remainderHom W independent
  have hsym : ∀ x y, B x y = B y x := Polarization.symmetric W
  have decompose (x : V) : W x = diagonal B x + L x := by
    have h := readout_decomposition W x
    rw [vacuum, zero_add] at h
    exact h
  have average (x : V) : diagonal B x = (W x + W (-x)) / 2 := by
    have hp := decompose x
    have hm := decompose (-x)
    rw [Diagonal.neg B, map_neg] at hm
    linarith
  have qpositive (x : V) : 0 ≤ diagonal B x := by
    rw [average]
    exact div_nonneg (add_nonneg (nonnegative x) (nonnegative (-x))) (by norm_num)
  have dominated (x : V) : |L x| ≤ diagonal B x := by
    have hp := nonnegative x
    have hm := nonnegative (-x)
    rw [decompose x] at hp
    rw [decompose (-x), Diagonal.neg B, map_neg] at hm
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have qconserve (x y : V) :
      diagonal B (a x + b y) + diagonal B (b x + a y) = diagonal B x + diagonal B y := by
    have hp := conserve x y
    have hm := conserve (-x) (-y)
    have ha : a (-x) + b (-y) = -(a x + b y) := by simp [add_comm]
    have hb : b (-x) + a (-y) = -(b x + a y) := by simp [add_comm]
    rw [ha, hb] at hm
    rw [average, average, average, average]
    linarith
  have column (x : V) : diagonal B (a x) + diagonal B (b x) = diagonal B x := by
    simpa only [map_zero, add_zero, Diagonal.zero, add_zero] using qconserve x 0
  have pointwise (x : V) : a x + b x = x :=
    congrArg (fun f : AddMonoid.End V => f x) transparent
  have commute : Commute a b := by
    apply AddMonoidHom.ext
    intro x
    have ha := congrArg a (pointwise x)
    simp only [map_add] at ha
    have hb := pointwise (a x)
    exact add_left_cancel (ha.trans hb.symm)
  have remainder_zero := additive_remainder_zero B hsym qpositive a b transparent
    commute ontoA ontoB column L dominated
  refine ⟨B, hsym, ?_⟩
  intro x
  simpa only [remainder_zero, add_zero, diagonal] using decompose x

/-- Evenness, parallelogram and integer-square repetition from the derived pairing. -/
theorem readout_identities (W : V → ℝ)
    (quadratic : ∃ B : V →+ V →+ ℝ,
      (∀ x y, B x y = B y x) ∧ (∀ x, W x = B x x)) :
    (∀ x, W (-x) = W x) ∧
      (∀ x y, W (x + y) + W (x - y) = 2 * W x + 2 * W y) ∧
      (∀ n : ℤ, ∀ x, W (n • x) = (n : ℝ) ^ 2 * W x) := by
  obtain ⟨B, symmetric, diagonal_eq⟩ := quadratic
  have heq (x : V) : W x = diagonal B x := diagonal_eq x
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp only [heq, Diagonal.neg]
  · intro x y
    simp only [heq]
    exact Diagonal.parallelogram B symmetric x y
  · intro n x
    simp only [heq]
    exact Diagonal.zsmul B symmetric n x

/-- Orthogonality follows from transparent column conservation. -/
theorem branch_orthogonality (B : V →+ V →+ ℝ)
    (symmetric : ∀ x y, B x y = B y x)
    (a b : AddMonoid.End V) (transparent : a + b = 1)
    (column : ∀ x, diagonal B (a x) + diagonal B (b x) = diagonal B x) (x : V) :
    B (a x) (b x) = 0 := by
  have ht : a x + b x = x := congrArg (fun f : AddMonoid.End V => f x) transparent
  have h := Diagonal.add B symmetric (a x) (b x)
  rw [ht] at h
  linarith [column x]

end Group

section Monoid

variable {V : Type*} [AddCommMonoid V]

/-- End-to-end reconstruction on the original carrier and original addition.
The additive-group structure is constructed internally from the recovery gate. -/
theorem reconstruct (G : TransparentSurjectiveMixingGroup.Gate V)
    (W : V → ℝ) (vacuum : W 0 = 0) (nonnegative : ∀ x, 0 ≤ W x)
    (conserve : ∀ x y,
      W (G.a x + G.b y) + W (G.b x + G.a y) = W x + W y) :
    ∃ B : V →+ V →+ ℝ,
      (∀ x y, B x y = B y x) ∧ (∀ x, W x = B x x) := by
  letI : AddCommGroup V := G.additiveGroup
  exact reconstruct_group G.a G.b G.transparent G.ontoA G.ontoB G.axis
    W vacuum nonnegative conserve

/-- Expanded end-to-end signature, with every recovery and readout premise visible. -/
theorem reconstruct_of_first_axis (a b : AddMonoid.End V)
    (transparent : a + b = 1)
    (ontoA : Function.Surjective a) (ontoB : Function.Surjective b)
    (axis : FirstAxisReachable a b b a)
    (W : V → ℝ) (vacuum : W 0 = 0) (nonnegative : ∀ x, 0 ≤ W x)
    (conserve : ∀ x y, W (a x + b y) + W (b x + a y) = W x + W y) :
    ∃ B : V →+ V →+ ℝ,
      (∀ x y, B x y = B y x) ∧ (∀ x, W x = B x x) := by
  let G : TransparentSurjectiveMixingGroup.Gate V := {
    a := a
    b := b
    transparent := transparent
    ontoA := ontoA
    ontoB := ontoB
    axis := axis }
  exact reconstruct G W vacuum nonnegative conserve

/-- Natural count-square scaling uses the original supplied nsmul operation. -/
theorem count_square (G : TransparentSurjectiveMixingGroup.Gate V)
    (W : V → ℝ) (vacuum : W 0 = 0) (nonnegative : ∀ x, 0 ≤ W x)
    (conserve : ∀ x y,
      W (G.a x + G.b y) + W (G.b x + G.a y) = W x + W y)
    (n : ℕ) (x : V) : W (n • x) = (n : ℝ) ^ 2 * W x := by
  obtain ⟨B, symmetric, diagonal_eq⟩ := reconstruct G W vacuum nonnegative conserve
  letI : AddCommGroup V := G.additiveGroup
  have h := Diagonal.nsmul B symmetric n x
  simpa only [diagonal, ← diagonal_eq] using h

end Monoid

end IDT.QMClosure.SurjectiveMixingQuadraticReadout
