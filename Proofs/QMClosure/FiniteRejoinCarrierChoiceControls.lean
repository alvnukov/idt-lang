import Proofs.QMClosure.FiniteRejoinQuadraticReadoutControls
import Proofs.QMClosure.CubicRejoinReadoutCountermodel

/-!
# Finite-rejoin and original-carrier controls

The first complex model has transparent invertible branches, a surjective
symmetric two-port map, and universal norm-square conservation. Its branch
powers fail to rejoin at every positive exponent. Its readout is quadratic.
Its unequal branch gains and nonzero same-branch response locate the role of
the positive finite-rejoin premise in the stronger reconstruction package.

The second model uses the entire additive carrier `ℂ × ℂ`, a period-twelve
rejoin, a surjective two-port map, and a normalized conserved readout that sees
only the first coordinate. It meets the complete reconstruction contract.
The original carrier still has a nonzero same-branch output and unequal
fourth powers in the invisible second coordinate. These are original-carrier
claims. The observable quotient has a different equality relation.

The complex coordinates are concrete model choices. These controls supply no
physical-origin, scalar-field uniqueness, or full-QM conclusion.
-/

noncomputable section

namespace IDT.QMClosure.FiniteRejoinCarrierChoiceControls

open FiniteRejoinReversibleQuadraticReadout
open scoped ComplexConjugate

open FiniteRejoinQuadraticReadoutControls

/-- Scalar composition powers, stated explicitly for the additive endomorphism. -/
theorem scalarEnd_pow_apply (c : ℂ) (n : ℕ) (z : ℂ) :
    (CanonicalComplex.scalarEnd c ^ n) z = c ^ n * z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change c * ((CanonicalComplex.scalarEnd c ^ n) z) = c ^ (n + 1) * z
      rw [ih]
      ring

/-- The two-port inverse exists whenever the transparent scalar difference is
nonzero. This statement quantifies over both output coordinates. -/
theorem scalar_twoPort_surjective (c d : ℂ) (hsum : c + d = 1)
    (hdifference : c - d ≠ 0) :
    Function.Surjective (twoPort (CanonicalComplex.scalarEnd c) (CanonicalComplex.scalarEnd d)) := by
  intro p
  refine ⟨((c * p.1 - d * p.2) / (c - d),
    (c * p.2 - d * p.1) / (c - d)), ?_⟩
  apply Prod.ext
  · change c * ((c * p.1 - d * p.2) / (c - d)) +
        d * ((c * p.2 - d * p.1) / (c - d)) = p.1
    calc
      _ = ((c + d) * (c - d) * p.1) / (c - d) := by ring
      _ = p.1 := by rw [hsum]; simp [hdifference]
  · change d * ((c * p.1 - d * p.2) / (c - d)) +
        c * ((c * p.2 - d * p.1) / (c - d)) = p.2
    calc
      _ = ((c + d) * (c - d) * p.2) / (c - d) := by ring
      _ = p.2 := by rw [hsum]; simp [hdifference]

namespace NoFiniteRejoin

/-- The unequal-gain first branch. -/
def alpha : ℂ := ⟨4 / 5, 2 / 5⟩

/-- The unequal-gain second branch. -/
def beta : ℂ := ⟨1 / 5, -(2 / 5)⟩

def A : AddMonoid.End ℂ := CanonicalComplex.scalarEnd alpha

def B : AddMonoid.End ℂ := CanonicalComplex.scalarEnd beta

def same : AddMonoid.End ℂ := A * A + B * B

def cross : AddMonoid.End ℂ := A * B + A * B

theorem coefficient_sum : alpha + beta = 1 := by
  apply Complex.ext <;> norm_num [alpha, beta]

theorem coefficient_norms :
    Complex.normSq alpha = 4 / 5 ∧ Complex.normSq beta = 1 / 5 ∧
    Complex.normSq (alpha - beta) = 1 := by
  norm_num [Complex.normSq_apply, alpha, beta]

/-- Exact scalar conditions responsible for universal norm conservation. -/
theorem coefficient_orthogonality :
    (alpha * conj beta).re = 0 ∧
    Complex.normSq alpha + Complex.normSq beta = 1 := by
  constructor
  · norm_num [alpha, beta, Complex.mul_re]
  · rw [coefficient_norms.1, coefficient_norms.2.1]
    norm_num

theorem coefficient_nonzero : alpha ≠ 0 ∧ beta ≠ 0 ∧ alpha - beta ≠ 0 := by
  constructor
  · intro h
    have := coefficient_norms.1
    rw [h, Complex.normSq_zero] at this
    norm_num at this
  constructor
  · intro h
    have := coefficient_norms.2.1
    rw [h, Complex.normSq_zero] at this
    norm_num at this
  · intro h
    have := coefficient_norms.2.2
    rw [h, Complex.normSq_zero] at this
    norm_num at this

theorem transparent : A + B = 1 := by
  apply DFunLike.ext
  intro z
  change alpha * z + beta * z = z
  rw [← add_mul, coefficient_sum, one_mul]

theorem branch_invertible :
    (CanonicalComplex.scalarEnd alpha⁻¹ * A = 1 ∧ A * CanonicalComplex.scalarEnd alpha⁻¹ = 1) ∧
    (CanonicalComplex.scalarEnd beta⁻¹ * B = 1 ∧ B * CanonicalComplex.scalarEnd beta⁻¹ = 1) := by
  constructor <;> constructor <;> apply DFunLike.ext <;> intro z
  · change alpha⁻¹ * (alpha * z) = z
    simp [← mul_assoc, coefficient_nonzero.1]
  · change alpha * (alpha⁻¹ * z) = z
    simp [← mul_assoc, coefficient_nonzero.1]
  · change beta⁻¹ * (beta * z) = z
    simp [← mul_assoc, coefficient_nonzero.2.1]
  · change beta * (beta⁻¹ * z) = z
    simp [← mul_assoc, coefficient_nonzero.2.1]

theorem onto : Function.Surjective (twoPort A B) :=
  scalar_twoPort_surjective alpha beta coefficient_sum coefficient_nonzero.2.2

/-- Conservation holds for every pair of complex inputs. -/
theorem norm_conservation (x y : ℂ) :
    Complex.normSq (A x + B y) + Complex.normSq (B x + A y) =
      Complex.normSq x + Complex.normSq y := by
  change Complex.normSq (alpha * x + beta * y) +
    Complex.normSq (beta * x + alpha * y) = Complex.normSq x + Complex.normSq y
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  dsimp only [alpha, beta]
  ring

/-- The no-rejoin readout itself still satisfies the quadratic identity. -/
theorem quadratic_parallelogram (x y : ℂ) :
    Complex.normSq (x + y) + Complex.normSq (x - y) =
      2 * Complex.normSq x + 2 * Complex.normSq y := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im]
  ring

theorem branch_gains (z : ℂ) :
    Complex.normSq (A z) = (4 / 5) * Complex.normSq z ∧
    Complex.normSq (B z) = (1 / 5) * Complex.normSq z := by
  change Complex.normSq (alpha * z) = _ ∧ Complex.normSq (beta * z) = _
  constructor
  · rw [Complex.normSq_mul, coefficient_norms.1]
  · rw [Complex.normSq_mul, coefficient_norms.2.1]

private theorem power_gain_le (n : ℕ) : (1 / 5 : ℝ) ^ n ≤ (4 / 5 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ, pow_succ]
      have hnonneg : 0 ≤ (1 / 5 : ℝ) ^ n := pow_nonneg (by norm_num) n
      nlinarith

private theorem power_gain_lt (n : ℕ) (hn : 0 < n) :
    (1 / 5 : ℝ) ^ n < (4 / 5 : ℝ) ^ n := by
  cases n with
  | zero => omega
  | succ n =>
      rw [pow_succ, pow_succ]
      have hle := power_gain_le n
      have hpos : 0 < (1 / 5 : ℝ) ^ n := pow_pos (by norm_num) n
      nlinarith

/-- No positive exponent rejoins even the scalar coefficients. -/
theorem coefficient_ne_pow (n : ℕ) (hn : 0 < n) : alpha ^ n ≠ beta ^ n := by
  intro h
  have hnorm := congrArg Complex.normSq h
  have ha : Complex.normSq (alpha ^ n) = (4 / 5 : ℝ) ^ n := by
    rw [map_pow, coefficient_norms.1]
  have hb : Complex.normSq (beta ^ n) = (1 / 5 : ℝ) ^ n := by
    rw [map_pow, coefficient_norms.2.1]
  rw [ha, hb] at hnorm
  exact (ne_of_gt (power_gain_lt n hn)) hnorm

/-- Every positive finite-rejoin exponent fails on the entire carrier. -/
theorem no_finite_rejoin : ∀ n : ℕ, 0 < n → A ^ n ≠ B ^ n := by
  intro n hn h
  have hpoint := congrArg (fun f : AddMonoid.End ℂ => f 1) h
  change (CanonicalComplex.scalarEnd alpha ^ n) 1 = (CanonicalComplex.scalarEnd beta ^ n) 1 at hpoint
  rw [scalarEnd_pow_apply, scalarEnd_pow_apply, mul_one, mul_one] at hpoint
  exact coefficient_ne_pow n hn hpoint

theorem same_value : same 1 = (⟨9 / 25, 12 / 25⟩ : ℂ) := by
  change alpha * (alpha * 1) + beta * (beta * 1) = _
  apply Complex.ext <;>
    norm_num [alpha, beta, Complex.mul_re, Complex.mul_im]

theorem cross_value : cross 1 = (⟨16 / 25, -(12 / 25)⟩ : ℂ) := by
  change alpha * (beta * 1) + alpha * (beta * 1) = _
  apply Complex.ext <;>
    norm_num [alpha, beta, Complex.mul_re, Complex.mul_im]

theorem stronger_conclusions_fail :
    Complex.normSq (A 1) ≠ Complex.normSq 1 / 2 ∧
    same 1 ≠ 0 ∧ Complex.normSq (cross 1) = 16 / 25 := by
  constructor
  · rw [(branch_gains 1).1, Complex.normSq_one]
    norm_num
  constructor
  · rw [same_value]
    intro h
    have := congrArg Complex.re h
    norm_num at this
  · rw [cross_value]
    norm_num [Complex.normSq_apply]

/-- All non-rejoin laws of the core contract hold universally. -/
theorem remaining_contract :
    A + B = 1 ∧ Function.Surjective (twoPort A B) ∧
    Complex.normSq 0 = 0 ∧ (∀ z, 0 ≤ Complex.normSq z) ∧
    (∀ x y, Complex.normSq (A x + B y) + Complex.normSq (B x + A y) =
      Complex.normSq x + Complex.normSq y) ∧ Complex.normSq 1 = 1 ∧
    (∀ n : ℕ, 0 < n → A ^ n ≠ B ^ n) :=
  ⟨transparent, onto, Complex.normSq_zero, Complex.normSq_nonneg,
    norm_conservation, Complex.normSq_one, no_finite_rejoin⟩

/-- These branches cannot be the branches of any positive-period core gate. -/
theorem no_gate_with_these_branches : ¬ ∃ G : Gate ℂ, G.a = A ∧ G.b = B := by
  rintro ⟨G, ha, hb⟩
  have h := G.rejoin
  rw [ha, hb] at h
  exact no_finite_rejoin G.period G.period_pos h

end NoFiniteRejoin

namespace HiddenCubicSector

abbrev V := ℂ × ℂ

/-- Coordinatewise scalar multiplication keeps the entire original carrier. -/
def pairScalarEnd (c d : ℂ) : AddMonoid.End V where
  toFun z := (c * z.1, d * z.2)
  map_zero' := by simp
  map_add' x y := by apply Prod.ext <;> simp [mul_add]

def A : AddMonoid.End V := pairScalarEnd CanonicalComplex.alpha CubicRejoinReadoutCountermodel.zeta

def B : AddMonoid.End V := pairScalarEnd CanonicalComplex.beta (conj CubicRejoinReadoutCountermodel.zeta)

/-- Only the visible coordinate is measured. -/
def W (z : V) : ℝ := Complex.normSq z.1

def e : V := (0, 1)

def normalizedState : V := (1, 0)

theorem pairScalarEnd_pow_apply (c d : ℂ) (n : ℕ) (z : V) :
    (pairScalarEnd c d ^ n) z = (c ^ n * z.1, d ^ n * z.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change (c * ((pairScalarEnd c d ^ n) z).1,
        d * ((pairScalarEnd c d ^ n) z).2) = _
      rw [ih]
      apply Prod.ext <;> dsimp only <;> ring

theorem transparent : A + B = 1 := by
  apply DFunLike.ext
  intro z
  apply Prod.ext
  · change CanonicalComplex.alpha * z.1 + CanonicalComplex.beta * z.1 = z.1
    rw [← add_mul, CanonicalComplex.coefficient_laws.1, one_mul]
  · change CubicRejoinReadoutCountermodel.zeta * z.2 + conj CubicRejoinReadoutCountermodel.zeta * z.2 = z.2
    rw [← add_mul, CubicRejoinReadoutCountermodel.zeta_sum, one_mul]

theorem coefficient_period12 :
    CanonicalComplex.alpha ^ 12 = CanonicalComplex.beta ^ 12 ∧
    CubicRejoinReadoutCountermodel.zeta ^ 12 = conj CubicRejoinReadoutCountermodel.zeta ^ 12 := by
  constructor
  · calc
      CanonicalComplex.alpha ^ 12 = (CanonicalComplex.alpha ^ 4) ^ 3 := by rw [← pow_mul]
      _ = (CanonicalComplex.beta ^ 4) ^ 3 := by rw [CanonicalComplex.coefficient_fourth]
      _ = CanonicalComplex.beta ^ 12 := by rw [← pow_mul]
  · calc
      CubicRejoinReadoutCountermodel.zeta ^ 12 = (CubicRejoinReadoutCountermodel.zeta ^ 3) ^ 4 := by rw [← pow_mul]
      _ = (conj CubicRejoinReadoutCountermodel.zeta ^ 3) ^ 4 := by rw [CubicRejoinReadoutCountermodel.zeta_cube, CubicRejoinReadoutCountermodel.conj_zeta_cube]
      _ = conj CubicRejoinReadoutCountermodel.zeta ^ 12 := by rw [← pow_mul]

theorem rejoin : A ^ 12 = B ^ 12 := by
  apply DFunLike.ext
  intro z
  change (pairScalarEnd CanonicalComplex.alpha CubicRejoinReadoutCountermodel.zeta ^ 12) z =
    (pairScalarEnd CanonicalComplex.beta (conj CubicRejoinReadoutCountermodel.zeta) ^ 12) z
  rw [pairScalarEnd_pow_apply, pairScalarEnd_pow_apply,
    coefficient_period12.1, coefficient_period12.2]

theorem hidden_difference_nonzero : CubicRejoinReadoutCountermodel.zeta - conj CubicRejoinReadoutCountermodel.zeta ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hr := CubicRejoinReadoutCountermodel.r_pos
  simp [CubicRejoinReadoutCountermodel.zeta] at him
  linarith

/-- Both coordinate two-port maps are onto, including the unmeasured sector. -/
theorem onto : Function.Surjective (twoPort A B) := by
  intro p
  obtain ⟨u, hu⟩ := CanonicalComplex.onto (p.1.1, p.2.1)
  obtain ⟨v, hv⟩ := scalar_twoPort_surjective CubicRejoinReadoutCountermodel.zeta (conj CubicRejoinReadoutCountermodel.zeta)
    CubicRejoinReadoutCountermodel.zeta_sum hidden_difference_nonzero (p.1.2, p.2.2)
  have hu1 := congrArg Prod.fst hu
  have hu2 := congrArg Prod.snd hu
  have hv1 := congrArg Prod.fst hv
  have hv2 := congrArg Prod.snd hv
  refine ⟨((u.1, v.1), (u.2, v.2)), ?_⟩
  change ((CanonicalComplex.alpha * u.1 + CanonicalComplex.beta * u.2,
      CubicRejoinReadoutCountermodel.zeta * v.1 + conj CubicRejoinReadoutCountermodel.zeta * v.2),
    (CanonicalComplex.beta * u.1 + CanonicalComplex.alpha * u.2,
      conj CubicRejoinReadoutCountermodel.zeta * v.1 + CubicRejoinReadoutCountermodel.zeta * v.2)) = p
  exact Prod.ext (Prod.ext hu1 hv1) (Prod.ext hu2 hv2)

/-- A genuine complete period-twelve gate on the full original carrier. -/
def gate : Gate V where
  a := A
  b := B
  period := 12
  period_pos := by decide
  transparent := transparent
  rejoin := rejoin
  onto := onto

theorem vacuum : W 0 = 0 := Complex.normSq_zero

theorem nonnegative (z : V) : 0 ≤ W z := Complex.normSq_nonneg z.1

theorem normalized : W normalizedState = 1 := Complex.normSq_one

/-- The conservation statement quantifies over every pair of carrier inputs. -/
theorem conservation (x y : V) :
    W (A x + B y) + W (B x + A y) = W x + W y :=
  CanonicalComplex.norm_conservation x.1 y.1

theorem complete_readout_certificate :
    A + B = 1 ∧ A ^ 12 = B ^ 12 ∧ Function.Surjective (twoPort A B) ∧
    W 0 = 0 ∧ (∀ z, 0 ≤ W z) ∧
    (∀ x y, W (A x + B y) + W (B x + A y) = W x + W y) ∧
    W normalizedState = 1 :=
  ⟨transparent, rejoin, onto, vacuum, nonnegative, conservation, normalized⟩

theorem reconstructed : Reconstruction gate W :=
  reconstruct gate W vacuum nonnegative conservation

/-- The same-branch operator is nonzero on an unmeasured state. -/
theorem same_at_hidden_state : gate.same e = (0, -1) := by
  apply Prod.ext
  · change CanonicalComplex.alpha * (CanonicalComplex.alpha * 0) +
        CanonicalComplex.beta * (CanonicalComplex.beta * 0) = 0
    simp
  · change CubicRejoinReadoutCountermodel.zeta * (CubicRejoinReadoutCountermodel.zeta * 1) +
        conj CubicRejoinReadoutCountermodel.zeta * (conj CubicRejoinReadoutCountermodel.zeta * 1) = -1
    simpa only [mul_one, pow_two] using CubicRejoinReadoutCountermodel.zeta_sq_sum

theorem same_nonzero : gate.same e ≠ 0 := by
  rw [same_at_hidden_state]
  intro h
  have := congrArg (fun z : V => z.2) h
  norm_num at this

theorem same_readout_zero : W (gate.same e) = 0 := by
  rw [same_at_hidden_state]
  exact Complex.normSq_zero

/-- The fourth-power difference remains nonzero on the original carrier. -/
theorem fourth_difference_at_hidden_state :
    (A ^ 4 - B ^ 4) e = (0, (⟨0, -CubicRejoinReadoutCountermodel.r⟩ : ℂ)) := by
  change (pairScalarEnd CanonicalComplex.alpha CubicRejoinReadoutCountermodel.zeta ^ 4) e -
    (pairScalarEnd CanonicalComplex.beta (conj CubicRejoinReadoutCountermodel.zeta) ^ 4) e = _
  rw [pairScalarEnd_pow_apply, pairScalarEnd_pow_apply]
  apply Prod.ext
  · simp [e]
  · change CubicRejoinReadoutCountermodel.zeta ^ 4 * 1 - conj CubicRejoinReadoutCountermodel.zeta ^ 4 * 1 = ⟨0, -CubicRejoinReadoutCountermodel.r⟩
    rw [mul_one, mul_one]
    have ha : CubicRejoinReadoutCountermodel.zeta ^ 4 = -CubicRejoinReadoutCountermodel.zeta := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, CubicRejoinReadoutCountermodel.zeta_cube]
      ring
    have hb : conj CubicRejoinReadoutCountermodel.zeta ^ 4 = -conj CubicRejoinReadoutCountermodel.zeta := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, CubicRejoinReadoutCountermodel.conj_zeta_cube]
      ring
    rw [ha, hb]
    apply Complex.ext <;> simp [CubicRejoinReadoutCountermodel.zeta] <;> ring

theorem fourth_difference_nonzero : (A ^ 4 - B ^ 4) e ≠ 0 := by
  rw [fourth_difference_at_hidden_state]
  intro h
  have him := congrArg (fun z : V => z.2.im) h
  change -CubicRejoinReadoutCountermodel.r = 0 at him
  have hr := CubicRejoinReadoutCountermodel.r_pos
  linarith

theorem fourth_rejoin_failure : A ^ 4 ≠ B ^ 4 := by
  intro h
  apply fourth_difference_nonzero
  rw [h, sub_self]
  rfl

/-- Failure of literal same-nullity of the entire carrier also defeats the
literal two-port square-as-swap identity. -/
theorem square_swap_failure :
    twoPort A B (twoPort A B (e, 0)) ≠ (e, 0).swap := by
  intro h
  have hfirst := congrArg Prod.fst h
  apply same_nonzero
  change A (A e + B 0) + B (B e + A 0) = 0 at hfirst
  simpa only [map_zero, add_zero] using hfirst

theorem original_carrier_failure_certificate :
    Reconstruction gate W ∧ W normalizedState = 1 ∧
    gate.same e ≠ 0 ∧ W (gate.same e) = 0 ∧
    (A ^ 4 - B ^ 4) e ≠ 0 ∧ A ^ 4 ≠ B ^ 4 ∧
    twoPort A B (twoPort A B (e, 0)) ≠ (e, 0).swap :=
  ⟨reconstructed, normalized, same_nonzero, same_readout_zero,
    fourth_difference_nonzero, fourth_rejoin_failure, square_swap_failure⟩

end HiddenCubicSector

end IDT.QMClosure.FiniteRejoinCarrierChoiceControls
