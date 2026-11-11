/-
Authors: OpenAI Codex, delegated agent /root/cyclic_four_congruence_draft
Lean kernel-checked mathematical source.
Parent-approved design: /tmp/idt-initial-normal-form/v1/CONTRACTS.md.
This module states an exact algebraic normal form for the literal initial
transparency/fourth-rejoin semiring. Its coordinate rings are concrete targets.
-/
import Proofs.QMClosure.TransparentFourthInitialHistoryPresentation
import Proofs.QMClosure.CyclicFourPositiveCongruence
import Proofs.QMClosure.SingleCalibrationScalarFaithfulness
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Complex.Basic

namespace IDT.QMClosure.TransparentFourthInitialNormalForm

noncomputable section

open TransparentFourthInitialHistoryPresentation
open SingleCalibrationScalarFaithfulness

abbrev P := Presentation
abbrev A := _root_.CyclicFourPositiveCongruence.A
abbrev Ambient := ℂ × ℝ

/-- A positive word giving the inverse of the second initial generator. -/
def bInv : P := FourthRejoinIdempotent.geometricInverse b a

theorem bInv_mul_b : bInv * b = 1 :=
  (FourthRejoinIdempotent.geometric_inverse_b transparent fourth_rejoin).1

theorem b_mul_bInv : b * bInv = 1 :=
  (FourthRejoinIdempotent.geometric_inverse_b transparent fourth_rejoin).2

def rho : P := a * bInv

theorem rho_mul_b : rho * b = a := by
  rw [rho, mul_assoc, bInv_mul_b, mul_one]

theorem rho_four : rho ^ 4 = 1 := by
  calc
    rho ^ 4 = a ^ 4 * bInv ^ 4 := by rw [rho, mul_pow]
    _ = b ^ 4 * bInv ^ 4 := by rw [fourth_rejoin]
    _ = (b * bInv) ^ 4 := (mul_pow _ _ _).symm
    _ = 1 := by rw [b_mul_bInv, one_pow]

private theorem rho_five : rho ^ 5 = rho := by
  rw [show 5 = 4 + 1 by decide, pow_add, rho_four]
  simp

private theorem rho_six : rho ^ 6 = rho ^ 2 := by
  rw [show 6 = 4 + 2 by decide, pow_add, rho_four, one_mul]

def cyclicPower (g : _root_.CyclicFourPositiveCongruence.C4) : P := rho ^ (Multiplicative.toAdd g).val

def cyclicPowerHom : _root_.CyclicFourPositiveCongruence.C4 →* P where
  toFun := cyclicPower
  map_one' := by
    change rho ^ 0 = 1
    exact pow_zero rho
  map_mul' x y := by
    change Fin 4 at x y
    fin_cases x <;> fin_cases y
    · change rho ^ 0 = rho ^ 0 * rho ^ 0
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 1 = rho ^ 0 * rho ^ 1
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 2 = rho ^ 0 * rho ^ 2
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 3 = rho ^ 0 * rho ^ 3
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 1 = rho ^ 1 * rho ^ 0
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 2 = rho ^ 1 * rho ^ 1
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 3 = rho ^ 1 * rho ^ 2
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 0 = rho ^ 1 * rho ^ 3
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 2 = rho ^ 2 * rho ^ 0
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 3 = rho ^ 2 * rho ^ 1
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 0 = rho ^ 2 * rho ^ 2
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 1 = rho ^ 2 * rho ^ 3
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 3 = rho ^ 3 * rho ^ 0
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 0 = rho ^ 3 * rho ^ 1
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 1 = rho ^ 3 * rho ^ 2
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]
    · change rho ^ 2 = rho ^ 3 * rho ^ 3
      rw [← pow_add] <;> norm_num [rho_four, rho_five, rho_six]

def cyclicEval : A →+* P :=
  MonoidAlgebra.liftNCRingHom (Nat.castRingHom P) cyclicPowerHom
    (fun _ _ => mul_comm _ _)

@[simp] theorem cyclicEval_r : cyclicEval _root_.CyclicFourPositiveCongruence.r = rho := by
  simp only [cyclicEval, _root_.CyclicFourPositiveCongruence.r,
    MonoidAlgebra.liftNCRingHom_single]
  change (1 : P) * rho ^ 1 = rho
  simp

theorem denominator_inverse : cyclicEval _root_.CyclicFourPositiveCongruence.s * b = 1 := by
  rw [_root_.CyclicFourPositiveCongruence.s, map_add, map_one, cyclicEval_r, add_mul, one_mul, rho_mul_b,
    add_comm, transparent]

theorem denominator_inverse_reverse : b * cyclicEval _root_.CyclicFourPositiveCongruence.s = 1 := by
  rw [mul_comm]
  exact denominator_inverse

theorem denominator_power_inverse (n : ℕ) :
    b ^ n * (cyclicEval _root_.CyclicFourPositiveCongruence.s) ^ n = 1 := by
  rw [← mul_pow, denominator_inverse_reverse, one_pow]

theorem cyclic_fraction_raise (n m : ℕ) (u : A) :
    b ^ (n + m) * cyclicEval (u * _root_.CyclicFourPositiveCongruence.s ^ m) =
      b ^ n * cyclicEval u := by
  calc
    _ = (b ^ n * cyclicEval u) *
        (b ^ m * (cyclicEval _root_.CyclicFourPositiveCongruence.s) ^ m) := by
      simp only [map_mul, map_pow, pow_add]
      ring
    _ = _ := by rw [denominator_power_inverse, mul_one]

/-- Every initial element has a positive cyclic numerator and a power-of-b
factor. This construction uses the initial positive grammar. -/
theorem exists_cyclic_fraction (p : P) :
    ∃ n : ℕ, ∃ u : A, p = b ^ n * cyclicEval u := by
  apply presentation_induction
    (motive := fun p => ∃ n : ℕ, ∃ u : A, p = b ^ n * cyclicEval u)
  · exact ⟨0, 0, by simp⟩
  · exact ⟨0, 1, by simp⟩
  · refine ⟨1, _root_.CyclicFourPositiveCongruence.r, ?_⟩
    simp only [pow_one, cyclicEval_r]
    rw [mul_comm, rho_mul_b]
  · exact ⟨1, 1, by simp⟩
  · intro x y hx hy
    obtain ⟨n, u, rfl⟩ := hx
    obtain ⟨m, v, rfl⟩ := hy
    refine ⟨n + m, u * _root_.CyclicFourPositiveCongruence.s ^ m + v * _root_.CyclicFourPositiveCongruence.s ^ n, ?_⟩
    have hv : b ^ (n + m) * cyclicEval (v * _root_.CyclicFourPositiveCongruence.s ^ n) =
        b ^ m * cyclicEval v := by
      simpa only [Nat.add_comm] using cyclic_fraction_raise m n v
    rw [map_add, mul_add, cyclic_fraction_raise, hv]
  · intro x y hx hy
    obtain ⟨n, u, rfl⟩ := hx
    obtain ⟨m, v, rfl⟩ := hy
    refine ⟨n + m, u * v, ?_⟩
    rw [map_mul, pow_add]
    ring

theorem cyclicEval_U_eq_V : cyclicEval _root_.CyclicFourPositiveCongruence.U = cyclicEval _root_.CyclicFourPositiveCongruence.V := by
  have h := congrArg cyclicEval _root_.CyclicFourPositiveCongruence.s_mul_U_eq_s_mul_V
  have h' := congrArg (fun x : P => b * x) h
  simpa only [map_mul, ← mul_assoc, denominator_inverse_reverse, one_mul] using h'

theorem cyclic_congruence_le_kernel : _root_.CyclicFourPositiveCongruence.congruence ≤ RingCon.ker cyclicEval := by
  apply RingCon.ringConGen_le
  intro x y h
  cases h
  exact cyclicEval_U_eq_V

theorem cyclic_semantic_fiber_collapse (u v : A) (h : _root_.CyclicFourPositiveCongruence.phi u = _root_.CyclicFourPositiveCongruence.phi v) :
    cyclicEval u = cyclicEval v :=
  cyclic_congruence_le_kernel ((_root_.CyclicFourPositiveCongruence.phi_eq_iff u v).mp h)

private theorem I_square : Complex.I ^ 2 = -(1 : ℂ) := Complex.I_sq
private theorem two_half : (2 : ℂ) * (1 / 2) = 1 := by norm_num

/-- The arithmetic-only generated subring, instantiated in Complex. -/
def gaussianDyadic : Subring ℂ :=
  Arithmetic.generatedSubring Complex.I (1 / 2) I_square two_half

def realDyadic : Subring ℝ := gaussianDyadic.comap Complex.ofRealHom

private theorem arithmetic_value_formula (k : ℕ) (m n : ℤ) :
    Arithmetic.value Complex.I (1 / 2) k (m, n) =
      ((m : ℂ) + (n : ℂ) * Complex.I) / (2 : ℂ) ^ k := by
  simp [Arithmetic.value, Arithmetic.gaussian, one_div_pow, div_eq_mul_inv, mul_comm]

theorem mem_gaussianDyadic (z : ℂ) :
    z ∈ gaussianDyadic ↔
      ∃ k : ℕ, ∃ m n : ℤ,
        z = ((m : ℂ) + (n : ℂ) * Complex.I) / (2 : ℂ) ^ k := by
  change (∃ k t, z = Arithmetic.value Complex.I (1 / 2) k t) ↔ _
  constructor
  · rintro ⟨k, ⟨m, n⟩, h⟩
    exact ⟨k, m, n, h.trans (arithmetic_value_formula k m n)⟩
  · rintro ⟨k, m, n, h⟩
    exact ⟨k, (m, n), h.trans (arithmetic_value_formula k m n).symm⟩

theorem mem_realDyadic (q : ℝ) :
    q ∈ realDyadic ↔ ∃ k : ℕ, ∃ m : ℤ, q = (m : ℝ) / (2 : ℝ) ^ k := by
  change (q : ℂ) ∈ gaussianDyadic ↔ _
  rw [mem_gaussianDyadic]
  constructor
  · rintro ⟨k, m, n, h⟩
    have hden : Complex.ofReal ((2 : ℝ) ^ k) = (2 : ℂ) ^ k := by norm_cast
    have hcross := (eq_div_iff (pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0))).mp h
    rw [← hden] at hcross
    have hre := congrArg Complex.re hcross
    simp at hre
    refine ⟨k, m, ?_⟩
    apply (eq_div_iff (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0))).mpr
    have hrealPower : ((2 : ℂ) ^ k).re = (2 : ℝ) ^ k := by
      simpa only [Complex.ofReal_re] using (congrArg Complex.re hden).symm
    simpa only [hrealPower] using hre
  · rintro ⟨k, m, rfl⟩
    refine ⟨k, m, 0, ?_⟩
    push_cast <;> simp

private theorem I_mem : Complex.I ∈ gaussianDyadic := by
  apply (mem_gaussianDyadic _).mpr
  exact ⟨0, 0, 1, by simp⟩

private theorem half_mem : (1 / 2 : ℂ) ∈ gaussianDyadic := by
  apply (mem_gaussianDyadic _).mpr
  exact ⟨1, 1, 0, by norm_num⟩

private theorem real_half_mem : (1 / 2 : ℝ) ∈ realDyadic := by
  apply (mem_realDyadic _).mpr
  exact ⟨1, 1, by norm_num⟩

/-- Zero together with every Gaussian-dyadic/positive-real-dyadic pair. -/
def normalSemiring : Subsemiring Ambient where
  carrier := {x | (x.1 = 0 ∧ x.2 = 0) ∨
    (x.1 ∈ gaussianDyadic ∧ x.2 ∈ realDyadic ∧ 0 < x.2)}
  zero_mem' := Or.inl ⟨rfl, rfl⟩
  one_mem' := Or.inr ⟨gaussianDyadic.one_mem, realDyadic.one_mem, zero_lt_one⟩
  add_mem' := by
    intro x y hx hy
    rcases hx with hx | ⟨hxg, hxd, hxp⟩
    · have hx0 : x = 0 := Prod.ext hx.1 hx.2
      rw [hx0, zero_add]
      exact hy
    rcases hy with hy | ⟨hyg, hyd, hyp⟩
    · have hy0 : y = 0 := Prod.ext hy.1 hy.2
      rw [hy0, add_zero]
      exact Or.inr ⟨hxg, hxd, hxp⟩
    · exact Or.inr ⟨gaussianDyadic.add_mem hxg hyg,
        realDyadic.add_mem hxd hyd, add_pos hxp hyp⟩
  mul_mem' := by
    intro x y hx hy
    rcases hx with hx | ⟨hxg, hxd, hxp⟩
    · have hx0 : x = 0 := Prod.ext hx.1 hx.2
      rw [hx0, zero_mul]
      exact Or.inl ⟨rfl, rfl⟩
    rcases hy with hy | ⟨hyg, hyd, hyp⟩
    · have hy0 : y = 0 := Prod.ext hy.1 hy.2
      rw [hy0, mul_zero]
      exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨gaussianDyadic.mul_mem hxg hyg,
        realDyadic.mul_mem hxd hyd, mul_pos hxp hyp⟩

def complexA : ℂ := (1 + Complex.I) / 2
def complexB : ℂ := (1 - Complex.I) / 2

private theorem complex_transparent : complexA + complexB = 1 := by
  dsimp [complexA, complexB]
  ring

private theorem complex_fourth : complexA ^ 4 = complexB ^ 4 := by
  apply Complex.ext <;>
    norm_num [complexA, complexB, pow_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

def complexEvaluation : P →+* ℂ :=
  eval complexA complexB complex_transparent complex_fourth

/-- The second coordinate is the independently constructed initial real shadow. -/
def rawSemantics : P →+* Ambient := complexEvaluation.prod realShadow

@[simp] theorem raw_a : rawSemantics a = (complexA, 1 / 2) := by
  simp [rawSemantics, complexEvaluation]

@[simp] theorem raw_b : rawSemantics b = (complexB, 1 / 2) := by
  simp [rawSemantics, complexEvaluation]

private theorem complexA_mem : complexA ∈ gaussianDyadic := by
  have h := gaussianDyadic.mul_mem
    (gaussianDyadic.add_mem gaussianDyadic.one_mem I_mem) half_mem
  simpa [complexA, div_eq_mul_inv] using h

private theorem complexB_mem : complexB ∈ gaussianDyadic := by
  have h := gaussianDyadic.mul_mem
    (gaussianDyadic.sub_mem gaussianDyadic.one_mem I_mem) half_mem
  simpa [complexB, div_eq_mul_inv] using h

theorem raw_mem_normalSemiring (p : P) : rawSemantics p ∈ normalSemiring := by
  apply presentation_induction
    (motive := fun p => rawSemantics p ∈ normalSemiring)
  · simpa using normalSemiring.zero_mem
  · simpa using normalSemiring.one_mem
  · rw [raw_a]
    exact Or.inr ⟨complexA_mem, real_half_mem, by norm_num⟩
  · rw [raw_b]
    exact Or.inr ⟨complexB_mem, real_half_mem, by norm_num⟩
  · intro x y hx hy
    simpa using normalSemiring.add_mem hx hy
  · intro x y hx hy
    simpa using normalSemiring.mul_mem hx hy

def normalSemantics : P →+* normalSemiring :=
  rawSemantics.codRestrict normalSemiring raw_mem_normalSemiring

@[simp] theorem normalSemantics_val (p : P) :
    (normalSemantics p).val = rawSemantics p := rfl

theorem real_coordinate_eq_shadow (p : P) :
    (normalSemantics p).val.2 = realShadow p := rfl

private theorem raw_bInv : rawSemantics bInv = (1 + Complex.I, 2) := by
  simp only [bInv, FourthRejoinIdempotent.geometricInverse,
    map_add, map_one, map_pow, raw_a, raw_b]
  apply Prod.ext
  · apply Complex.ext <;>
      norm_num [complexA, complexB, pow_succ, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im]
  · norm_num

@[simp] theorem raw_rho : rawSemantics rho = (Complex.I, 1) := by
  rw [rho, map_mul, raw_a, raw_bInv]
  apply Prod.ext
  · apply Complex.ext <;>
      norm_num [complexA, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im]
  · norm_num

/-- Faithful integer-coordinate embedding into the ambient coordinate rings. -/
def integerEmbedding : _root_.CyclicFourPositiveCongruence.Target →+* Ambient :=
  RingHom.prodMap GaussianInt.toComplex (Int.castRingHom ℝ)

theorem integerEmbedding_injective : Function.Injective integerEmbedding := by
  intro x y h
  apply Prod.ext
  · exact GaussianInt.toComplex_injective (congrArg Prod.fst h)
  · have hc : (x.2 : ℝ) = (y.2 : ℝ) := congrArg Prod.snd h
    exact_mod_cast hc

theorem cyclic_semantics (u : A) :
    rawSemantics (cyclicEval u) = integerEmbedding (_root_.CyclicFourPositiveCongruence.phi u) := by
  have he : rawSemantics.comp cyclicEval = integerEmbedding.comp _root_.CyclicFourPositiveCongruence.phi := by
    apply MonoidAlgebra.ringHom_ext
    · intro n
      change rawSemantics (cyclicEval (MonoidAlgebra.single 1 n)) = _
      have hn : (MonoidAlgebra.single (1 : _root_.CyclicFourPositiveCongruence.C4) n : A) = (n : A) :=
        (MonoidAlgebra.natCast_def n).symm
      rw [hn]
      simp
    · intro g
      simp only [RingHom.comp_apply, cyclicEval,
        MonoidAlgebra.liftNCRingHom_single, _root_.CyclicFourPositiveCongruence.phi_single,
        Nat.cast_one, one_mul]
      rw [map_one (Nat.castRingHom P), one_mul]
      change Fin 4 at g
      fin_cases g
      · change rawSemantics (rho ^ 0) =
          integerEmbedding ((⟨1, 0⟩, 1) : _root_.CyclicFourPositiveCongruence.Target)
        rw [map_pow, raw_rho]
        apply Prod.ext
        · apply Complex.ext <;>
            norm_num [integerEmbedding, GaussianInt.toComplex_def', pow_succ,
              Complex.mul_re, Complex.mul_im]
        · norm_num [integerEmbedding]
      · change rawSemantics (rho ^ 1) =
          integerEmbedding ((⟨0, 1⟩, 1) : _root_.CyclicFourPositiveCongruence.Target)
        rw [map_pow, raw_rho]
        apply Prod.ext
        · apply Complex.ext <;>
            norm_num [integerEmbedding, GaussianInt.toComplex_def', pow_succ,
              Complex.mul_re, Complex.mul_im]
        · norm_num [integerEmbedding]
      · change rawSemantics (rho ^ 2) =
          integerEmbedding ((⟨-1, 0⟩, 1) : _root_.CyclicFourPositiveCongruence.Target)
        rw [map_pow, raw_rho]
        apply Prod.ext
        · apply Complex.ext <;>
            norm_num [integerEmbedding, GaussianInt.toComplex_def', pow_succ,
              Complex.mul_re, Complex.mul_im]
        · norm_num [integerEmbedding]
      · change rawSemantics (rho ^ 3) =
          integerEmbedding ((⟨0, -1⟩, 1) : _root_.CyclicFourPositiveCongruence.Target)
        rw [map_pow, raw_rho]
        apply Prod.ext
        · apply Complex.ext <;>
            norm_num [integerEmbedding, GaussianInt.toComplex_def', pow_succ,
              Complex.mul_re, Complex.mul_im]
        · norm_num [integerEmbedding]
  exact congrArg (fun f : A →+* Ambient => f u) he

@[simp] theorem raw_denominator :
    rawSemantics (cyclicEval _root_.CyclicFourPositiveCongruence.s) = (1 + Complex.I, 2) := by
  simp only [_root_.CyclicFourPositiveCongruence.s, map_add, map_one, cyclicEval_r, raw_rho]
  apply Prod.ext <;> norm_num

/-- Equality reflection follows by aligning positive cyclic fractions and
multiplying by the explicit inverse denominator, then using the cyclic kernel. -/
theorem rawSemantics_injective : Function.Injective rawSemantics := by
  intro p q heq
  obtain ⟨n, u, hp⟩ := exists_cyclic_fraction p
  obtain ⟨m, v, hq⟩ := exists_cyclic_fraction q
  let N := n + m
  let u' := u * _root_.CyclicFourPositiveCongruence.s ^ m
  let v' := v * _root_.CyclicFourPositiveCongruence.s ^ n
  have hp' : p = b ^ N * cyclicEval u' := by
    rw [hp]
    exact (cyclic_fraction_raise n m u).symm
  have hq' : q = b ^ N * cyclicEval v' := by
    rw [hq]
    simpa only [N, v', Nat.add_comm] using (cyclic_fraction_raise m n v).symm
  have hunit : rawSemantics (cyclicEval _root_.CyclicFourPositiveCongruence.s) ^ N *
      rawSemantics b ^ N = 1 := by
    rw [← mul_pow, ← map_mul, denominator_inverse, map_one, one_pow]
  rw [hp', hq'] at heq
  simp only [rawSemantics.map_mul, rawSemantics.map_pow] at heq
  have hclear := congrArg
    (fun t : Ambient => rawSemantics (cyclicEval _root_.CyclicFourPositiveCongruence.s) ^ N * t) heq
  have hc : rawSemantics (cyclicEval u') = rawSemantics (cyclicEval v') := by
    simpa only [← mul_assoc, hunit, one_mul] using hclear
  rw [cyclic_semantics, cyclic_semantics] at hc
  have he := cyclic_semantic_fiber_collapse u' v' (integerEmbedding_injective hc)
  rw [hp', hq', he]

theorem normalSemantics_injective : Function.Injective normalSemantics := by
  intro p q h
  exact rawSemantics_injective (congrArg Subtype.val h)

/-- Absolute coordinate sum used only for the exact image construction. -/
def complexL1 (z : ℂ) : ℝ := |z.re| + |z.im|

private theorem complexL1_I_mul (z : ℂ) : complexL1 (Complex.I * z) = complexL1 z := by
  simp [complexL1, Complex.mul_re, Complex.mul_im, abs_neg, add_comm]

private theorem complexL1_I_pow_mul (m : ℕ) (z : ℂ) :
    complexL1 (Complex.I ^ m * z) = complexL1 z := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', mul_assoc, complexL1_I_mul, ih]

private theorem complexL1_scale (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    complexL1 ((c : ℂ) * z) = c * complexL1 z := by
  simp [complexL1, Complex.mul_re, Complex.mul_im, abs_mul, abs_of_nonneg hc] <;> ring

private theorem one_add_I_even_power (m : ℕ) :
    (1 + Complex.I) ^ (2 * m) = (2 : ℂ) ^ m * Complex.I ^ m := by
  have hs : (1 + Complex.I) ^ 2 = (2 : ℂ) * Complex.I := by
    calc
      _ = 1 + 2 * Complex.I + Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [pow_mul, hs, mul_pow]

private theorem complexL1_even_power (m : ℕ) (z : ℂ) :
    complexL1 ((1 + Complex.I) ^ (2 * m) * z) =
      (2 : ℝ) ^ m * complexL1 z := by
  rw [one_add_I_even_power, mul_assoc]
  have hcast : Complex.ofReal ((2 : ℝ) ^ m) = (2 : ℂ) ^ m := by norm_cast
  calc
    _ = (2 : ℝ) ^ m * complexL1 (Complex.I ^ m * z) := by
      rw [← hcast]
      exact complexL1_scale ((2 : ℝ) ^ m) (pow_nonneg (by norm_num) m) _
    _ = _ := by rw [complexL1_I_pow_mul]

private theorem clear_dyadic {K : Type*} [Field K] [CharZero K]
    (a : K) (d m : ℕ) (hd : d ≤ m) :
    (2 : K) ^ m * (a / (2 : K) ^ d) = (2 : K) ^ (m - d) * a := by
  have htwo : (2 : K) ≠ 0 := by norm_num
  calc
    _ = ((2 : K) ^ (m - d) * (2 : K) ^ d) * (a / (2 : K) ^ d) := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    _ = _ := by field_simp

private theorem one_le_two_pow (n : ℕ) : (1 : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; nlinarith

private theorem gaussianL1_cast (g : GaussianInt) :
    complexL1 (GaussianInt.toComplex g) = ((|g.re| + |g.im| : ℤ) : ℝ) := by
  rw [GaussianInt.toComplex_def₂]
  change |(g.re : ℝ)| + |(g.im : ℝ)| = _
  norm_cast

/-- Clear dyadic denominators at a sufficiently large even degree. The output
is an actual positive cyclic numerator, with the parity condition verified. -/
theorem exists_cyclic_numerator (z : ℂ) (q : ℝ)
    (hz : z ∈ gaussianDyadic) (hq : q ∈ realDyadic) (hpos : 0 < q) :
    ∃ k : ℕ, 4 ≤ k ∧ ∃ u : A,
      integerEmbedding (_root_.CyclicFourPositiveCongruence.phi u) =
        rawSemantics (cyclicEval _root_.CyclicFourPositiveCongruence.s) ^ k * (z, q) := by
  obtain ⟨d, M, N, hzrep⟩ := (mem_gaussianDyadic z).mp hz
  obtain ⟨l, R, hqrep⟩ := (mem_realDyadic q).mp hq
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (complexL1 z / q)
    (show (1 : ℝ) < 2 by norm_num)
  let m := d + l + t + 2
  have hdm : d + 1 ≤ m := by dsimp [m]; omega
  have hlm : l + 1 ≤ 2 * m := by dsimp [m]; omega
  have hm2 : 2 ≤ m := by dsimp [m]; omega
  have hpow : (2 : ℝ) ^ t ≤ (2 : ℝ) ^ m := by
    have hfac := one_le_two_pow (d + l + 2)
    have hpt : 0 < (2 : ℝ) ^ t := pow_pos (by norm_num) _
    have hexp : m = t + (d + l + 2) := by dsimp [m]; omega
    rw [hexp, pow_add]
    simpa using mul_le_mul_of_nonneg_left hfac hpt.le
  have hlarge : complexL1 z ≤ (2 : ℝ) ^ m * q := by
    exact (div_le_iff₀ hpos).mp (le_trans ht.le hpow)
  let gi : GaussianInt := ⟨0, 1⟩
  let g : GaussianInt := (2 : GaussianInt) ^ (m - d) * gi ^ m * ⟨M, N⟩
  let Q : ℤ := (2 : ℤ) ^ (2 * m - l) * R
  have hgi : GaussianInt.toComplex gi = Complex.I := by
    simp [gi, GaussianInt.toComplex_def]
  have hg : GaussianInt.toComplex g = (1 + Complex.I) ^ (2 * m) * z := by
    dsimp [g]
    simp only [map_mul, map_pow, map_ofNat, hgi]
    rw [GaussianInt.toComplex_def, one_add_I_even_power, hzrep]
    have hc := clear_dyadic ((M : ℂ) + (N : ℂ) * Complex.I) d m (by omega)
    calc
      _ = Complex.I ^ m *
          ((2 : ℂ) ^ m * (((M : ℂ) + (N : ℂ) * Complex.I) / (2 : ℂ) ^ d)) := by
        rw [hc]
        ring
      _ = _ := by ring
  have hQ : (Q : ℝ) = (2 : ℝ) ^ (2 * m) * q := by
    dsimp [Q]
    push_cast
    rw [hqrep]
    exact (clear_dyadic (R : ℝ) l (2 * m) (by omega)).symm
  have hg_even : ∃ g0 : GaussianInt, g = 2 * g0 := by
    refine ⟨(2 : GaussianInt) ^ (m - d - 1) * gi ^ m * ⟨M, N⟩, ?_⟩
    dsimp [g]
    nth_rw 1 [show m - d = (m - d - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hQ_even : ∃ Q0 : ℤ, Q = 2 * Q0 := by
    refine ⟨(2 : ℤ) ^ (2 * m - l - 1) * R, ?_⟩
    dsimp [Q]
    nth_rw 1 [show 2 * m - l = (2 * m - l - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hboundR : (((|g.re| + |g.im| : ℤ) : ℝ)) ≤ (Q : ℝ) := by
    rw [← gaussianL1_cast, hg, complexL1_even_power, hQ]
    calc
      (2 : ℝ) ^ m * complexL1 z ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ m * q) :=
        mul_le_mul_of_nonneg_left hlarge (pow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ (2 * m) * q := by
        rw [show 2 * m = m + m by omega, pow_add]
        ring
  have hbound : |g.re| + |g.im| ≤ Q := by exact_mod_cast hboundR
  have hparity : Q % 2 = (g.re + g.im) % 2 := by
    obtain ⟨g0, hg0⟩ := hg_even
    obtain ⟨Q0, hQ0⟩ := hQ_even
    have hre := congrArg Zsqrtd.re hg0
    have him := congrArg Zsqrtd.im hg0
    simp at hre him
    omega
  obtain ⟨n0, n1, n2, n3, hr, hi, htotal⟩ :=
    _root_.CyclicFourPositiveCongruence.exists_coefficients_of_cone g.re g.im Q hbound hparity
  let u := _root_.CyclicFourPositiveCongruence.ofFour n0 n1 n2 n3
  have hu : _root_.CyclicFourPositiveCongruence.phi u = (g, Q) := by
    rw [_root_.CyclicFourPositiveCongruence.phi_ofFour]
    apply Prod.ext
    · exact Zsqrtd.ext hr hi
    · exact htotal
  refine ⟨2 * m, by omega, u, ?_⟩
  rw [hu, raw_denominator]
  apply Prod.ext
  · simpa [integerEmbedding] using hg
  · simpa [integerEmbedding] using hQ

theorem normalSemantics_surjective : Function.Surjective normalSemantics := by
  intro x
  rcases x.property with hzero | ⟨hz, hq, hpos⟩
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    change rawSemantics 0 = x.val
    rw [map_zero]
    exact (Prod.ext hzero.1 hzero.2).symm
  · obtain ⟨k, hk, u, hu⟩ := exists_cyclic_numerator x.val.1 x.val.2 hz hq hpos
    refine ⟨b ^ k * cyclicEval u, ?_⟩
    apply Subtype.ext
    change rawSemantics (b ^ k * cyclicEval u) = x.val
    rw [map_mul, map_pow, cyclic_semantics, hu]
    calc
      _ = (rawSemantics b ^ k *
          rawSemantics (cyclicEval _root_.CyclicFourPositiveCongruence.s) ^ k) * x.val := by ring
      _ = x.val := by
        rw [← mul_pow, ← map_mul, denominator_inverse_reverse, map_one, one_pow, one_mul]

/-- Exact initial-semiring normal form. -/
def normalFormEquiv : P ≃+* normalSemiring :=
  RingEquiv.ofBijective normalSemantics
    ⟨normalSemantics_injective, normalSemantics_surjective⟩

@[simp] theorem normalForm_a :
    (normalFormEquiv a).val = ((1 + Complex.I) / 2, 1 / 2) := raw_a

@[simp] theorem normalForm_b :
    (normalFormEquiv b).val = ((1 - Complex.I) / 2, 1 / 2) := raw_b

@[simp] theorem normalForm_T : (normalFormEquiv T).val = (0, 1 / 2) := by
  change rawSemantics (a ^ 2 + b ^ 2) = _
  rw [map_add, map_pow, map_pow, raw_a, raw_b]
  apply Prod.ext
  · apply Complex.ext <;>
      norm_num [complexA, complexB, pow_succ, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im]
  · norm_num

@[simp] theorem normalForm_e : (normalFormEquiv e).val = (0, 1) := by
  change rawSemantics ((2 : P) * T) = _
  rw [map_mul, map_ofNat]
  change (2 : Ambient) * (normalFormEquiv T).val = _
  rw [normalForm_T]
  apply Prod.ext <;> norm_num

theorem equality_iff_coordinates (p q : P) :
    p = q ↔ (normalFormEquiv p).val.1 = (normalFormEquiv q).val.1 ∧
      (normalFormEquiv p).val.2 = (normalFormEquiv q).val.2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hr, hi⟩
    apply normalFormEquiv.injective
    exact Subtype.ext (Prod.ext hr hi)

end
end IDT.QMClosure.TransparentFourthInitialNormalForm
