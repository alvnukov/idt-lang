import Proofs.QMClosure.FiniteRejoinCarrierChoiceControls
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Logic.Function.Iterate

/-!
# A finite generated-ring recovery exclusion

SCRATCH DRAFT. Complete proposed proof bodies await registered-target compilation
and independent kernel, signature and dependency review.

The coefficients and the nonzero conserved complex model are those of
`FiniteRejoinCarrierChoiceControls.NoFiniteRejoin`. The unital subring generated
by the forward coefficients and their two inverses is exactly the elementary
Gaussian denominator ring with denominator powers of `4 - 2i`. This ring already
contains `i` and the dyadic half. Reduction of Gaussian integers modulo five at
`i = 3` excludes both recovered coefficients and the inverse difference.

The operator statement uses the actual ring of additive endomorphisms, with
multiplication given by composition, and a faithful scalar-multiplication ring
homomorphism. It permits signed sums and products of the stated generators.
Adding the scalar `1/5` removes this particular obstruction.

The ambient complex model already has mathematical two-port recovery. These
results concern finite expression resources. Physical access, generic pairing
adjoints, mixed-gain controls and full QM remain separate obligations.
-/

noncomputable section

namespace IDT.QMClosure.UnbalancedRecoveryOperatorRingWall

open FiniteRejoinCarrierChoiceControls
open FiniteRejoinQuadraticReadoutControls
open scoped ComplexConjugate

abbrev alpha : ℂ := NoFiniteRejoin.alpha
abbrev beta : ℂ := NoFiniteRejoin.beta

/-- The Gaussian denominator `2 * (2 - i)`. -/
def denominator : GaussianInt := ⟨4, -2⟩

/-- The Gaussian factor killed by the chosen residue. -/
def conjugatePrime : GaussianInt := ⟨2, 1⟩

/-- The conjugate Gaussian factor, retained by the chosen residue. -/
def forwardPrime : GaussianInt := ⟨2, -1⟩

/-- The adjoint coefficient of the first branch in the concrete model. -/
def recoveredAlpha : ℂ := conj alpha

/-- The second recovered coefficient, using transparency. -/
def recoveredBeta : ℂ := 1 - recoveredAlpha

/-- The ambient mathematical inverse of the branch-difference coefficient. -/
def inverseDifference : ℂ := (alpha - beta)⁻¹

theorem alpha_inverse : alpha⁻¹ = (⟨1, -(1 / 2)⟩ : ℂ) := by
  apply Complex.ext <;>
    norm_num [alpha, NoFiniteRejoin.alpha, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply]

theorem beta_inverse : beta⁻¹ = (⟨1, 2⟩ : ℂ) := by
  apply Complex.ext <;>
    norm_num [beta, NoFiniteRejoin.beta, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply]

theorem denominator_nonzero : (GaussianInt.toComplex denominator) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [denominator, GaussianInt.toComplex_def₂] at hr

/-- An elementary denominator subring. The witness equation avoids choosing
localization representatives or allowing arbitrary scalar division. -/
def denominatorRing : Subring ℂ where
  carrier := {z | ∃ n : ℕ, ∃ g : GaussianInt,
    z * GaussianInt.toComplex denominator ^ n = GaussianInt.toComplex g}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro z w ⟨n, g, hg⟩ ⟨m, h, hh⟩
    refine ⟨n + m, g * denominator ^ m + h * denominator ^ n, ?_⟩
    calc
      (z + w) * GaussianInt.toComplex denominator ^ (n + m) =
          (z * GaussianInt.toComplex denominator ^ n) *
              GaussianInt.toComplex denominator ^ m +
            (w * GaussianInt.toComplex denominator ^ m) *
              GaussianInt.toComplex denominator ^ n := by
                rw [pow_add]
                ring
      _ = GaussianInt.toComplex (g * denominator ^ m + h * denominator ^ n) := by
        rw [hg, hh]
        simp only [map_add, map_mul, map_pow]
  neg_mem' := by
    rintro z ⟨n, g, hg⟩
    refine ⟨n, -g, ?_⟩
    simp only [map_neg, neg_mul, hg]
  mul_mem' := by
    rintro z w ⟨n, g, hg⟩ ⟨m, h, hh⟩
    refine ⟨n + m, g * h, ?_⟩
    calc
      (z * w) * GaussianInt.toComplex denominator ^ (n + m) =
          (z * GaussianInt.toComplex denominator ^ n) *
            (w * GaussianInt.toComplex denominator ^ m) := by
              rw [pow_add]
              ring
      _ = GaussianInt.toComplex (g * h) := by rw [hg, hh, map_mul]

theorem gaussian_mem_denominatorRing (g : GaussianInt) :
    GaussianInt.toComplex g ∈ denominatorRing :=
  ⟨0, g, by simp⟩

theorem alpha_mem_denominatorRing : alpha ∈ denominatorRing := by
  refine ⟨1, (4 : GaussianInt), ?_⟩
  apply Complex.ext <;>
    norm_num [alpha, NoFiniteRejoin.alpha, denominator,
      GaussianInt.toComplex_def₂, Complex.mul_re, Complex.mul_im]

theorem beta_mem_denominatorRing : beta ∈ denominatorRing := by
  refine ⟨1, (⟨0, -2⟩ : GaussianInt), ?_⟩
  apply Complex.ext <;>
    norm_num [beta, NoFiniteRejoin.beta, denominator,
      GaussianInt.toComplex_def₂, Complex.mul_re, Complex.mul_im]

theorem alpha_inverse_mem_denominatorRing : alpha⁻¹ ∈ denominatorRing := by
  refine ⟨1, (⟨3, -4⟩ : GaussianInt), ?_⟩
  rw [alpha_inverse]
  apply Complex.ext <;>
    norm_num [denominator, GaussianInt.toComplex_def₂,
      Complex.mul_re, Complex.mul_im]

theorem beta_inverse_mem_denominatorRing : beta⁻¹ ∈ denominatorRing := by
  rw [beta_inverse]
  refine ⟨0, (⟨1, 2⟩ : GaussianInt), ?_⟩
  apply Complex.ext <;>
    norm_num only [pow_zero, mul_one, GaussianInt.toComplex_def,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.natCast_re, Complex.natCast_im,
      Complex.re_ofNat, Complex.im_ofNat]

/-- Exactly four generators, with integer coefficients provided by Subring. -/
def forwardGenerators : Set ℂ := {alpha, beta, alpha⁻¹, beta⁻¹}

def coefficientRing : Subring ℂ := Subring.closure forwardGenerators

theorem coefficientRing_le_denominatorRing : coefficientRing ≤ denominatorRing := by
  apply Subring.closure_le.mpr
  intro z hz
  simp only [forwardGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact alpha_mem_denominatorRing
  · exact beta_mem_denominatorRing
  · exact alpha_inverse_mem_denominatorRing
  · exact beta_inverse_mem_denominatorRing

theorem alpha_mem_coefficientRing : alpha ∈ coefficientRing :=
  Subring.subset_closure (by simp [forwardGenerators])

theorem alpha_inverse_mem_coefficientRing : alpha⁻¹ ∈ coefficientRing :=
  Subring.subset_closure (by simp [forwardGenerators])

/-- Branch inversion already generates the imaginary unit. -/
theorem imaginary_mem_coefficientRing : Complex.I ∈ coefficientRing := by
  have ht : 1 - alpha⁻¹ ∈ coefficientRing :=
    coefficientRing.sub_mem coefficientRing.one_mem alpha_inverse_mem_coefficientRing
  have hi : Complex.I = (2 : ℂ) * (1 - alpha⁻¹) := by
    rw [alpha_inverse]
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  rw [hi]
  exact coefficientRing.mul_mem (natCast_mem coefficientRing 2) ht

/-- Branch inversion already generates the dyadic half, without inserting
arbitrary rational coefficients into the generated ring. -/
theorem half_mem_coefficientRing : (1 / 2 : ℂ) ∈ coefficientRing := by
  have ht : 1 - alpha⁻¹ ∈ coefficientRing :=
    coefficientRing.sub_mem coefficientRing.one_mem alpha_inverse_mem_coefficientRing
  have hh : (1 / 2 : ℂ) = (-2 : ℂ) * (1 - alpha⁻¹) ^ 2 := by
    rw [alpha_inverse]
    apply Complex.ext <;>
      norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  rw [hh]
  exact coefficientRing.mul_mem (coefficientRing.neg_mem (natCast_mem coefficientRing 2))
    (coefficientRing.pow_mem ht 2)

theorem inverse_denominator_mem_coefficientRing :
    (GaussianInt.toComplex denominator)⁻¹ ∈ coefficientRing := by
  have hformula : (GaussianInt.toComplex denominator)⁻¹ =
      alpha * (1 / 2 : ℂ) ^ 2 := by
    apply Complex.ext <;>
      norm_num [denominator, GaussianInt.toComplex_def₂,
        alpha, NoFiniteRejoin.alpha, Complex.inv_re, Complex.inv_im,
        Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  rw [hformula]
  exact coefficientRing.mul_mem alpha_mem_coefficientRing
    (coefficientRing.pow_mem half_mem_coefficientRing 2)

theorem gaussian_mem_coefficientRing (g : GaussianInt) :
    GaussianInt.toComplex g ∈ coefficientRing := by
  rw [GaussianInt.toComplex_def]
  exact coefficientRing.add_mem (intCast_mem coefficientRing g.re)
    (coefficientRing.mul_mem (intCast_mem coefficientRing g.im)
      imaginary_mem_coefficientRing)

/-- Exact elementary localization description of the four-generator ring. -/
theorem coefficientRing_eq_denominatorRing : coefficientRing = denominatorRing := by
  apply le_antisymm coefficientRing_le_denominatorRing
  rintro z ⟨n, g, hg⟩
  have hd : GaussianInt.toComplex denominator ^ n ≠ 0 :=
    pow_ne_zero n denominator_nonzero
  have hz : z = GaussianInt.toComplex g *
      (GaussianInt.toComplex denominator)⁻¹ ^ n := by
    apply (mul_right_cancel₀ hd)
    calc
      z * GaussianInt.toComplex denominator ^ n = GaussianInt.toComplex g := hg
      _ = (GaussianInt.toComplex g * (GaussianInt.toComplex denominator)⁻¹ ^ n) *
          GaussianInt.toComplex denominator ^ n := by
            rw [inv_pow]
            simp [hd]
  rw [hz]
  exact coefficientRing.mul_mem (gaussian_mem_coefficientRing g)
    (coefficientRing.pow_mem inverse_denominator_mem_coefficientRing n)

/-- The exact Gaussian residue `i ↦ 3` in the field with five elements. -/
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

def residue : GaussianInt →+* ZMod 5 :=
  Zsqrtd.lift (d := -1) ⟨(3 : ZMod 5), by decide⟩

theorem residue_denominator : residue denominator = 3 := by decide

theorem residue_conjugatePrime : residue conjugatePrime = 0 := by decide

theorem residue_forwardPrime : residue forwardPrime = 4 := by decide

theorem recoveredAlpha_mul_conjugatePrime :
    recoveredAlpha * GaussianInt.toComplex conjugatePrime = 2 := by
  apply Complex.ext <;>
    norm_num [recoveredAlpha, alpha, NoFiniteRejoin.alpha, conjugatePrime,
      GaussianInt.toComplex_def₂, Complex.mul_re, Complex.mul_im]

/-- Symbolic all-exponent exclusion, using the finite residue homomorphism. -/
theorem recoveredAlpha_not_mem_denominatorRing : recoveredAlpha ∉ denominatorRing := by
  rintro ⟨n, g, hg⟩
  have hcomplex : GaussianInt.toComplex g * GaussianInt.toComplex conjugatePrime =
      2 * GaussianInt.toComplex denominator ^ n := by
    calc
      GaussianInt.toComplex g * GaussianInt.toComplex conjugatePrime =
          (recoveredAlpha * GaussianInt.toComplex conjugatePrime) *
            GaussianInt.toComplex denominator ^ n := by rw [← hg]; ring
      _ = 2 * GaussianInt.toComplex denominator ^ n := by
        rw [recoveredAlpha_mul_conjugatePrime]
  have hgaussian : g * conjugatePrime = (2 : GaussianInt) * denominator ^ n := by
    apply GaussianInt.toComplex_injective
    simpa only [map_mul, map_pow, map_ofNat] using hcomplex
  have hresidue : (0 : ZMod 5) = 2 * (3 : ZMod 5) ^ n := by
    simpa only [map_mul, map_pow, map_ofNat, residue_conjugatePrime,
      residue_denominator, mul_zero] using congrArg residue hgaussian
  exact (mul_ne_zero (by decide : (2 : ZMod 5) ≠ 0)
    (pow_ne_zero n (by decide : (3 : ZMod 5) ≠ 0))) hresidue.symm

theorem recoveredAlpha_not_mem_coefficientRing : recoveredAlpha ∉ coefficientRing :=
  fun h => recoveredAlpha_not_mem_denominatorRing
    (coefficientRing_le_denominatorRing h)

theorem recoveredBeta_not_mem_coefficientRing : recoveredBeta ∉ coefficientRing := by
  intro h
  apply recoveredAlpha_not_mem_coefficientRing
  have hc : recoveredAlpha = 1 - recoveredBeta := by rw [recoveredBeta]; ring
  rw [hc]
  exact coefficientRing.sub_mem coefficientRing.one_mem h

theorem inverseDifference_mul_alpha : inverseDifference * alpha = recoveredAlpha := by
  apply Complex.ext <;>
    norm_num [inverseDifference, recoveredAlpha, alpha, beta,
      NoFiniteRejoin.alpha, NoFiniteRejoin.beta, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

theorem inverseDifference_not_mem_coefficientRing : inverseDifference ∉ coefficientRing := by
  intro h
  apply recoveredAlpha_not_mem_coefficientRing
  rw [← inverseDifference_mul_alpha]
  exact coefficientRing.mul_mem h alpha_mem_coefficientRing

theorem difference_mul_forwardPrime :
    (alpha - beta) * GaussianInt.toComplex forwardPrime =
      GaussianInt.toComplex conjugatePrime := by
  apply Complex.ext <;>
    norm_num [alpha, beta, NoFiniteRejoin.alpha, NoFiniteRejoin.beta,
      forwardPrime, conjugatePrime, GaussianInt.toComplex_def₂,
      Complex.mul_re, Complex.mul_im]

/-- All positive exponents are excluded by the symbolic residue argument. -/
theorem difference_no_positive_period (n : ℕ) (hn : 0 < n) :
    (alpha - beta) ^ n ≠ 1 := by
  intro hperiod
  have hcomplex : GaussianInt.toComplex conjugatePrime ^ n =
      GaussianInt.toComplex forwardPrime ^ n := by
    calc
      GaussianInt.toComplex conjugatePrime ^ n =
          ((alpha - beta) * GaussianInt.toComplex forwardPrime) ^ n := by
            rw [difference_mul_forwardPrime]
      _ = GaussianInt.toComplex forwardPrime ^ n := by
        rw [mul_pow, hperiod, one_mul]
  have hgaussian : conjugatePrime ^ n = forwardPrime ^ n := by
    apply GaussianInt.toComplex_injective
    simpa only [map_pow] using hcomplex
  have hresidue : (0 : ZMod 5) = (4 : ZMod 5) ^ n := by
    simpa only [map_pow, residue_conjugatePrime, residue_forwardPrime,
      zero_pow (Nat.ne_of_gt hn)] using congrArg residue hgaussian
  exact (pow_ne_zero n (by decide : (4 : ZMod 5) ≠ 0)) hresidue.symm

/-- The complete two-port function from the reused model. -/
abbrev forwardMixer : ℂ × ℂ → ℂ × ℂ :=
  FiniteRejoinReversibleQuadraticReadout.twoPort NoFiniteRejoin.A NoFiniteRejoin.B

theorem forwardMixer_antidiagonal (z : ℂ) :
    forwardMixer (z, -z) = ((alpha - beta) * z, -((alpha - beta) * z)) := by
  apply Prod.ext
  · change alpha * z + beta * (-z) = (alpha - beta) * z
    ring
  · change beta * z + alpha * (-z) = -((alpha - beta) * z)
    ring

theorem forwardMixer_iterate_antidiagonal (n : ℕ) (z : ℂ) :
    (forwardMixer^[n]) (z, -z) =
      ((alpha - beta) ^ n * z, -((alpha - beta) ^ n * z)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, forwardMixer_antidiagonal]
      apply Prod.ext <;> simp only [pow_succ] <;> ring

/-- No positive iterate of the full mixer is the identity function. -/
theorem forwardMixer_no_positive_period (n : ℕ) (hn : 0 < n) :
    (forwardMixer^[n]) ≠ id := by
  intro h
  have heval := congrFun h ((1 : ℂ), (-1 : ℂ))
  rw [forwardMixer_iterate_antidiagonal] at heval
  have hpower : (alpha - beta) ^ n = 1 := by
    simpa using congrArg Prod.fst heval
  exact difference_no_positive_period n hn hpower

/-- Scalar multiplication is a ring homomorphism into actual additive
endomorphisms, whose multiplication is composition. -/
def scalarEndHom : ℂ →+* AddMonoid.End ℂ where
  toFun := CanonicalComplex.scalarEnd
  map_zero' := by apply DFunLike.ext; intro z; change (0 : ℂ) * z = 0; simp
  map_one' := by apply DFunLike.ext; intro z; change (1 : ℂ) * z = z; simp
  map_add' c d := by apply DFunLike.ext; intro z; change (c + d) * z = c * z + d * z; ring
  map_mul' c d := by apply DFunLike.ext; intro z; change (c * d) * z = c * (d * z); ring

theorem scalarEndHom_injective : Function.Injective scalarEndHom := by
  intro c d h
  have heval := DFunLike.congr_fun h (1 : ℂ)
  change c * 1 = d * 1 at heval
  simpa using heval

/-- Actual endomorphism ring generated by the four allowed scalar operators. -/
def operatorRing : Subring (AddMonoid.End ℂ) :=
  Subring.closure (scalarEndHom '' forwardGenerators)

theorem operatorRing_eq_explicit : operatorRing =
    Subring.closure ({NoFiniteRejoin.A, NoFiniteRejoin.B,
      CanonicalComplex.scalarEnd alpha⁻¹, CanonicalComplex.scalarEnd beta⁻¹} :
        Set (AddMonoid.End ℂ)) := by
  simp only [operatorRing, forwardGenerators, Set.image_insert_eq, Set.image_singleton,
    scalarEndHom, NoFiniteRejoin.A, NoFiniteRejoin.B]
  rfl

theorem operatorRing_eq_map : operatorRing = coefficientRing.map scalarEndHom := by
  exact (RingHom.map_closure scalarEndHom forwardGenerators).symm

theorem scalarEnd_mem_operatorRing_iff (c : ℂ) :
    scalarEndHom c ∈ operatorRing ↔ c ∈ coefficientRing := by
  rw [operatorRing_eq_map, Subring.mem_map]
  constructor
  · rintro ⟨d, hd, hdc⟩
    exact scalarEndHom_injective hdc ▸ hd
  · intro hc
    exact ⟨c, hc, rfl⟩

/-- Operator-level exclusion. This concerns equality of actual functions,
as detected at input one, and allows the branch inverse operators. -/
theorem recoveredAlphaEnd_not_mem_operatorRing :
    scalarEndHom recoveredAlpha ∉ operatorRing := by
  simpa only [scalarEnd_mem_operatorRing_iff] using recoveredAlpha_not_mem_coefficientRing

theorem recoveredBetaEnd_not_mem_operatorRing :
    scalarEndHom recoveredBeta ∉ operatorRing := by
  simpa only [scalarEnd_mem_operatorRing_iff] using recoveredBeta_not_mem_coefficientRing

theorem inverseDifferenceEnd_not_mem_operatorRing :
    scalarEndHom inverseDifference ∉ operatorRing := by
  simpa only [scalarEnd_mem_operatorRing_iff] using inverseDifference_not_mem_coefficientRing

/-- Visible normalization anchors the reused complex control. -/
theorem normalized_model_input : Complex.normSq (1 : ℂ) = 1 := Complex.normSq_one

/-- The two recovered coefficients are conjugates in the reused concrete model. -/
theorem recoveredBeta_eq_conjugate : recoveredBeta = conj beta := by
  apply Complex.ext <;>
    norm_num [recoveredBeta, recoveredAlpha, alpha, beta,
      NoFiniteRejoin.alpha, NoFiniteRejoin.beta]

/-- Both inverse block equations hold in this concrete conserved model. -/
theorem concrete_recovery_blocks :
    alpha * recoveredAlpha + beta * recoveredBeta = 1 ∧
      alpha * recoveredBeta + beta * recoveredAlpha = 0 := by
  constructor <;> apply Complex.ext <;>
    norm_num [recoveredBeta, recoveredAlpha, alpha, beta,
      NoFiniteRejoin.alpha, NoFiniteRejoin.beta, Complex.mul_re, Complex.mul_im]

/-- The exact symmetric recovered mixer returns every pair. This is a
mathematical inverse already available in the ambient model. -/
theorem concrete_recovery_returns (x y : ℂ) :
    (alpha * (recoveredAlpha * x + recoveredBeta * y) +
        beta * (recoveredBeta * x + recoveredAlpha * y),
      beta * (recoveredAlpha * x + recoveredBeta * y) +
        alpha * (recoveredBeta * x + recoveredAlpha * y)) = (x, y) := by
  apply Prod.ext
  · calc
      _ = (alpha * recoveredAlpha + beta * recoveredBeta) * x +
          (alpha * recoveredBeta + beta * recoveredAlpha) * y := by ring
      _ = x := by rw [concrete_recovery_blocks.1, concrete_recovery_blocks.2]; ring
  · calc
      _ = (alpha * recoveredBeta + beta * recoveredAlpha) * x +
          (alpha * recoveredAlpha + beta * recoveredBeta) * y := by ring
      _ = y := by rw [concrete_recovery_blocks.1, concrete_recovery_blocks.2]; ring

/-- Introducing the odd denominator one fifth removes this specific gap. -/
theorem recoveredAlpha_eq_with_one_fifth :
    recoveredAlpha = (8 : ℂ) * (1 / 5 : ℂ) - alpha := by
  apply Complex.ext <;>
    norm_num [recoveredAlpha, alpha, NoFiniteRejoin.alpha]

/-- A finite positive-coefficient history expression realizes scalar negation.
Its operational use requires a separate recombination resource contract. -/
theorem positive_cubic_negation :
    (2 : ℂ) * alpha ^ 3 + 9 * alpha * beta ^ 2 + 11 * beta ^ 3 = -1 := by
  apply Complex.ext <;>
    norm_num [alpha, beta, NoFiniteRejoin.alpha, NoFiniteRejoin.beta,
      pow_succ, Complex.mul_re, Complex.mul_im]

end IDT.QMClosure.UnbalancedRecoveryOperatorRingWall
