import Proofs.QMClosure.FiniteTranslationSpectrum
import Proofs.QMClosure.FiniteDifferencePolynomial

/-!
# Finite exponential-polynomial existence for finite global translate rank

Algebraic existence using joint spectral decomposition and finite differences.
Finite dimension is explicit. The conclusion is an algebraic existence theorem
for complex-valued functions on the integer lattice. It supplies no general
uniqueness theorem, dilation classification, real-rank transfer, or physical
interpretation.
-/

noncomputable section

namespace IDT.TranslationRankGap

open FiniteTranslationSpectrum
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- A character specified by its coordinate values. Nonzero coordinates are
required separately by the laws that use integer-exponent addition. -/
def latticeCharacter (χ : Fin 2 → ℂ) (z : IntegerLattice) : ℂ :=
  (χ 0) ^ z.1 * (χ 1) ^ z.2

theorem latticeCharacter_ne_zero (χ : Fin 2 → ℂ)
    (hχ : ∀ i, χ i ≠ 0) (z : IntegerLattice) :
    latticeCharacter χ z ≠ 0 :=
  mul_ne_zero (zpow_ne_zero z.1 (hχ 0)) (zpow_ne_zero z.2 (hχ 1))

@[simp] theorem latticeCharacter_zero (χ : Fin 2 → ℂ) :
    latticeCharacter χ 0 = 1 := by
  simp [latticeCharacter]

theorem latticeCharacter_add (χ : Fin 2 → ℂ)
    (hχ : ∀ i, χ i ≠ 0) (z w : IntegerLattice) :
    latticeCharacter χ (z + w) =
      latticeCharacter χ z * latticeCharacter χ w := by
  rcases z with ⟨m, n⟩
  rcases w with ⟨r, s⟩
  simp only [latticeCharacter, Prod.fst_add, Prod.snd_add]
  rw [zpow_add₀ (hχ 0), zpow_add₀ (hχ 1)]
  ring

@[simp] theorem latticeCharacter_coordinateStep (χ : Fin 2 → ℂ) (i : Fin 2) :
    latticeCharacter χ (coordinateStep i) = χ i := by
  fin_cases i <;> simp [latticeCharacter, coordinateStep]

theorem latticeCharacter_add_coordinateStep (χ : Fin 2 → ℂ)
    (hχ : ∀ i, χ i ≠ 0) (z : IntegerLattice) (i : Fin 2) :
    latticeCharacter χ (z + coordinateStep i) = latticeCharacter χ z * χ i := by
  rw [latticeCharacter_add χ hχ, latticeCharacter_coordinateStep]

/-- Division by the character is complex-linear on the translate module. -/
def characterTwistLinearMap (f : IntegerLattice → ℂ) (χ : Fin 2 → ℂ) :
    TranslationSpace f →ₗ[ℂ] (IntegerLattice → ℂ) where
  toFun v z := (v : IntegerLattice → ℂ) z / latticeCharacter χ z
  map_add' v w := by
    funext z
    exact add_div ((v : IntegerLattice → ℂ) z)
      ((w : IntegerLattice → ℂ) z) (latticeCharacter χ z)
  map_smul' c v := by
    funext z
    exact mul_div_assoc c ((v : IntegerLattice → ℂ) z) (latticeCharacter χ z)

@[simp] theorem characterTwistLinearMap_apply (f : IntegerLattice → ℂ)
    (χ : Fin 2 → ℂ) (v : TranslationSpace f) (z : IntegerLattice) :
    characterTwistLinearMap f χ v z = (v : IntegerLattice → ℂ) z / latticeCharacter χ z := rfl

def coordinatePrimaryDifference (f : IntegerLattice → ℂ) (χ : Fin 2 → ℂ)
    (i : Fin 2) : Module.End ℂ (TranslationSpace f) :=
  coordinateEnd f i - χ i • 1

/-- The twist intertwines the primary operator with a scalar multiple of the
coordinate forward difference. This holds on the entire translate module. -/
theorem characterTwist_primaryDifference (f : IntegerLattice → ℂ)
    (χ : Fin 2 → ℂ) (hχ : ∀ i, χ i ≠ 0) (i : Fin 2)
    (v : TranslationSpace f) :
    characterTwistLinearMap f χ (coordinatePrimaryDifference f χ i v) =
      χ i • fwdDiff (coordinateStep i) (characterTwistLinearMap f χ v) := by
  funext z
  change ((v : IntegerLattice → ℂ) (z + coordinateStep i) -
      χ i * (v : IntegerLattice → ℂ) z) / latticeCharacter χ z =
    χ i * ((v : IntegerLattice → ℂ) (z + coordinateStep i) / latticeCharacter χ (z + coordinateStep i) -
      (v : IntegerLattice → ℂ) z / latticeCharacter χ z)
  rw [latticeCharacter_add_coordinateStep χ hχ]
  field_simp [latticeCharacter_ne_zero χ hχ z, hχ i]

/-- Equivalent inverse-scalar form of the one-step intertwining identity. -/
theorem fwdDiff_characterTwist (f : IntegerLattice → ℂ)
    (χ : Fin 2 → ℂ) (hχ : ∀ i, χ i ≠ 0) (i : Fin 2)
    (v : TranslationSpace f) :
    fwdDiff (coordinateStep i) (characterTwistLinearMap f χ v) =
      (χ i)⁻¹ • characterTwistLinearMap f χ
        (coordinatePrimaryDifference f χ i v) := by
  rw [characterTwist_primaryDifference f χ hχ i v]
  simp only [smul_smul, inv_mul_cancel₀ (hχ i), one_smul]

/-- Iterated intertwining, preserving the same global function domain. -/
theorem characterTwist_primaryDifference_pow (f : IntegerLattice → ℂ)
    (χ : Fin 2 → ℂ) (hχ : ∀ i, χ i ≠ 0) (i : Fin 2) (k : ℕ)
    (v : TranslationSpace f) :
    characterTwistLinearMap f χ (((coordinatePrimaryDifference f χ i) ^ k) v) =
      (χ i) ^ k •
        (fwdDiff (coordinateStep i))^[k] (characterTwistLinearMap f χ v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply,
      characterTwist_primaryDifference f χ hχ i, ih, fwdDiff_const_smul]
    simp only [smul_smul, pow_succ', Function.iterate_succ_apply']

/-- Each joint generalized eigenfunction becomes a globally finite-difference
polynomial sequence after division by its character. -/
theorem exists_coordinate_annihilator_of_jointBlock_mem
    (f : IntegerLattice → ℂ) (χ : Fin 2 → ℂ) (hχ : ∀ i, χ i ≠ 0)
    (v : TranslationSpace f) (hv : v ∈ jointBlock f χ) (i : Fin 2) :
    ∃ k : ℕ, (fwdDiff (coordinateStep i))^[k]
      (characterTwistLinearMap f χ v) = 0 := by
  have hvi : v ∈ (coordinateEnd f i).maxGenEigenspace (χ i) :=
    (Submodule.mem_iInf _).mp hv i
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace
    (coordinateEnd f i) (χ i) v).mp hvi
  change ((coordinatePrimaryDifference f χ i) ^ k) v = 0 at hk
  refine ⟨k, ?_⟩
  have hinter := characterTwist_primaryDifference_pow f χ hχ i k v
  rw [hk, map_zero] at hinter
  have hscalar : (χ i) ^ k ≠ 0 := pow_ne_zero k (hχ i)
  funext z
  have hz := congrFun hinter z
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hz
  exact (mul_eq_zero.mp hz.symm).resolve_left hscalar

/-- A single joint-primary vector is a polynomial times its coordinate character. -/
theorem exists_polynomial_of_jointBlock_mem
    (f : IntegerLattice → ℂ) (χ : Fin 2 → ℂ) (hχ : ∀ i, χ i ≠ 0)
    (v : TranslationSpace f) (hv : v ∈ jointBlock f χ) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      ∀ m n : ℤ, (v : IntegerLattice → ℂ) (m, n) =
        MvPolynomial.eval ![(m : ℂ), (n : ℂ)] P * latticeCharacter χ (m, n) := by
  obtain ⟨d, hx⟩ := exists_coordinate_annihilator_of_jointBlock_mem f χ hχ v hv 0
  obtain ⟨e, hy⟩ := exists_coordinate_annihilator_of_jointBlock_mem f χ hχ v hv 1
  have hx' : (fwdDiff ((1, 0) : IntegerLattice))^[d]
      (characterTwistLinearMap f χ v) = 0 := by
    simpa only [coordinateStep, if_pos rfl] using hx
  have hy' : (fwdDiff ((0, 1) : IntegerLattice))^[e]
      (characterTwistLinearMap f χ v) = 0 := by
    simpa [coordinateStep] using hy
  obtain ⟨P, hP, _⟩ := existsUnique_polynomial_of_coordinate_fwdDiff_eq_zero
    (characterTwistLinearMap f χ v) d e hx' hy'
  refine ⟨P, ?_⟩
  intro m n
  have hvalue := hP m n
  change (v : IntegerLattice → ℂ) (m, n) / latticeCharacter χ (m, n) =
    MvPolynomial.eval ![(m : ℂ), (n : ℂ)] P at hvalue
  exact (div_eq_iff (latticeCharacter_ne_zero χ hχ (m, n))).mp hvalue

theorem exists_nonzero_polynomial_of_jointBlock_mem
    (f : IntegerLattice → ℂ) (χ : Fin 2 → ℂ) (hχ : ∀ i, χ i ≠ 0)
    (v : TranslationSpace f) (hv : v ∈ jointBlock f χ) (hne : v ≠ 0) :
    ∃ P : MvPolynomial (Fin 2) ℂ, P ≠ 0 ∧
      ∀ m n : ℤ, (v : IntegerLattice → ℂ) (m, n) =
        MvPolynomial.eval ![(m : ℂ), (n : ℂ)] P * latticeCharacter χ (m, n) := by
  obtain ⟨P, hP⟩ := exists_polynomial_of_jointBlock_mem f χ hχ v hv
  refine ⟨P, ?_, hP⟩
  intro hzero
  apply hne
  apply Subtype.ext
  funext z
  rcases z with ⟨m, n⟩
  simpa only [hzero, map_zero, zero_mul, Pi.zero_apply] using hP m n

section FiniteDimension

variable (f : IntegerLattice → ℂ) [FiniteDimensional ℂ (TranslationSpace f)]

theorem readoutComponent_ne_zero_of_mem_support (χ : Fin 2 → ℂ)
    (hχ : χ ∈ (readoutComponents f).support) :
    (readoutComponents f χ : TranslationSpace f) ≠ 0 := by
  intro hzero
  apply (DFinsupp.mem_support_iff.mp hχ)
  exact Subtype.ext hzero

/-- Finite global translate rank gives a finite exponential-polynomial expansion.
The support is the actual support of the joint-primary readout decomposition.
The coefficient map is zero outside that finite support. The zero function is
included without an additional nontriviality premise. -/
theorem exists_finite_exponentialPolynomial :
    ∃ (S : Finset (Fin 2 → ℂ))
      (P : (Fin 2 → ℂ) → MvPolynomial (Fin 2) ℂ),
      S = (readoutComponents f).support ∧
      (∀ χ ∈ S, ∀ i : Fin 2, χ i ≠ 0) ∧
      (∀ χ ∈ S, P χ ≠ 0) ∧
      (∀ χ ∉ S, P χ = 0) ∧
      (∀ χ ∈ S, ∀ m n : ℤ,
        ((readoutComponents f χ : TranslationSpace f) : IntegerLattice → ℂ) (m, n) =
          MvPolynomial.eval ![(m : ℂ), (n : ℂ)] (P χ) * latticeCharacter χ (m, n)) ∧
      ∀ m n : ℤ,
        f (m, n) = ∑ χ ∈ S,
          MvPolynomial.eval ![(m : ℂ), (n : ℂ)] (P χ) * (χ 0) ^ m * (χ 1) ^ n := by
  classical
  let S : Finset (Fin 2 → ℂ) := (readoutComponents f).support
  have hcoordinate (χ : Fin 2 → ℂ) (hχ : χ ∈ S) : ∀ i, χ i ≠ 0 :=
    readoutComponents_coordinate_ne_zero f χ
      (readoutComponent_ne_zero_of_mem_support f χ hχ)
  have hex (χ : {χ : Fin 2 → ℂ // χ ∈ S}) :
      ∃ P : MvPolynomial (Fin 2) ℂ, P ≠ 0 ∧
        ∀ m n : ℤ, ((readoutComponents f χ.val : TranslationSpace f) : IntegerLattice → ℂ) (m, n) =
          MvPolynomial.eval ![(m : ℂ), (n : ℂ)] P * latticeCharacter χ.val (m, n) :=
    exists_nonzero_polynomial_of_jointBlock_mem f χ.val
      (hcoordinate χ.val χ.property) (readoutComponents f χ.val)
      (readoutComponents_mem f χ.val)
      (readoutComponent_ne_zero_of_mem_support f χ.val χ.property)
  let poly : {χ : Fin 2 → ℂ // χ ∈ S} → MvPolynomial (Fin 2) ℂ :=
    fun χ => Classical.choose (hex χ)
  have hpoly (χ : {χ : Fin 2 → ℂ // χ ∈ S}) :
      poly χ ≠ 0 ∧ ∀ m n : ℤ,
        ((readoutComponents f χ.val : TranslationSpace f) : IntegerLattice → ℂ) (m, n) =
          MvPolynomial.eval ![(m : ℂ), (n : ℂ)] (poly χ) *
            latticeCharacter χ.val (m, n) :=
    Classical.choose_spec (hex χ)
  let P : (Fin 2 → ℂ) → MvPolynomial (Fin 2) ℂ := fun χ =>
    if hχ : χ ∈ S then poly ⟨χ, hχ⟩ else 0
  have hP (χ : Fin 2 → ℂ) (hχ : χ ∈ S) : P χ = poly ⟨χ, hχ⟩ := by
    simp only [P, dif_pos hχ]
  have hrepresentation (χ : Fin 2 → ℂ) (hχ : χ ∈ S) (m n : ℤ) :
      ((readoutComponents f χ : TranslationSpace f) : IntegerLattice → ℂ) (m, n) =
        MvPolynomial.eval ![(m : ℂ), (n : ℂ)] (P χ) * latticeCharacter χ (m, n) := by
    rw [hP χ hχ]
    exact (hpoly ⟨χ, hχ⟩).2 m n
  refine ⟨S, P, rfl, hcoordinate, ?_, ?_, hrepresentation, ?_⟩
  · intro χ hχ
    rw [hP χ hχ]
    exact (hpoly ⟨χ, hχ⟩).1
  · intro χ hχ
    simp only [P, dif_neg hχ]
  · intro m n
    let ev : TranslationSpace f →ₗ[ℂ] ℂ :=
      { toFun := fun v => (v : IntegerLattice → ℂ) (m, n)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hsum := congrArg (fun v : TranslationSpace f => ev v) (sum_readoutComponents f)
    simp only [map_sum] at hsum
    calc
      f (m, n) = ∑ χ ∈ S,
          ((readoutComponents f χ : TranslationSpace f) : IntegerLattice → ℂ) (m, n) := by
        simpa only [S, ev, original] using hsum.symm
      _ = ∑ χ ∈ S,
          MvPolynomial.eval ![(m : ℂ), (n : ℂ)] (P χ) * (χ 0) ^ m * (χ 1) ^ n := by
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [hrepresentation χ hχ m n]
        simp only [latticeCharacter, mul_assoc]

end FiniteDimension

end IDT.TranslationRankGap
