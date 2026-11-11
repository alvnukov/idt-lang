import Proofs.QMClosure.FiniteTranslationDilationSupport
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Small complex translate rank excludes nontrivial dyadic spectral support

Finite dimensionality of the actual complex translate span is explicit.
The statements concern lattice functions and their actual readout components.
-/

noncomputable section

namespace FiniteTranslationSmallRankSupport

open FiniteTranslationSpectrum FiniteTranslationDilationSupport
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Counterclockwise quarter-turn on the integer lattice. -/
def turn (z : G) : G := (-z.2, z.1)

def unturn (z : G) : G := (z.2, -z.1)

@[simp] theorem turn_zero : turn 0 = 0 := rfl
@[simp] theorem unturn_zero : unturn 0 = 0 := rfl

@[simp] theorem turn_unturn (z : G) : turn (unturn z) = z := by
  ext <;> simp [turn, unturn]

@[simp] theorem unturn_turn (z : G) : unturn (turn z) = z := by
  ext <;> simp [turn, unturn]

@[simp] theorem turn_four (z : G) : turn (turn (turn (turn z))) = z := by
  ext <;> simp [turn]

def rotation : Module.End ℂ Ambient where
  toFun g z := g (turn z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- This identity uses the rotation law only for the original readout. -/
theorem rotation_translate_readout (f : Ambient)
    (hrot : ∀ z, f (turn z) = f z) (a : G) :
    rotation (translate a f) = translate (unturn a) f := by
  funext z
  change f (turn z + a) = f (z + unturn a)
  rw [← hrot (z + unturn a)]
  congr 1
  ext <;> simp [turn, unturn] <;> abel

theorem rotation_mem_translationSpan (f : Ambient)
    (hrot : ∀ z, f (turn z) = f z)
    {g : Ambient} (hg : g ∈ translationSpanC f) :
    rotation g ∈ translationSpanC f := by
  have hclosed : translationSpanC f ≤ (translationSpanC f).comap rotation := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change rotation (translate a f) ∈ translationSpanC f
    rw [rotation_translate_readout f hrot a]
    exact Submodule.subset_span ⟨unturn a, rfl⟩
  exact hclosed hg

def rotationEnd (f : Ambient) (hrot : ∀ z, f (turn z) = f z) :
    Module.End ℂ (TranslationSpace f) where
  toFun g := ⟨rotation g, rotation_mem_translationSpan f hrot g.property⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

@[simp] theorem rotationEnd_apply (f : Ambient)
    (hrot : ∀ z, f (turn z) = f z) (g : TranslationSpace f) (z : G) :
    ((rotationEnd f hrot g : TranslationSpace f) : Ambient) z = (g : Ambient) (turn z) := rfl

/-- Rotation preserves the actual translate span in both directions. -/
def rotationEquiv (f : Ambient) (hrot : ∀ z, f (turn z) = f z) :
    TranslationSpace f ≃ₗ[ℂ] TranslationSpace f where
  toFun := rotationEnd f hrot
  invFun g := rotationEnd f hrot (rotationEnd f hrot (rotationEnd f hrot g))
  left_inv g := by
    apply Subtype.ext
    funext z
    change (g : Ambient) (turn (turn (turn (turn z)))) = (g : Ambient) z
    rw [turn_four]
  right_inv g := by
    apply Subtype.ext
    funext z
    change (g : Ambient) (turn (turn (turn (turn z)))) = (g : Ambient) z
    rw [turn_four]
  map_add' := (rotationEnd f hrot).map_add
  map_smul' := (rotationEnd f hrot).map_smul

/-- The label action matching precomposition by the chosen quarter-turn. -/
def turnLabel (χ : Label) : Label := ![χ 1, (χ 0)⁻¹]

@[simp] theorem turnLabel_zero (χ : Label) : turnLabel χ 0 = χ 1 := rfl
@[simp] theorem turnLabel_one (χ : Label) : turnLabel χ 1 = (χ 0)⁻¹ := rfl

@[simp] theorem turnLabel_four (χ : Label) :
    turnLabel (turnLabel (turnLabel (turnLabel χ))) = χ := by
  funext i
  fin_cases i <;> simp [turnLabel]

theorem turnLabel_injective : Function.Injective turnLabel := by
  intro χ θ h
  have := congrArg (fun η => turnLabel (turnLabel (turnLabel η))) h
  simpa only [turnLabel_four] using this

/-- A negative coordinate shift, on the ambient lattice-function space. -/
def backward : Module.End ℂ Ambient := translateLinearMap (-coordinateStep 0)

def backwardDifference (eigenvalue : ℂ) : Module.End ℂ Ambient := backward - eigenvalue⁻¹ • 1

def backwardFactor (eigenvalue : ℂ) : Module.End ℂ Ambient := -eigenvalue⁻¹ • backward

/-- Inverse eigenvalue transport keeps its nonzero-eigenvalue premise explicit. -/
theorem backwardDifference_factor (eigenvalue : ℂ) (heigenvalue : eigenvalue ≠ 0) :
    backwardDifference eigenvalue = backwardFactor eigenvalue * difference 0 eigenvalue := by
  ext g z
  change g (z + -coordinateStep 0) - eigenvalue⁻¹ * g z =
    -eigenvalue⁻¹ * (g ((z + -coordinateStep 0) + coordinateStep 0) -
      eigenvalue * g (z + -coordinateStep 0))
  simp only [add_assoc, neg_add_cancel, add_zero]
  field_simp [heigenvalue] <;> ring

theorem backward_factors_commute (eigenvalue : ℂ) :
    Commute (backwardFactor eigenvalue) (difference 0 eigenvalue) := by
  change backwardFactor eigenvalue * difference 0 eigenvalue = difference 0 eigenvalue * backwardFactor eigenvalue
  ext g z
  change -eigenvalue⁻¹ * (g ((z + -coordinateStep 0) + coordinateStep 0) -
      eigenvalue * g (z + -coordinateStep 0)) =
    -eigenvalue⁻¹ * g ((z + coordinateStep 0) + -coordinateStep 0) -
      eigenvalue * (-eigenvalue⁻¹ * g (z + -coordinateStep 0))
  simp only [add_assoc, neg_add_cancel, add_neg_cancel, add_zero]
  ring

theorem backwardDifference_pow_zero (eigenvalue : ℂ) (heigenvalue : eigenvalue ≠ 0)
    (g : Ambient) (n : ℕ) (hn : (difference 0 eigenvalue ^ n) g = 0) :
    (backwardDifference eigenvalue ^ n) g = 0 := by
  rw [backwardDifference_factor eigenvalue heigenvalue, (backward_factors_commute eigenvalue).mul_pow]
  change (backwardFactor eigenvalue ^ n) ((difference 0 eigenvalue ^ n) g) = 0
  rw [hn, map_zero]

theorem rotation_difference_zero (χ : Label) (g : Ambient) :
    difference 0 (χ 1) (rotation g) = rotation (difference 1 (χ 1) g) := by
  ext z
  change g (turn (z + coordinateStep 0)) - χ 1 * g (turn z) =
    g (turn z + coordinateStep 1) - χ 1 * g (turn z)
  congr 2
  ext <;> simp [turn, coordinateStep]

theorem rotation_difference_one (χ : Label) (g : Ambient) :
    difference 1 ((χ 0)⁻¹) (rotation g) = rotation (backwardDifference (χ 0) g) := by
  ext z
  change g (turn (z + coordinateStep 1)) - (χ 0)⁻¹ * g (turn z) =
    g (turn z + -coordinateStep 0) - (χ 0)⁻¹ * g (turn z)
  congr 2
  ext <;> simp [turn, coordinateStep, add_comm]

/-- Ambient transport avoids assuming any support permutation under rotation. -/
theorem rotation_mem_ambientBlock {χ : Label} {g : Ambient}
    (hg : g ∈ ambientBlock χ) (hχ : χ 0 ≠ 0) :
    rotation g ∈ ambientBlock (turnLabel χ) := by
  apply (Submodule.mem_iInf _).mpr
  intro i
  fin_cases i
  · obtain ⟨n, hn⟩ :=
      (Module.End.mem_maxGenEigenspace (shift 1) (χ 1) g).mp
        ((Submodule.mem_iInf _).mp hg 1)
    apply (Module.End.mem_maxGenEigenspace (shift 0) (χ 1) (rotation g)).mpr
    refine ⟨n, ?_⟩
    change (difference 0 (χ 1) ^ n) (rotation g) = 0
    rw [intertwines_pow _ _ rotation (rotation_difference_zero χ) n g]
    change (difference 1 (χ 1) ^ n) g = 0 at hn
    rw [hn, map_zero]
  · obtain ⟨n, hn⟩ :=
      (Module.End.mem_maxGenEigenspace (shift 0) (χ 0) g).mp
        ((Submodule.mem_iInf _).mp hg 0)
    apply (Module.End.mem_maxGenEigenspace (shift 1) ((χ 0)⁻¹) (rotation g)).mpr
    refine ⟨n, ?_⟩
    change (difference 1 ((χ 0)⁻¹) ^ n) (rotation g) = 0
    rw [intertwines_pow _ _ rotation (rotation_difference_one χ) n g]
    change (difference 0 (χ 0) ^ n) g = 0 at hn
    rw [backwardDifference_pow_zero (χ 0) hχ g n hn, map_zero]

/-- Ambient block membership reflects to vectors already in the original span. -/
theorem jointBlock_mem_of_coe_mem_ambientBlock (f : Ambient) (χ : Label)
    {v : TranslationSpace f} (hv : (v : Ambient) ∈ ambientBlock χ) :
    v ∈ jointBlock f χ := by
  apply (Submodule.mem_iInf _).mpr
  intro i
  obtain ⟨n, hn⟩ :=
    (Module.End.mem_maxGenEigenspace (shift i) (χ i) (v : Ambient)).mp
      ((Submodule.mem_iInf _).mp hv i)
  apply (Module.End.mem_maxGenEigenspace (coordinateEnd f i) (χ i) v).mpr
  refine ⟨n, ?_⟩
  let inclusion : TranslationSpace f →ₗ[ℂ] Ambient := (translationSpanC f).subtype
  have hinter : ∀ w : TranslationSpace f,
      difference i (χ i) (inclusion w) =
        inclusion ((coordinateEnd f i - (χ i) • 1) w) := by
    intro w
    ext z
    rfl
  apply Subtype.ext
  change inclusion (((coordinateEnd f i - (χ i) • 1) ^ n) v) = 0
  rw [← intertwines_pow _ _ inclusion hinter n v]
  exact hn

theorem rotationEnd_mem_jointBlock (f : Ambient)
    (hrot : ∀ z, f (turn z) = f z) {χ : Label}
    {v : TranslationSpace f} (hv : v ∈ jointBlock f χ) (hχ : χ 0 ≠ 0) :
    rotationEnd f hrot v ∈ jointBlock f (turnLabel χ) := by
  apply jointBlock_mem_of_coe_mem_ambientBlock
  exact rotation_mem_ambientBlock (coe_mem_ambientBlock f χ hv) hχ

section FiniteDimension

variable (f : Ambient) [FiniteDimensional ℂ (TranslationSpace f)]

/-- Iterating dilation at zero follows the already established finite permutation. -/
theorem component_zero_cycle (hscale : ∀ z, f (z + z) = 4 * f z)
    (n : ℕ) (χ : Supported f) :
    component f χ.val 0 = (4 : ℂ) ^ n *
      component f (((squarePerm f hscale ^ n) χ).val) 0 := by
  induction n generalizing χ with
  | zero => simp
  | succ n ih =>
    have hstep := congrFun (dilate_component f hscale χ.val χ.property) 0
    change component f χ.val 0 = 4 * component f (squarePerm f hscale χ).val 0 at hstep
    rw [hstep, ih (squarePerm f hscale χ)]
    rw [pow_succ]
    have harg :
        ((squarePerm f hscale ^ n) (squarePerm f hscale χ)).val =
          ((squarePerm f hscale ^ (n + 1)) χ).val := by
      rw [pow_succ, Equiv.Perm.mul_apply]
    rw [harg]
    ring

/-- Every actual readout component vanishes at the origin, including zero components. -/
theorem component_zero (hscale : ∀ z, f (z + z) = 4 * f z) (χ : Label) :
    component f χ 0 = 0 := by
  by_cases hχ : χ ∈ support f
  · let π := squarePerm f hscale
    have hk : 0 < orderOf π := orderOf_pos π
    have hcycle := component_zero_cycle f hscale (orderOf π) ⟨χ, hχ⟩
    have hperm : squarePerm f hscale ^ orderOf π = 1 := pow_orderOf_eq_one π
    rw [hperm] at hcycle
    change component f χ 0 = (4 : ℂ) ^ orderOf π * component f χ 0 at hcycle
    have hpow : (4 : ℂ) ^ orderOf π ≠ 1 := by
      exact_mod_cast (ne_of_gt (one_lt_pow₀ (show (1 : ℕ) < 4 by decide) hk.ne'))
    have hmul : ((4 : ℂ) ^ orderOf π - 1) * component f χ 0 = 0 := by
      calc
        _ = (4 : ℂ) ^ orderOf π * component f χ 0 - component f χ 0 := by ring
        _ = 0 := sub_eq_zero.mpr hcycle.symm
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hpow)
  · rw [component_eq_zero_of_not_mem_support f hχ]
    rfl

end FiniteDimension

/-- An odd-order complex root whose square is one must itself be one. -/
theorem eq_one_of_square_eq_one_of_odd_period {c : ℂ} {M : ℕ}
    (hodd : Odd M) (hperiod : c ^ M = 1) (hsq : c ^ 2 = 1) : c = 1 := by
  obtain ⟨n, hn⟩ := hodd
  have hvalue : c ^ M = c := by
    rw [hn, pow_add, pow_mul, hsq]
    simp
  exact hvalue.symm.trans hperiod

/-- A half-turn fixed label with common odd period is trivial. -/
theorem eq_one_of_turnLabel_twice_eq {χ : Label} {M : ℕ}
    (hodd : Odd M) (hperiod : ∀ i, χ i ^ M = 1)
    (hfixed : turnLabel (turnLabel χ) = χ) : χ = fun _ => 1 := by
  funext i
  have hinv : (χ i)⁻¹ = χ i := by
    fin_cases i
    · simpa [turnLabel] using congrFun hfixed 0
    · simpa [turnLabel] using congrFun hfixed 1
  have hc : χ i ≠ 0 := by
    intro hz
    have := hperiod i
    have hM : M ≠ 0 := by
      obtain ⟨n, hn⟩ := hodd
      omega
    simp [hz, hM] at this
  apply eq_one_of_square_eq_one_of_odd_period hodd (hperiod i)
  calc
    χ i ^ 2 = χ i * χ i := by ring
    _ = χ i * (χ i)⁻¹ := by rw [hinv]
    _ = 1 := mul_inv_cancel₀ hc

def labelOrbit (χ : Label) : Fin 4 → Label :=
  ![χ, turnLabel χ, turnLabel (turnLabel χ), turnLabel (turnLabel (turnLabel χ))]

/-- The four labels are distinct using odd period only, with no actual-support transport. -/
theorem labelOrbit_injective {χ : Label} {M : ℕ}
    (hodd : Odd M) (hperiod : ∀ i, χ i ^ M = 1) (hne : χ ≠ fun _ => 1) :
    Function.Injective (labelOrbit χ) := by
  have h02 : χ ≠ turnLabel (turnLabel χ) := by
    intro h
    exact hne (eq_one_of_turnLabel_twice_eq hodd hperiod h.symm)
  have h01 : χ ≠ turnLabel χ := by
    intro h
    exact h02 (h.trans (congrArg turnLabel h))
  have h03 : χ ≠ turnLabel (turnLabel (turnLabel χ)) := by
    intro h
    have ht : turnLabel χ = χ := by
      simpa only [turnLabel_four] using congrArg turnLabel h
    exact h01 ht.symm
  have h12 : turnLabel χ ≠ turnLabel (turnLabel χ) := by
    intro h
    exact h01 (turnLabel_injective h)
  have h13 : turnLabel χ ≠ turnLabel (turnLabel (turnLabel χ)) := by
    intro h
    exact h02 (turnLabel_injective h)
  have h23 : turnLabel (turnLabel χ) ≠ turnLabel (turnLabel (turnLabel χ)) := by
    intro h
    exact h12 (turnLabel_injective h)
  intro k l h
  fin_cases k <;> fin_cases l <;> simp_all [labelOrbit]

/-- Four rotated vectors, still in the original translate span. -/
def vectorOrbit (f : Ambient) (hrot : ∀ z, f (turn z) = f z)
    (v : TranslationSpace f) : Fin 4 → TranslationSpace f :=
  ![v, rotationEnd f hrot v, rotationEnd f hrot (rotationEnd f hrot v),
    rotationEnd f hrot (rotationEnd f hrot (rotationEnd f hrot v))]

def pointOrbit (a : G) : Fin 4 → G := ![a, unturn a, -a, turn a]

theorem vectorOrbit_at_point (f : Ambient) (hrot : ∀ z, f (turn z) = f z)
    (v : TranslationSpace f) (a : G) (k : Fin 4) :
    (vectorOrbit f hrot v k : Ambient) (pointOrbit a k) = (v : Ambient) a := by
  fin_cases k <;> simp [vectorOrbit, pointOrbit, turn, unturn, rotationEnd_apply]

theorem vectorOrbit_zero (f : Ambient) (hrot : ∀ z, f (turn z) = f z)
    (v : TranslationSpace f) (hv : (v : Ambient) 0 = 0) (k : Fin 4) :
    (vectorOrbit f hrot v k : Ambient) 0 = 0 := by
  fin_cases k <;> simp [vectorOrbit, rotationEnd_apply, hv]

theorem vectorOrbit_mem_jointBlock (f : Ambient) (hrot : ∀ z, f (turn z) = f z)
    {χ : Label} {v : TranslationSpace f} (hv : v ∈ jointBlock f χ)
    (hχ : ∀ i, χ i ≠ 0) (k : Fin 4) :
    vectorOrbit f hrot v k ∈ jointBlock f (labelOrbit χ k) := by
  have hv1 := rotationEnd_mem_jointBlock f hrot hv (hχ 0)
  have hv2 := rotationEnd_mem_jointBlock f hrot hv1 (by simpa using hχ 1)
  have hv3 := rotationEnd_mem_jointBlock f hrot hv2 (by simpa using inv_ne_zero (hχ 0))
  fin_cases k
  · simpa [vectorOrbit, labelOrbit] using hv
  · simpa [vectorOrbit, labelOrbit] using hv1
  · simpa [vectorOrbit, labelOrbit] using hv2
  · simpa [vectorOrbit, labelOrbit] using hv3

/-- Two vectors in each orbit block, separated by evaluation at the origin. -/
def orbitPair (f : Ambient) (hrot : ∀ z, f (turn z) = f z)
    (v : TranslationSpace f) (a : G) (k : Fin 4) : Fin 2 → TranslationSpace f :=
  ![vectorOrbit f hrot v k,
    translationEnd f (pointOrbit a k) (vectorOrbit f hrot v k)]

theorem orbitPair_mem_jointBlock (f : Ambient) (hrot : ∀ z, f (turn z) = f z)
    {χ : Label} {v : TranslationSpace f} (hv : v ∈ jointBlock f χ)
    (hχ : ∀ i, χ i ≠ 0) (a : G) (k : Fin 4) (j : Fin 2) :
    orbitPair f hrot v a k j ∈ jointBlock f (labelOrbit χ k) := by
  have hk := vectorOrbit_mem_jointBlock f hrot hv hχ k
  fin_cases j
  · exact hk
  · exact translationEnd_mapsTo_jointBlock f (pointOrbit a k) _ hk

/-- The actual component's zero-origin property creates two independent vectors per block. -/
theorem orbitPair_linearIndependent (f : Ambient)
    (hrot : ∀ z, f (turn z) = f z) (v : TranslationSpace f)
    (hv0 : (v : Ambient) 0 = 0) (a : G) (hva : (v : Ambient) a ≠ 0) (k : Fin 4) :
    LinearIndependent ℂ (orbitPair f hrot v a k) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hsum j
  have hpair :
      c 0 • vectorOrbit f hrot v k +
        c 1 • translationEnd f (pointOrbit a k) (vectorOrbit f hrot v k) = 0 := by
    simpa [Fin.sum_univ_two, orbitPair] using hsum
  have heval0 := congrArg (fun w : TranslationSpace f => (w : Ambient) 0) hpair
  have hczero : c 1 = 0 := by
    have hmul : c 1 * (v : Ambient) a = 0 := by
      simpa [vectorOrbit_zero f hrot v hv0 k, translationEnd_apply,
        vectorOrbit_at_point f hrot v a k] using heval0
    exact (mul_eq_zero.mp hmul).resolve_right hva
  have hevala := congrArg
    (fun w : TranslationSpace f => (w : Ambient) (pointOrbit a k)) hpair
  have hcone : c 0 = 0 := by
    have hmul : c 0 * (v : Ambient) a = 0 := by
      simpa [hczero, vectorOrbit_at_point f hrot v a k] using hevala
    exact (mul_eq_zero.mp hmul).resolve_right hva
  fin_cases j <;> assumption

/-- Combining independent pairs in four independent joint blocks gives eight vectors. -/
theorem orbitPairs_linearIndependent (f : Ambient)
    (hrot : ∀ z, f (turn z) = f z) {χ : Label} (v : TranslationSpace f)
    (hv : v ∈ jointBlock f χ) (hχ : ∀ i, χ i ≠ 0)
    (hinj : Function.Injective (labelOrbit χ))
    (hv0 : (v : Ambient) 0 = 0) (a : G) (hva : (v : Ambient) a ≠ 0) :
    LinearIndependent ℂ (fun p : Fin 4 × Fin 2 => orbitPair f hrot v a p.1 p.2) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hsum p
  have hind : iSupIndep (fun k : Fin 4 => jointBlock f (labelOrbit χ k)) :=
    (jointBlock_independent f).comp hinj
  have hgrouped :
      ∑ k : Fin 4, ∑ j : Fin 2, c (k, j) • orbitPair f hrot v a k j = 0 := by
    simpa only [Fintype.sum_prod_type] using hsum
  have hzero :=
    (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero _).mp hind Finset.univ
      (fun k => ∑ j : Fin 2, c (k, j) • orbitPair f hrot v a k j)
      (by
        intro k _
        apply (jointBlock f (labelOrbit χ k)).sum_mem
        intro j _
        exact (jointBlock f (labelOrbit χ k)).smul_mem _
          (orbitPair_mem_jointBlock f hrot hv hχ a k j)) hgrouped p.1 (Finset.mem_univ _)
  exact Fintype.linearIndependent_iff.mp
    (orbitPair_linearIndependent f hrot v hv0 a hva p.1) (fun j => c (p.1, j)) hzero p.2

section FiniteDimension

variable (f : Ambient) [FiniteDimensional ℂ (TranslationSpace f)]

/-- Any supported nontrivial label costs at least eight complex translation dimensions. -/
theorem eight_le_finrank_of_supported_nontrivial
    (hscale : ∀ z, f (z + z) = 4 * f z)
    (hrot : ∀ z, f (turn z) = f z)
    {χ : Label} (hχ : χ ∈ support f) (hne : χ ≠ fun _ => 1) :
    8 ≤ Module.finrank ℂ (TranslationSpace f) := by
  obtain ⟨M, _hMpos, hModd, hM⟩ := exists_common_odd_period f hscale
  have hcomponent : component f χ ≠ 0 := (mem_support_iff f χ).mp hχ
  obtain ⟨a, ha⟩ : ∃ a : G, component f χ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hcomponent (funext h)
  let v : TranslationSpace f := readoutComponents f χ
  have hv0 : (v : Ambient) 0 = 0 := component_zero f hscale χ
  have hva : (v : Ambient) a ≠ 0 := ha
  have hind := orbitPairs_linearIndependent f hrot v (readoutComponents_mem f χ)
    (component_coordinate_ne_zero f hχ)
    (labelOrbit_injective hModd (hM χ hχ) hne) hv0 a hva
  simpa using hind.fintype_card_le_finrank

/-- Zero and empty support are allowed. Calibration is unnecessary for this exclusion. -/
theorem supported_eq_one_of_finrank_lt_eight
    (hscale : ∀ z, f (z + z) = 4 * f z)
    (hrot : ∀ z, f (turn z) = f z)
    (hrank : Module.finrank ℂ (TranslationSpace f) < 8)
    {χ : Label} (hχ : χ ∈ support f) : χ = fun _ => 1 := by
  by_contra hne
  exact (not_le_of_gt hrank)
    (eight_le_finrank_of_supported_nontrivial f hscale hrot hχ hne)

end FiniteDimension

end FiniteTranslationSmallRankSupport
