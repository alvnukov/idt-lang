import Proofs.QMClosure.NativeAllocatedSignatureLaw
import Proofs.QMClosure.NativeGaussianDyadicDensity
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Analysis.Complex.Norm

/-!
# A supplied open constant patch excludes dense hidden response fibers

The carrier is the existing exact scalar generated carrier. Its ordinary complex subspace topology is supplied. The signature has
an arbitrary codomain, without any topology or continuity assumption there.

Distinct response-equivalent inputs yield a nonzero global contextual period.
Explicit generated references solve the first/second mixer output for every
generated base point. Contextual periods form an additive subgroup stable under
both mixer coefficients, hence under multiplication by i and division by two.
Their Gaussian-dyadic multiples are dense by the existing finite-program
approximation theorem. Consequently every nonempty signature fiber is dense.

A nonempty relatively open constant region therefore forces a signature with
a distinct response-equivalent pair to be globally constant. With this local
patch supplied, nonconstancy, full contextual separation, and existence of the
existing six-field single-basis-reference law are equivalent. The law criterion
uses canonical scalar consistency only for sufficiency; no observational or
physical probability provenance is inferred.

All references remain exact finite allocated known preparations in the same
supplied scalar frame. Contexts retain exactly one unknown hole. No unknown
cloning, uniform source budget, algorithmic/precision/noise bound, physical
reference availability, joint-input probability extension, topology derivation,
tensor structure, actualization, or QM closure is asserted.
-/

namespace IDT.QMClosure.NativeAllocatedStableObservation

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open OperationalContextQuotient ResponseContextQuotient
open NativeAllocatedObservationBoundary NativeAllocatedSourceArithmetic
open NativeAllocatedSignatureLaw
open NativeAttenuationCircuit (a b mixer_fst mixer_snd)

variable {Ω : Type*}

/-- This is an algebraic presentation of the already fixed generated carrier,
not an enlarged reference domain. Closure is witnessed by the actual macros. -/
private def reachableAddSubgroup : AddSubgroup ℂ where
  carrier := Reachable
  zero_mem' := ⟨NativeAllocatedSourceArithmetic.zero, value_zero⟩
  add_mem' := by
    rintro x y ⟨p, hp⟩ ⟨q, hq⟩
    exact ⟨NativeAllocatedSourceArithmetic.add p q, by rw [value_add, hp, hq]⟩
  neg_mem' := by
    rintro x ⟨p, hp⟩
    exact ⟨negate p, by rw [value_negate, hp]⟩

local instance : AddCommGroup G :=
  inferInstanceAs (AddCommGroup reachableAddSubgroup)

/-- The ordinary complex subspace metric; no new topology is quantified over. -/
instance generatedPseudoMetricSpace : PseudoMetricSpace G :=
  inferInstanceAs (PseudoMetricSpace {z : ℂ // Reachable z})

@[simp] private theorem coe_zero : (0 : G).val = 0 := rfl
@[simp] private theorem coe_add (x y : G) : (x + y).val = x.val + y.val := rfl
@[simp] private theorem coe_neg (x : G) : (-x).val = -x.val := rfl
@[simp] private theorem coe_sub (x y : G) : (x - y).val = x.val - y.val := rfl

@[simp] private theorem coe_zsmul (n : ℤ) (x : G) :
    (n • x).val = (n : ℂ) * x.val := by
  change n • x.val = (n : ℂ) * x.val
  simp only [zsmul_eq_mul]

private def chosenProgram (x : G) : ScalarProgram := Classical.choose x.property

@[simp] private theorem value_chosenProgram (x : G) :
    value (chosenProgram x) = x.val := Classical.choose_spec x.property

private def imagG (x : G) : G := ofProgram (phasePlus (chosenProgram x))
private def halfG (x : G) : G := ofProgram (half (chosenProgram x))

@[simp] private theorem coe_imagG (x : G) : (imagG x).val = Complex.I * x.val := by
  simp only [imagG, val_ofProgram, value_phasePlus, value_chosenProgram]

@[simp] private theorem coe_halfG (x : G) : (halfG x).val = x.val / 2 := by
  simp only [halfG, val_ofProgram, value_half, value_chosenProgram]

private def aG (x : G) : G := (operationG (x, zeroG)).1
private def bG (x : G) : G := (operationG (zeroG, x)).1

@[simp] private theorem coe_operation_fst (x y : G) :
    (operationG (x, y)).1.val = a * x.val + b * y.val := mixer_fst _ _

@[simp] private theorem coe_operation_snd (x y : G) :
    (operationG (x, y)).2.val = b * x.val + a * y.val := mixer_snd _ _

@[simp] private theorem coe_aG (x : G) : (aG x).val = a * x.val := by
  simp only [aG, coe_operation_fst, val_zeroG, mul_zero, add_zero]

@[simp] private theorem coe_bG (x : G) : (bG x).val = b * x.val := by
  simp only [bG, coe_operation_fst, val_zeroG, mul_zero, zero_add]

private def inverseBG (x : G) : G := x + imagG x
private def inverseAG (x : G) : G := x - imagG x

private theorem b_inverseBG (x : G) : b * (inverseBG x).val = x.val := by
  simp only [inverseBG, coe_add, coe_imagG]
  apply Complex.ext <;>
    norm_num [b, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

private theorem a_inverseAG (x : G) : a * (inverseAG x).val = x.val := by
  simp only [inverseAG, coe_sub, coe_imagG]
  apply Complex.ext <;>
    norm_num [a, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

/-- Global contextual periods, rather than bare signature periods, retain the
context-congruence needed for contraction closure. -/
private def contextualPeriods (σ : G → Ω) : AddSubgroup G where
  carrier := {d | ∀ z : G, ResponseEq operationG σ z (z + d)}
  zero_mem' := by
    intro z C
    simp only [add_zero]
  add_mem' := by
    intro d e hd he z C
    simpa only [add_assoc] using (hd z C).trans (he (z + d) C)
  neg_mem' := by
    intro d hd z C
    simpa only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero] using
      (hd (z - d) C).symm

/-- Translation invariance is proved from explicit references in G. -/
private theorem a_period_of_responseEq (σ : G → Ω) {x y : G}
    (h : ResponseEq operationG σ x y) :
    aG (y - x) ∈ contextualPeriods σ := by
  intro z
  let r : G := inverseBG (z - aG x)
  have hfirst : (operationG (x, r)).1 = z := by
    apply Subtype.ext
    rw [coe_operation_fst]
    change a * x.val + b * (inverseBG (z - aG x)).val = z.val
    rw [b_inverseBG, coe_sub, coe_aG]
    ring
  have hsecond : (operationG (y, r)).1 = z + aG (y - x) := by
    apply Subtype.ext
    rw [coe_operation_fst]
    change a * y.val + b * (inverseBG (z - aG x)).val = (z + aG (y - x)).val
    rw [b_inverseBG]
    simp only [coe_sub, coe_aG, coe_add]
    ring
  have hh := left_congr h .first r
  change ResponseEq operationG σ (operationG (x, r)).1 (operationG (y, r)).1 at hh
  rwa [hfirst, hsecond] at hh

private theorem b_period_of_responseEq (σ : G → Ω) {x y : G}
    (h : ResponseEq operationG σ x y) :
    bG (y - x) ∈ contextualPeriods σ := by
  intro z
  let r : G := inverseAG (z - bG x)
  have hfirst : (operationG (x, r)).2 = z := by
    apply Subtype.ext
    rw [coe_operation_snd]
    change b * x.val + a * (inverseAG (z - bG x)).val = z.val
    rw [a_inverseAG, coe_sub, coe_bG]
    ring
  have hsecond : (operationG (y, r)).2 = z + bG (y - x) := by
    apply Subtype.ext
    rw [coe_operation_snd]
    change b * y.val + a * (inverseAG (z - bG x)).val = (z + bG (y - x)).val
    rw [a_inverseAG]
    simp only [coe_sub, coe_bG, coe_add]
    ring
  have hh := left_congr h .second r
  change ResponseEq operationG σ (operationG (x, r)).2 (operationG (y, r)).2 at hh
  rwa [hfirst, hsecond] at hh

private theorem contextualPeriods_a (σ : G → Ω) {d : G}
    (hd : d ∈ contextualPeriods σ) : aG d ∈ contextualPeriods σ := by
  have hh := a_period_of_responseEq σ (hd 0)
  simpa only [zero_add, sub_zero] using hh

private theorem contextualPeriods_b (σ : G → Ω) {d : G}
    (hd : d ∈ contextualPeriods σ) : bG d ∈ contextualPeriods σ := by
  have hh := b_period_of_responseEq σ (hd 0)
  simpa only [zero_add, sub_zero] using hh

private theorem contextualPeriods_imag (σ : G → Ω) {d : G}
    (hd : d ∈ contextualPeriods σ) : imagG d ∈ contextualPeriods σ := by
  have haa := contextualPeriods_a σ (contextualPeriods_a σ hd)
  have heq : aG (aG d) + aG (aG d) = imagG d := by
    apply Subtype.ext
    simp only [coe_add, coe_aG, coe_imagG]
    apply Complex.ext <;>
      norm_num [a, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring
  rw [← heq]
  exact (contextualPeriods σ).add_mem haa haa

private theorem contextualPeriods_half (σ : G → Ω) {d : G}
    (hd : d ∈ contextualPeriods σ) : halfG d ∈ contextualPeriods σ := by
  have hab := contextualPeriods_b σ (contextualPeriods_a σ hd)
  have heq : bG (aG d) = halfG d := by
    apply Subtype.ext
    simp only [coe_bG, coe_aG, coe_halfG]
    apply Complex.ext <;>
      norm_num [a, b, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring
  rwa [← heq]

private def halveIter : ℕ → G → G
  | 0, d => d
  | k + 1, d => halfG (halveIter k d)

@[simp] private theorem coe_halveIter (k : ℕ) (d : G) :
    (halveIter k d).val = d.val / (2 : ℂ)^k := by
  induction k with
  | zero => simp [halveIter]
  | succ k ih => rw [halveIter, coe_halfG, ih, pow_succ, div_div]

private theorem contextualPeriods_halveIter (σ : G → Ω) (k : ℕ) {d : G}
    (hd : d ∈ contextualPeriods σ) : halveIter k d ∈ contextualPeriods σ := by
  induction k with
  | zero => exact hd
  | succ k ih => exact contextualPeriods_half σ ih

/-- Multiplication here is certified through finite integer/phase/halving
macros; no field closure or inverse of an arbitrary generated scalar is used. -/
private theorem contextualPeriods_gaussian_dyadic_mul (σ : G → Ω) {d : G}
    (hd : d ∈ contextualPeriods σ) (c : ℂ) (hc : GaussianDyadic c) :
    ∃ e : G, e ∈ contextualPeriods σ ∧ e.val = c * d.val := by
  obtain ⟨k, g, rfl⟩ := hc
  let numerator : G := g.re • d + imagG (g.im • d)
  have hnum : numerator ∈ contextualPeriods σ :=
    (contextualPeriods σ).add_mem ((contextualPeriods σ).zsmul_mem hd g.re)
      (contextualPeriods_imag σ ((contextualPeriods σ).zsmul_mem hd g.im))
  have hval : numerator.val = (g : ℂ) * d.val := by
    simp only [numerator, coe_add, coe_zsmul, coe_imagG, GaussianInt.toComplex_def]
    ring
  refine ⟨halveIter k numerator, contextualPeriods_halveIter σ k hnum, ?_⟩
  rw [coe_halveIter, hval]
  ring

/-- A distinct equivalent pair forces every inhabited fiber to be dense.
This conclusion uses no topology on Ω and no continuity of σ. -/
theorem dense_fiber_of_distinct_responseEq (σ : G → Ω) {x y : G}
    (hxy : x ≠ y) (h : ResponseEq operationG σ x y) (v : G) :
    Dense {w : G | σ w = σ v} := by
  let d : G := aG (y - x)
  have hd : d ∈ contextualPeriods σ := a_period_of_responseEq σ h
  have hd0 : d.val ≠ 0 := by
    change (aG (y - x)).val ≠ 0
    rw [coe_aG, coe_sub]
    apply mul_ne_zero ResponseSignatureControls.native_a_ne_zero
    intro he
    apply hxy
    apply Subtype.ext
    exact (sub_eq_zero.mp he).symm
  have hdn : 0 < ‖d.val‖ := norm_pos_iff.mpr hd0
  intro z
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let c : ℂ := (z.val - v.val) / d.val
  obtain ⟨p, hp⟩ := NativeGaussianDyadicDensity.exists_program_approx c
    (ε / ‖d.val‖) (div_pos hε hdn)
  obtain ⟨e, he, heval⟩ := contextualPeriods_gaussian_dyadic_mul σ hd (value p)
    (value_gaussian_dyadic p)
  let w : G := v + e
  have hw : σ w = σ v := (ResponseContextQuotient.signature_eq (he v)).symm
  have hc : c * d.val = z.val - v.val := div_mul_cancel₀ _ hd0
  have herr : w.val - z.val = (value p - c) * d.val := by
    change (v + e).val - z.val = (value p - c) * d.val
    rw [coe_add, heval]
    calc
      v.val + value p * d.val - z.val =
          (value p - c) * d.val + (c * d.val - (z.val - v.val)) := by ring
      _ = (value p - c) * d.val := by rw [hc]; ring
  refine ⟨w, hw, ?_⟩
  change dist z.val w.val < ε
  rw [dist_eq_norm, norm_sub_rev, herr, norm_mul]
  calc
    ‖value p - c‖ * ‖d.val‖ < (ε / ‖d.val‖) * ‖d.val‖ :=
      mul_lt_mul_of_pos_right hp hdn
    _ = ε := div_mul_cancel₀ _ hdn.ne'

/-- Nonempty relative openness and constancy are supplied only on this patch.
There is no global continuity premise and Ω has no topology. -/
def HasOpenConstantPatch (σ : G → Ω) : Prop :=
  ∃ U : Set G, IsOpen U ∧ U.Nonempty ∧ ∃ c : Ω, ∀ z ∈ U, σ z = c

theorem constant_of_patch_and_distinct_responseEq (σ : G → Ω)
    (hpatch : HasOpenConstantPatch σ) {x y : G} (hxy : x ≠ y)
    (h : ResponseEq operationG σ x y) : ∀ u v : G, σ u = σ v := by
  obtain ⟨U, hU, hUne, c, hc⟩ := hpatch
  have hall : ∀ v : G, σ v = c := by
    intro v
    obtain ⟨w, hw, hwU⟩ :=
      (dense_fiber_of_distinct_responseEq σ hxy h v).exists_mem_open hU hUne
    exact hw.symm.trans (hc w hwU)
  intro u v
  exact (hall u).trans (hall v).symm

theorem separates_iff_nonconstant_of_open_constant_patch (σ : G → Ω)
    (hpatch : HasOpenConstantPatch σ) :
    Separates σ ↔ ∃ x y : G, σ x ≠ σ y := by
  classical
  constructor
  · intro hsep
    by_contra hn
    push Not at hn
    have heq : unitG = zeroG := hsep unitG zeroG (fun C => hn _ _)
    have hv := congrArg Subtype.val heq
    norm_num at hv
  · rintro ⟨u, v, huv⟩ x y h
    by_contra hxy
    exact huv (constant_of_patch_and_distinct_responseEq σ hpatch hxy h u v)

theorem law_nonempty_iff_nonconstant_of_open_constant_patch (σ : G → Ω)
    (hpatch : HasOpenConstantPatch σ) :
    Nonempty (ResponseNativeProbabilitySelection.Law (signatureData σ) unitG) ↔
      ∃ x y : G, σ x ≠ σ y :=
  (law_nonempty_iff_separates σ).trans
    (separates_iff_nonconstant_of_open_constant_patch σ hpatch)

/-- Every supplied scalar family's complete probability field transports when
the patch signature is nonconstant. This supplies no probability provenance. -/
def lawOfScalarOfPatchNonconstant (σ : G → Ω) (hpatch : HasOpenConstantPatch σ)
    (hnonconstant : ∃ x y : G, σ x ≠ σ y) (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (signatureData σ) unitG :=
  lawOfScalar σ ((separates_iff_nonconstant_of_open_constant_patch σ hpatch).mpr
    hnonconstant) L

theorem lawOfScalarOfPatchNonconstant_probability (σ : G → Ω)
    (hpatch : HasOpenConstantPatch σ) (hnonconstant : ∃ x y : G, σ x ≠ σ y)
    (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob G Ω (signatureData σ) unitG
      (lawOfScalarOfPatchNonconstant σ hpatch hnonconstant L) =
        @NativeVacuumProbabilityFamily.Law.prob L := rfl

end
end IDT.QMClosure.NativeAllocatedStableObservation
