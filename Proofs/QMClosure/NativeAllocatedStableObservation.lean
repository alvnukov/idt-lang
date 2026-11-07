import Proofs.QMClosure.NativeAllocatedSignatureLaw
import Proofs.QMClosure.NativeGaussianDyadicDensity
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Logic.Function.Iterate

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

/-!
## Supplied exact settling under one fixed generated reference

This additional contract is algebraic and topology-free: each generated input's
signature is eventually exactly the reference's signature along repeated
first-output mixing with that same reference. The settling threshold may depend
on the input. This is an infinite supplied contract, without a finite-validation,
physical relaxation, detector precision/noise, or probability-provenance claim.
Each repeated known-reference occurrence requires a fresh separately charged
preparation. No uniform source budget is asserted.
-/

/-- Repeat the existing first output with one fixed generated reference. -/
def referenceStep (z : G) (x : G) : G := (operationG (x, z)).1


/-- Exact eventual signature agreement, supplied separately for every input. -/
def ReferenceSettles (σ : G → Ω) : Prop :=
  ∃ z : G, ∀ x : G, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    σ ((referenceStep z)^[n] x) = σ z


private theorem two_pow_four_mul (n : ℕ) :
    (2 : ℂ)^(4 * n) = (16 : ℂ)^n := by
  rw [pow_mul]
  norm_num


/-- A nonzero contextual period has a positive ordinary integer multiple-period.
All scalar multipliers are certified Gaussian dyadics. -/
private theorem exists_positive_integer_period (σ : G → Ω) {d : G}
    (hd : d ∈ contextualPeriods σ) (hd0 : d.val ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ e : G, e ∈ contextualPeriods σ ∧ e.val = (N : ℂ) := by
  obtain ⟨k, g, hgval⟩ := (reachable_iff_gaussian_dyadic d.val).mp d.property
  have hg : g ≠ 0 := by
    intro hz
    apply hd0
    simpa only [hz, GaussianInt.toComplex_zero, zero_div] using hgval
  let N : ℕ := g.norm.natAbs
  have hNcast : (N : ℤ) = g.norm := GaussianInt.abs_natCast_norm g
  have hN : 0 < N := by
    have hp : (0 : ℤ) < (N : ℤ) := by
      rw [hNcast]
      exact GaussianInt.norm_pos.mpr hg
    exact_mod_cast hp
  let c : GaussianInt := star g * (2 : GaussianInt)^k
  have hc : GaussianDyadic (c : ℂ) := ⟨0, c, by simp⟩
  obtain ⟨e, he, heval⟩ := contextualPeriods_gaussian_dyadic_mul σ hd (c : ℂ) hc
  have hpow : (((2 : GaussianInt)^k : GaussianInt) : ℂ) = (2 : ℂ)^k := by
    simpa only [map_ofNat] using (map_pow GaussianInt.toComplex (2 : GaussianInt) k)
  have hcval : (c : ℂ) = ((star g : GaussianInt) : ℂ) * (2 : ℂ)^k := by
    rw [show c = star g * (2 : GaussianInt)^k from rfl, GaussianInt.toComplex_mul, hpow]
  have hnorm : ((star g : GaussianInt) : ℂ) * (g : ℂ) = (g.norm : ℂ) := by
    rw [GaussianInt.toComplex_star, GaussianInt.intCast_complex_norm]
    exact (Complex.normSq_eq_conj_mul_self (z := (g : ℂ))).symm
  refine ⟨N, hN, e, he, ?_⟩
  calc
    e.val = (((star g : GaussianInt) : ℂ) * (2 : ℂ)^k) *
        ((g : ℂ) / (2 : ℂ)^k) := by rw [heval, hcval, hgval]
    _ = ((star g : GaussianInt) : ℂ) * (g : ℂ) := by
      field_simp [pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0)]
    _ = (g.norm : ℂ) := hnorm
    _ = (N : ℂ) := (GaussianInt.natCast_natAbs_norm g).symm


/-- Finiteness is used only for the ordinary ring ZMod N. No finite contextual
quotient, odd-part argument, or finite response alphabet is assumed. -/
private theorem exists_power_difference_period (σ : G → Ω) {d : G}
    (hd : d ∈ contextualPeriods σ) (hd0 : d.val ≠ 0) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ e : G, e ∈ contextualPeriods σ ∧
      e.val = (16 : ℂ)^ℓ - 1 := by
  obtain ⟨N, hN, eN, heN, heNval⟩ := exists_positive_integer_period σ hd hd0
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨u, v, huv, hpoweq⟩ :
      ∃ u v : ℕ, u < v ∧ (16 : ZMod N)^u = (16 : ZMod N)^v :=
    Set.Finite.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => (16 : ZMod N)^n)
      (fun _ => Set.mem_univ _) Set.finite_univ
  have hcast : (((16 : ℤ)^u : ℤ) : ZMod N) =
      (((16 : ℤ)^v : ℤ) : ZMod N) := by
    simpa only [Int.cast_pow, Int.cast_ofNat] using hpoweq
  have hdiv : (N : ℤ) ∣ (16 : ℤ)^v - (16 : ℤ)^u :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp hcast
  obtain ⟨m, hm⟩ := hdiv
  let e : G := m • eN
  have he : e ∈ contextualPeriods σ := (contextualPeriods σ).zsmul_mem heN m
  have heval : e.val = (16 : ℂ)^v - (16 : ℂ)^u := by
    change (m • eN).val = _
    rw [coe_zsmul, heNval, mul_comm]
    exact_mod_cast hm.symm
  let ℓ : ℕ := v - u
  have hℓ : 0 < ℓ := Nat.sub_pos_of_lt huv
  have hv : v = u + ℓ := by dsimp [ℓ]; omega
  refine ⟨ℓ, hℓ, halveIter (4 * u) e, contextualPeriods_halveIter σ _ he, ?_⟩
  rw [coe_halveIter, heval, two_pow_four_mul, hv, pow_add]
  field_simp [pow_ne_zero u (by norm_num : (16 : ℂ) ≠ 0)]


private theorem native_a_add_b : a + b = 1 := by
  unfold a b
  ring


private theorem native_a_pow_eight : a^8 = (1 : ℂ) / 16 := by
  apply Complex.ext <;>
    norm_num [a, pow_succ, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]


/-- Literal scalar semantics of the actual fixed-reference one-hole iteration. -/
theorem referenceStep_iterate_coe (z x : G) (n : ℕ) :
    ((referenceStep z)^[n] x).val = z.val + a^n * (x.val - z.val) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero_apply, pow_zero, one_mul]
    ring
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (operationG (((referenceStep z)^[n] x), z)).1.val =
      z.val + a^(n + 1) * (x.val - z.val)
    rw [coe_operation_fst, ih, pow_succ]
    calc
      a * (z.val + a^n * (x.val - z.val)) + b * z.val =
          (a + b) * z.val + (a^n * a) * (x.val - z.val) := by ring
      _ = z.val + (a^n * a) * (x.val - z.val) := by rw [native_a_add_b, one_mul]


private theorem referenceStep_return_difference (z x : G) (ℓ : ℕ) :
    ((referenceStep z)^[8 * ℓ] x).val - x.val =
      (-(x.val - z.val) / (2 : ℂ)^(4 * ℓ)) * ((16 : ℂ)^ℓ - 1) := by
  have ha : a^(8 * ℓ) = 1 / (16 : ℂ)^ℓ := by
    rw [pow_mul, native_a_pow_eight, div_pow, one_pow]
  rw [referenceStep_iterate_coe, ha, two_pow_four_mul]
  field_simp [pow_ne_zero ℓ (by norm_num : (16 : ℂ) ≠ 0)]
  ring


private theorem responseEq_reference_return_of_period (σ : G → Ω)
    (ℓ : ℕ) {d : G} (hd : d ∈ contextualPeriods σ)
    (hdval : d.val = (16 : ℂ)^ℓ - 1) (z x : G) :
    ResponseEq operationG σ x ((referenceStep z)^[8 * ℓ] x) := by
  let p : ScalarProgram := negate (halfPower (4 * ℓ) (chosenProgram (x - z)))
  have hpval : value p = -(x.val - z.val) / (2 : ℂ)^(4 * ℓ) := by
    dsimp [p]
    rw [value_negate, value_halfPower, value_chosenProgram, coe_sub]
    ring
  have hc : GaussianDyadic (-(x.val - z.val) / (2 : ℂ)^(4 * ℓ)) := by
    rw [← hpval]
    exact value_gaussian_dyadic p
  obtain ⟨e, he, heval⟩ := contextualPeriods_gaussian_dyadic_mul σ hd
    (-(x.val - z.val) / (2 : ℂ)^(4 * ℓ)) hc
  have hout : x + e = (referenceStep z)^[8 * ℓ] x := by
    apply Subtype.ext
    rw [coe_add, heval, hdval, ← referenceStep_return_difference z x ℓ]
    ring
  have hh := he x
  rwa [hout] at hh


/-- Any distinct equivalent pair forces a common positive contextual return
length for all generated inputs and all generated fixed references. -/
theorem common_contextual_return_of_distinct_responseEq (σ : G → Ω) {x y : G}
    (hxy : x ≠ y) (h : ResponseEq operationG σ x y) :
    ∃ L : ℕ, 0 < L ∧ ∀ z x : G,
      ResponseEq operationG σ x ((referenceStep z)^[L] x) := by
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
  obtain ⟨ℓ, hℓ, e, he, heval⟩ := exists_power_difference_period σ hd hd0
  refine ⟨8 * ℓ, Nat.mul_pos (by decide) hℓ, ?_⟩
  intro z x
  exact responseEq_reference_return_of_period σ ℓ he heval z x


private theorem responseEq_reference_iterate_multiple (σ : G → Ω) (L : ℕ)
    (hret : ∀ z x : G, ResponseEq operationG σ x ((referenceStep z)^[L] x))
    (z x : G) (m : ℕ) :
    ResponseEq operationG σ x ((referenceStep z)^[L * m] x) := by
  induction m with
  | zero =>
    intro C
    rfl
  | succ m ih =>
    rw [Nat.mul_succ, Nat.add_comm, Function.iterate_add_apply]
    intro C
    exact (ih C).trans (hret z ((referenceStep z)^[L * m] x) C)


/-- Exact settling excludes nonconstant signatures with a collapsed response
pair. No topology or continuity premise occurs in this argument. -/
theorem constant_of_settling_and_distinct_responseEq (σ : G → Ω)
    (hsettles : ReferenceSettles σ) {x y : G} (hxy : x ≠ y)
    (h : ResponseEq operationG σ x y) : ∀ u v : G, σ u = σ v := by
  obtain ⟨z, hz⟩ := hsettles
  obtain ⟨L, hL, hret⟩ := common_contextual_return_of_distinct_responseEq σ hxy h
  have hall : ∀ x : G, σ x = σ z := by
    intro x
    obtain ⟨N, hN⟩ := hz x
    have hlarge : N ≤ L * (N + 1) :=
      (Nat.le_succ N).trans (by
        simpa only [Nat.succ_eq_add_one, Nat.zero_add, one_mul] using
          Nat.mul_le_mul_right (N + 1) (Nat.succ_le_of_lt hL))
    exact (ResponseContextQuotient.signature_eq
      (responseEq_reference_iterate_multiple σ L hret z x (N + 1))).trans
        (hN (L * (N + 1)) hlarge)
  intro u v
  exact (hall u).trans (hall v).symm


theorem separates_iff_nonconstant_of_reference_settles (σ : G → Ω)
    (hsettles : ReferenceSettles σ) :
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
    exact huv (constant_of_settling_and_distinct_responseEq σ hsettles hxy h u v)


theorem law_nonempty_iff_nonconstant_of_reference_settles (σ : G → Ω)
    (hsettles : ReferenceSettles σ) :
    Nonempty (ResponseNativeProbabilitySelection.Law (signatureData σ) unitG) ↔
      ∃ x y : G, σ x ≠ σ y :=
  (law_nonempty_iff_separates σ).trans
    (separates_iff_nonconstant_of_reference_settles σ hsettles)


/-- Preserve the entire probability field of any supplied scalar family and
transport the unchanged six-field contract. Settling and nonconstancy supply
separation, not probability provenance. -/
def lawOfScalarOfReferenceSettles (σ : G → Ω) (hsettles : ReferenceSettles σ)
    (hnonconstant : ∃ x y : G, σ x ≠ σ y) (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (signatureData σ) unitG :=
  lawOfScalar σ ((separates_iff_nonconstant_of_reference_settles σ hsettles).mpr
    hnonconstant) L


theorem lawOfScalarOfReferenceSettles_probability (σ : G → Ω)
    (hsettles : ReferenceSettles σ) (hnonconstant : ∃ x y : G, σ x ≠ σ y)
    (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob G Ω (signatureData σ) unitG
      (lawOfScalarOfReferenceSettles σ hsettles hnonconstant L) =
        @NativeVacuumProbabilityFamily.Law.prob L := rfl

end
end IDT.QMClosure.NativeAllocatedStableObservation
