import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

namespace IDT.QMClosure.ReferenceNormalizationCountermodels

noncomputable section

/-!
# Exact negative controls for reference normalization

These controls distinguish a shared flat response from hierarchical readout,
complete outcomes from postselection, and a globally fixed linear generator
from a nonlinear vector field with a nonzero linear part. They supply no IDT
primitive bridge, physical causality theorem, global flow, or Born/QM proof.
-/

structure Readout where
  reference : ℝ
  left : ℝ
  right : ℝ

def hierarchical (p u v : ℝ) : Readout :=
  ⟨p, (1 - p) * u / (u + v), (1 - p) * v / (u + v)⟩

theorem hierarchical_nonnegative (p u v : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htotal : 0 < u + v) :
    0 ≤ (hierarchical p u v).reference ∧
      0 ≤ (hierarchical p u v).left ∧ 0 ≤ (hierarchical p u v).right := by
  dsimp [hierarchical]
  exact ⟨hp, div_nonneg (mul_nonneg (sub_nonneg.mpr hp') hu) htotal.le,
    div_nonneg (mul_nonneg (sub_nonneg.mpr hp') hv) htotal.le⟩

theorem hierarchical_normalized (p u v : ℝ) (htotal : 0 < u + v) :
    (hierarchical p u v).reference + (hierarchical p u v).left +
      (hierarchical p u v).right = 1 := by
  dsimp [hierarchical]
  field_simp [ne_of_gt htotal]
  ring

/-- Coarse reference preservation alone places no constraint on raw subblock totals. -/
theorem hierarchical_reference_unchanged (p u v u' v' : ℝ) :
    (hierarchical p u v).reference = (hierarchical p u' v').reference := rfl

def quartic (t : ℝ) : ℝ := t ^ 4

def rawSum (f : ℝ → ℝ) (x y : ℝ) : ℝ := f x + f y

def flatReference (R : ℝ) (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  R / (R + rawSum f x y)

def rationalRotation (x y : ℝ) : ℝ × ℝ :=
  ((3 / 5 : ℝ) * x - (4 / 5 : ℝ) * y,
    (4 / 5 : ℝ) * x + (3 / 5 : ℝ) * y)

def rationalRotationInverse (x y : ℝ) : ℝ × ℝ :=
  ((3 / 5 : ℝ) * x + (4 / 5 : ℝ) * y,
    -(4 / 5 : ℝ) * x + (3 / 5 : ℝ) * y)

theorem rationalRotation_inverse (x y : ℝ) :
    rationalRotationInverse (rationalRotation x y).1 (rationalRotation x y).2 =
      (x, y) := by
  ext <;> dsimp [rationalRotationInverse, rationalRotation] <;> ring

theorem rationalRotation_preserves_quadratic (x y : ℝ) :
    (rationalRotation x y).1 ^ 2 + (rationalRotation x y).2 ^ 2 = x ^ 2 + y ^ 2 := by
  dsimp [rationalRotation]
  ring

/-- The same quartic response fails flat reference preservation under this
supplied rotation, while a hierarchical reference remains fixed. -/
theorem quartic_rotation_exact_control :
    rationalRotation 1 0 = ((3 / 5 : ℝ), (4 / 5 : ℝ)) ∧
    rawSum quartic 1 0 = 1 ∧
    rawSum quartic (3 / 5) (4 / 5) = 337 / 625 ∧
    flatReference 1 quartic 1 0 = 1 / 2 ∧
    flatReference 1 quartic (3 / 5) (4 / 5) = 625 / 962 ∧
    flatReference 1 quartic 1 0 ≠ flatReference 1 quartic (3 / 5) (4 / 5) ∧
    (hierarchical (1 / 2) (quartic (3 / 5)) (quartic (4 / 5))).reference = 1 / 2 ∧
    (hierarchical (1 / 2) (quartic (3 / 5)) (quartic (4 / 5))).left = 81 / 674 ∧
    (hierarchical (1 / 2) (quartic (3 / 5)) (quartic (4 / 5))).right = 128 / 337 := by
  norm_num [rationalRotation, rawSum, quartic, flatReference, hierarchical]

/-- A concrete counterexample to inferring raw conservation from coarse-event
preservation without imposing the shared flat normalization contract. -/
theorem coarse_reference_does_not_force_raw_conservation :
    (hierarchical (1 / 2) (quartic 1) (quartic 0)).reference =
      (hierarchical (1 / 2) (quartic (3 / 5)) (quartic (4 / 5))).reference ∧
    rawSum quartic 1 0 ≠ rawSum quartic (3 / 5) (4 / 5) := by
  norm_num [hierarchical, rawSum, quartic]

/-- The third outcome is filter failure/loss; it belongs to the complete readout. -/
def afterFilter : Readout := ⟨1 / 2, 1 / 4, 1 / 4⟩

def conditionOnReferenceOrSuccess (p : Readout) : ℝ :=
  p.reference / (p.reference + p.left)

/-- Conditional selection changes the displayed fraction despite an unchanged
unconditional reference. This arithmetic is not a causal-violation theorem. -/
theorem complete_filter_and_postselection_control :
    afterFilter.reference + afterFilter.left + afterFilter.right = 1 ∧
    afterFilter.reference = 1 / 2 ∧
    0 < afterFilter.right ∧
    conditionOnReferenceOrSuccess afterFilter = 2 / 3 ∧
    conditionOnReferenceOrSuccess afterFilter ≠ afterFilter.reference := by
  norm_num [afterFilter, conditionOnReferenceOrSuccess]

def nonlinearResponse (t : ℝ) : ℝ := t ^ 2 + t ^ 4

theorem nonlinearResponse_nonnegative (t : ℝ) : 0 ≤ nonlinearResponse t := by
  dsimp [nonlinearResponse]
  positivity

@[simp] theorem nonlinearResponse_zero : nonlinearResponse 0 = 0 := by
  norm_num [nonlinearResponse]

theorem nonlinearResponse_one_positive : 0 < nonlinearResponse 1 := by
  norm_num [nonlinearResponse]

theorem nonlinearResponse_hasDerivAt (t : ℝ) :
    HasDerivAt nonlinearResponse (2 * t + 4 * t ^ 3) t := by
  convert ((hasDerivAt_id t).pow 2).add ((hasDerivAt_id t).pow 4) using 1
  simp only [id_eq]
  ring

theorem nonlinearResponse_deriv (t : ℝ) :
    deriv nonlinearResponse t = 2 * t + 4 * t ^ 3 :=
  (nonlinearResponse_hasDerivAt t).deriv

def thirdOrderDifference (f : ℝ → ℝ) (a b c : ℝ) : ℝ :=
  f (a + b + c) - f (a + b) - f (a + c) - f (b + c) +
    f a + f b + f c - f 0

theorem nonlinearResponse_I3_unit :
    thirdOrderDifference nonlinearResponse 1 1 1 = 36 := by
  norm_num [thirdOrderDifference, nonlinearResponse]

def nonlinearExchange (x y : ℝ) : ℝ × ℝ :=
  (2 * y + 4 * y ^ 3, -2 * x - 4 * x ^ 3)

/-- Exact infinitesimal balance for the actual derivative of the response.
No existence, completeness, or reversibility of a flow is asserted here. -/
theorem nonlinearExchange_response_balance (x y : ℝ) :
    deriv nonlinearResponse x * (nonlinearExchange x y).1 +
      deriv nonlinearResponse y * (nonlinearExchange x y).2 = 0 := by
  rw [nonlinearResponse_deriv, nonlinearResponse_deriv]
  dsimp [nonlinearExchange]
  ring

theorem nonlinearExchange_decomposition (x y : ℝ) :
    nonlinearExchange x y =
      (2 : ℝ) • (y, -x) + (4 : ℝ) • (y ^ 3, -(x ^ 3)) := by
  ext <;> dsimp [nonlinearExchange]
  ring

def linearPart (x y : ℝ) : ℝ × ℝ := (2 * y, -2 * x)

/-- Along every ray through the vacuum, the actual first derivative is the
displayed nonzero linear exchange. This is a local vector-field statement,
not a construction of a global dynamical flow. -/
theorem nonlinearExchange_hasDerivAt_vacuum_ray (x y : ℝ) :
    HasDerivAt (fun t : ℝ => nonlinearExchange (t * x) (t * y))
      (linearPart x y) 0 := by
  have hx : HasDerivAt (fun t : ℝ => t * x) x 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const x
  have hy : HasDerivAt (fun t : ℝ => t * y) y 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const y
  have hleft : HasDerivAt (fun t : ℝ => 2 * (t * y) + 4 * (t * y) ^ 3)
      (2 * y) 0 := by
    simpa using (hy.const_mul 2).add ((hy.pow 3).const_mul 4)
  have hright : HasDerivAt (fun t : ℝ => -2 * (t * x) - 4 * (t * x) ^ 3)
      (-2 * x) 0 := by
    simpa using (hx.const_mul (-2)).sub ((hx.pow 3).const_mul 4)
  simpa only [nonlinearExchange, linearPart] using hleft.prodMk hright

theorem nonlinearExchange_linear_part_nonzero : linearPart 1 0 ≠ (0, 0) := by
  norm_num [linearPart]

theorem nonlinearExchange_is_not_additive :
    nonlinearExchange (1 + 1) (0 + 0) ≠
      nonlinearExchange 1 0 + nonlinearExchange 1 0 := by
  norm_num [nonlinearExchange, Prod.mk_add_mk]

theorem nonlinearExchange_nonadditivity_values :
    nonlinearExchange 2 0 = (0, -36) ∧
      nonlinearExchange 1 0 + nonlinearExchange 1 0 = (0, -12) := by
  norm_num [nonlinearExchange, Prod.mk_add_mk]

def linearExchange (x y : ℝ) : ℝ × ℝ := (y, -x)

/-- Directional raw variation of the quartic response under the fixed supplied J. -/
def quarticRawVariation (x y : ℝ) : ℝ :=
  4 * x ^ 3 * (linearExchange x y).1 + 4 * y ^ 3 * (linearExchange x y).2

/-- The algebraic coefficient in the flat-reference chain rule. The theorem
below evaluates this expression; it does not construct a dynamical flow. -/
def flatReferenceVariationCoefficient (R S dS : ℝ) : ℝ :=
  -R / (R + S) ^ 2 * dS

theorem quartic_fixed_linear_exchange_control :
    rawSum quartic 1 2 = 17 ∧
    quarticRawVariation 1 2 = -24 ∧
    flatReference 1 quartic 1 2 = 1 / 18 ∧
    flatReferenceVariationCoefficient 1 (rawSum quartic 1 2)
      (quarticRawVariation 1 2) = 2 / 27 := by
  norm_num [rawSum, quartic, quarticRawVariation, linearExchange,
    flatReference, flatReferenceVariationCoefficient]

/-- Data-only scope ledger: these entries describe the precise distinctions
illustrated above and contain no proof-status or physical-success flags. -/
structure ControlScope where
  control : String
  distinction : String
  limitation : String

def controlScopes : List ControlScope := [
  ⟨"hierarchical_reference", "coarse-event preservation versus shared flat response",
    "no physical causality or Bell no-signalling theorem"⟩,
  ⟨"postselection", "conditional readout versus complete outcomes including loss",
    "omitted loss cannot justify unconditional reference conservation"⟩,
  ⟨"nonlinear_exchange", "fixed global coherent-merge compatibility versus a nonzero vacuum linear part",
    "vector-field balance only; no machine-checked global flow or reversibility"⟩,
  ⟨"quartic_linear_exchange", "the same supplied universal linear generator must balance the same response",
    "exact algebraic witness; negative controls retained; no Born or full-QM proof"⟩]

end

end IDT.QMClosure.ReferenceNormalizationCountermodels
