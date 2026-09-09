import Proofs.QMClosure.PairHistoryMeasureProbe

namespace IDT.QMClosure.NativeAmplitudeObservability

/-!
# Native amplitude laws and a restricted observable quotient

`GaussianHistoryAmplitude` is reused only as a record of two integer
coordinates. The multiplication and weight below are supplied independently;
the record's name does not select Gaussian multiplication or quantum physics.

The classification quantifies over arbitrary integer parameters and coordinates.
The quotient theorem quantifies over exactly the finite expression grammar in
this file: variables, coordinate constants, addition, and multiplication. It
does not quantify over all physical preparations, measurements, or operations.
These weights are not normalized probabilities, and these results neither
select a physical carrier nor establish quantum mechanics.
-/

abbrev CoordinatePlane := GaussianHistoryAmplitude

def planeAdd (left right : CoordinatePlane) : CoordinatePlane :=
  ⟨left.re + right.re, left.im + right.im⟩

def planeMul (k : ℤ) (left right : CoordinatePlane) : CoordinatePlane :=
  ⟨left.re * right.re + k * left.im * right.im,
    left.re * right.im + left.im * right.re⟩

def planeWeight (eta : ℤ) (amplitude : CoordinatePlane) : ℤ :=
  amplitude.re ^ 2 + eta * amplitude.im ^ 2

theorem weight_nonnegative_iff (eta : ℤ) :
    (∀ amplitude, 0 ≤ planeWeight eta amplitude) ↔ 0 ≤ eta := by
  constructor
  · intro h
    have unitAxis := h ⟨0, 1⟩
    simpa only [planeWeight, zero_pow (by decide : 2 ≠ 0), one_pow,
      mul_one, zero_add] using unitAxis
  · intro h amplitude
    exact add_nonneg (sq_nonneg amplitude.re)
      (mul_nonneg h (sq_nonneg amplitude.im))

/-- The complete polynomial defect, before any parameter is selected. -/
theorem multiplication_weight_defect (k eta : ℤ)
    (left right : CoordinatePlane) :
    planeWeight eta (planeMul k left right) -
        planeWeight eta left * planeWeight eta right =
      (k + eta) * (2 * left.re * left.im * right.re * right.im +
        (k - eta) * left.im ^ 2 * right.im ^ 2) := by
  simp only [planeWeight, planeMul]
  ring

theorem weight_multiplicative_iff (k eta : ℤ) :
    (∀ left right,
      planeWeight eta (planeMul k left right) =
        planeWeight eta left * planeWeight eta right) ↔ k = -eta := by
  constructor
  · intro h
    have unitAxis := h ⟨0, 1⟩ ⟨0, 1⟩
    have mixedAxis := h ⟨1, 1⟩ ⟨1, 1⟩
    norm_num [planeWeight, planeMul] at unitAxis mixedAxis
    nlinarith [unitAxis, mixedAxis]
  · intro h left right
    subst k
    simp only [planeWeight, planeMul]
    ring

theorem nonnegative_multiplicative_classification (k eta : ℤ) :
    ((∀ amplitude, 0 ≤ planeWeight eta amplitude) ∧
      (∀ left right,
        planeWeight eta (planeMul k left right) =
          planeWeight eta left * planeWeight eta right)) ↔
      0 ≤ eta ∧ k = -eta := by
  rw [weight_nonnegative_iff, weight_multiplicative_iff]

/-- Supplied operation grammar, not an inventory of all physical operations. -/
inductive AmplitudeExpr where
  | input (index : Nat)
  | constant (value : CoordinatePlane)
  | add (left right : AmplitudeExpr)
  | mul (left right : AmplitudeExpr)
deriving DecidableEq, Repr

def evalPlane (k : ℤ) (environment : Nat → CoordinatePlane) :
    AmplitudeExpr → CoordinatePlane
  | .input index => environment index
  | .constant value => value
  | .add left right =>
      planeAdd (evalPlane k environment left) (evalPlane k environment right)
  | .mul left right =>
      planeMul k (evalPlane k environment left) (evalPlane k environment right)

/-- The comparison model projects constants as well as environment inputs. -/
def evalScalar (environment : Nat → ℤ) : AmplitudeExpr → ℤ
  | .input index => environment index
  | .constant value => value.re
  | .add left right => evalScalar environment left + evalScalar environment right
  | .mul left right => evalScalar environment left * evalScalar environment right

theorem dual_evaluation_projects (environment : Nat → CoordinatePlane)
    (expression : AmplitudeExpr) :
    (evalPlane 0 environment expression).re =
      evalScalar (fun index => (environment index).re) expression := by
  induction expression with
  | input index => rfl
  | constant value => rfl
  | add left right ihLeft ihRight =>
      simp only [evalPlane, evalScalar, planeAdd, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp only [evalPlane, evalScalar, planeMul, zero_mul, add_zero, ihLeft, ihRight]

theorem dual_weight_projects (environment : Nat → CoordinatePlane)
    (expression : AmplitudeExpr) :
    planeWeight 0 (evalPlane 0 environment expression) =
      pairHistoryQuadraticWeight
        (evalScalar (fun index => (environment index).re) expression) := by
  simp only [planeWeight, pairHistoryQuadraticWeight, zero_mul, add_zero,
    dual_evaluation_projects]

/-- Hidden second coordinates remain unobservable throughout this grammar. -/
theorem same_real_environments_have_same_dual_weights
    (left right : Nat → CoordinatePlane)
    (sameReal : ∀ index, (left index).re = (right index).re)
    (expression : AmplitudeExpr) :
    planeWeight 0 (evalPlane 0 left expression) =
      planeWeight 0 (evalPlane 0 right expression) := by
  rw [dual_weight_projects, dual_weight_projects]
  have projectedEnvironments :
      (fun index => (left index).re) = (fun index => (right index).re) := by
    funext index
    exact sameReal index
  rw [projectedEnvironments]

def secondAxis : CoordinatePlane := ⟨0, 1⟩

/-- A null input alone does not justify taking a quotient for another product. -/
theorem null_axis_can_become_visible_under_multiplication :
    planeWeight 0 secondAxis = 0 ∧
      planeWeight 0 (planeMul (-1) secondAxis secondAxis) = 1 := by
  norm_num [secondAxis, planeWeight, planeMul]

/-- The same projection is not weight-preserving for the Gaussian norm. -/
theorem gaussian_weight_is_not_scalar_projection :
    planeWeight 1 secondAxis = 1 ∧
      pairHistoryQuadraticWeight secondAxis.re = 0 := by
  norm_num [secondAxis, planeWeight, pairHistoryQuadraticWeight]

end IDT.QMClosure.NativeAmplitudeObservability
