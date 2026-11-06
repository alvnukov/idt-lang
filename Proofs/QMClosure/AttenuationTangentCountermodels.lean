import Proofs.QMClosure.ReferenceNormalizationCountermodels

namespace IDT.QMClosure.AttenuationTangentCountermodels

open ReferenceNormalizationCountermodels

noncomputable section

/-!
# Negative controls for uniform attenuation and a common vacuum tangent

All balance statements use the actual analytic derivative of the response.
The ray statements use `HasDerivAt`, rather than naming a polynomial coefficient
"the derivative". These controls make no global flow or reversibility claim,
no IDT primitive bridge, and no Born or full-QM claim.
-/

/-- The mixed quadratic/quartic response has no uniform strict attenuation,
even when the gain is allowed to be an arbitrary real number. -/
theorem nonlinearResponse_no_uniform_attenuation (rho gain : ℝ)
    (hr : 0 < rho) (hr1 : rho < 1) :
    ¬ ∀ t : ℝ, nonlinearResponse (rho * t) = gain * nonlinearResponse t := by
  intro h
  have h1 := h 1
  have h2 := h 2
  norm_num [nonlinearResponse] at h1 h2
  have hs : 0 < rho ^ 2 := sq_pos_of_pos hr
  have hs1 : rho ^ 2 < 1 := by nlinarith
  have hstrict := mul_lt_mul_of_pos_left hs1 hs
  nlinarith

/-- This existing nonlinear field has a nonzero, genuinely rotating vacuum
tangent and exact response balance, but fails the attenuation assumption. -/
theorem mixed_response_control :
    (∀ x y : ℝ,
      deriv nonlinearResponse x * (nonlinearExchange x y).1 +
        deriv nonlinearResponse y * (nonlinearExchange x y).2 = 0) ∧
    (∀ x y : ℝ, HasDerivAt
      (fun t : ℝ => nonlinearExchange (t * x) (t * y)) (linearPart x y) 0) ∧
    linearPart 1 0 ≠ (0, 0) ∧
    thirdOrderDifference nonlinearResponse 1 1 1 = 36 ∧
    (∀ rho gain : ℝ, 0 < rho → rho < 1 →
      ¬ ∀ t : ℝ, nonlinearResponse (rho * t) = gain * nonlinearResponse t) := by
  exact ⟨nonlinearExchange_response_balance, nonlinearExchange_hasDerivAt_vacuum_ray,
    nonlinearExchange_linear_part_nonzero, nonlinearResponse_I3_unit,
    nonlinearResponse_no_uniform_attenuation⟩

theorem quartic_hasDerivAt (x : ℝ) : HasDerivAt quartic (4 * x ^ 3) x := by
  simpa [quartic] using (hasDerivAt_id x).pow 4

theorem quartic_deriv (x : ℝ) : deriv quartic x = 4 * x ^ 3 :=
  (quartic_hasDerivAt x).deriv

theorem quartic_nonnegative (x : ℝ) : 0 ≤ quartic x := by
  dsimp [quartic]
  positivity

theorem quartic_uniform_attenuation (rho x : ℝ) :
    quartic (rho * x) = rho ^ 4 * quartic x := by
  simp [quartic, mul_pow]

theorem quartic_strict_attenuation_witness :
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧ (0 : ℝ) < (1 / 2 : ℝ) ^ 4 ∧
    ∀ x : ℝ, quartic ((1 / 2) * x) = (1 / 2 : ℝ) ^ 4 * quartic x := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  exact quartic_uniform_attenuation (1 / 2)

theorem quartic_I3_unit : thirdOrderDifference quartic 1 1 1 = 36 := by
  norm_num [thirdOrderDifference, quartic]

def cubicExchange (x y : ℝ) : ℝ × ℝ := (y ^ 3, -(x ^ 3))

@[simp] theorem cubicExchange_zero : cubicExchange 0 0 = (0, 0) := by
  norm_num [cubicExchange]

theorem cubicExchange_response_balance (x y : ℝ) :
    deriv quartic x * (cubicExchange x y).1 +
      deriv quartic y * (cubicExchange x y).2 = 0 := by
  rw [quartic_deriv, quartic_deriv]
  dsimp [cubicExchange]
  ring

/-- A globally nonzero conserving field can have zero vacuum tangent on every
ray, so nontriviality away from the vacuum cannot replace tangent mixing. -/
theorem cubicExchange_hasDerivAt_vacuum_ray (x y : ℝ) :
    HasDerivAt (fun t : ℝ => cubicExchange (t * x) (t * y)) (0, 0) 0 := by
  have hx : HasDerivAt (fun t : ℝ => t * x) x 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const x
  have hy : HasDerivAt (fun t : ℝ => t * y) y 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const y
  simpa [cubicExchange] using (hy.pow 3).prodMk (hx.pow 3).neg

theorem cubicExchange_nonzero_away_from_vacuum : cubicExchange 1 0 ≠ (0, 0) := by
  norm_num [cubicExchange]

/-- Homogeneous degree one but nonlinear directional dependence. Lean's
division-by-zero convention sets the displayed field to zero at the vacuum. -/
def directionalExchange (x y : ℝ) : ℝ × ℝ :=
  (y ^ 3 / (x ^ 2 + y ^ 2), -(x ^ 3) / (x ^ 2 + y ^ 2))

@[simp] theorem directionalExchange_zero : directionalExchange 0 0 = (0, 0) := by
  norm_num [directionalExchange]

theorem directionalExchange_response_balance (x y : ℝ) :
    deriv quartic x * (directionalExchange x y).1 +
      deriv quartic y * (directionalExchange x y).2 = 0 := by
  rw [quartic_deriv, quartic_deriv]
  dsimp [directionalExchange]
  ring

/-- This identity includes negative and zero scalars, with no punctured-domain
qualification and no use of an unproved continuity assertion. -/
theorem directionalExchange_homogeneous (r x y : ℝ) :
    directionalExchange (r * x) (r * y) = r • directionalExchange x y := by
  by_cases hr : r = 0
  · subst r
    simp
  by_cases hd : x ^ 2 + y ^ 2 = 0
  · have hx : x = 0 := by nlinarith [sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x]
    subst x
    subst y
    simp
  have hrd : (r * x) ^ 2 + (r * y) ^ 2 ≠ 0 := by
    have heq : (r * x) ^ 2 + (r * y) ^ 2 = r ^ 2 * (x ^ 2 + y ^ 2) := by ring
    rw [heq]
    exact mul_ne_zero (pow_ne_zero 2 hr) hd
  ext <;> dsimp [directionalExchange] <;> field_simp [hrd, hd]

/-- Every vacuum ray has an actual derivative; their joint dependence is the
nonlinear map `directionalExchange` itself. -/
theorem directionalExchange_hasDerivAt_vacuum_ray (x y : ℝ) :
    HasDerivAt (fun t : ℝ => directionalExchange (t * x) (t * y))
      (directionalExchange x y) 0 := by
  have heq : (fun t : ℝ => directionalExchange (t * x) (t * y)) =
      (fun t : ℝ => t • directionalExchange x y) := by
    funext t
    exact directionalExchange_homogeneous t x y
  rw [heq]
  simpa using (hasDerivAt_id (0 : ℝ)).smul_const (directionalExchange x y)

theorem directionalExchange_axis_and_diagonal_values :
    directionalExchange 1 0 = (0, -1) ∧
    directionalExchange 0 1 = (1, 0) ∧
    directionalExchange 1 1 = (1 / 2, -(1 / 2)) := by
  norm_num [directionalExchange]

/-- The two axes look rotational but the diagonal disproves a common linear
tangent. Axis directional derivatives alone do not establish a Jacobian. -/
theorem directionalExchange_no_common_linear_map :
    ¬ ∃ L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ),
      ∀ x y : ℝ, L (x, y) = directionalExchange x y := by
  rintro ⟨L, hL⟩
  have h := L.map_add (1, 0) (0, 1)
  norm_num [Prod.mk_add_mk, hL, directionalExchange] at h

/-- An equivalent obstruction phrased directly in terms of the actual ray
derivatives, using uniqueness of `HasDerivAt`. -/
theorem directionalExchange_no_common_linear_ray_derivative :
    ¬ ∃ L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ), ∀ x y : ℝ,
      HasDerivAt (fun t : ℝ => directionalExchange (t * x) (t * y)) (L (x, y)) 0 := by
  rintro ⟨L, hL⟩
  apply directionalExchange_no_common_linear_map
  refine ⟨L, fun x y => ?_⟩
  exact (hL x y).unique (directionalExchange_hasDerivAt_vacuum_ray x y)

/-- Frechet differentiability at the vacuum would supply one common linear
ray-derivative map, contradicting the axis/diagonal calculation above. -/
theorem directionalExchange_not_differentiableAt_vacuum :
    ¬ DifferentiableAt ℝ (fun p : ℝ × ℝ => directionalExchange p.1 p.2) (0, 0) := by
  intro h
  apply directionalExchange_no_common_linear_map
  refine ⟨(fderiv ℝ (fun p : ℝ × ℝ => directionalExchange p.1 p.2) (0, 0)).toLinearMap,
    fun x y => ?_⟩
  have hx : HasDerivAt (fun t : ℝ => t * x) x 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const x
  have hy : HasDerivAt (fun t : ℝ => t * y) y 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const y
  have hcomp := h.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hx.prodMk hy) (by simp)
  exact hcomp.unique (directionalExchange_hasDerivAt_vacuum_ray x y)

/-- Data-only descriptions of omitted assumptions; not theory-status flags. -/
structure ControlScope where
  control : String
  retained : String
  omitted : String
  limitation : String

def controlScopes : List ControlScope := [
  ⟨"mixed_quadratic_quartic", "actual balance and nonzero common linear vacuum tangent",
    "uniform strict attenuation with one gain for every input",
    "no global flow, reversibility, or primitive bridge"⟩,
  ⟨"quartic_cubic_exchange", "uniform attenuation, actual balance, nonzero field away from zero",
    "nonzero mixing in the vacuum tangent; all ray derivatives vanish",
    "I3 at three unit inputs is 36; no quadratic or Born conclusion"⟩,
  ⟨"quartic_directional_exchange", "uniform attenuation, actual balance, every ray derivative",
    "one common linear map for all vacuum ray derivatives",
    "rotational axis derivatives coexist with failure of Frechet differentiability; no continuity or flow assertion"⟩]

end

end IDT.QMClosure.AttenuationTangentCountermodels
