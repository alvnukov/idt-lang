import Proofs.QMClosure.AttenuationTangentCountermodels

namespace IDT.QMClosure.DenseExchangeCountermodels

noncomputable section

/-!
# A nonzero cross operator does not imply dense exchange

The response is quartic on a direction invisible to the exchange operators.
It has uniform strict attenuation and an actual Frechet derivative everywhere.
The exchange is globally linear, has its displayed actual vacuum derivative,
and exactly conserves the raw response. Its nonzero cross operator has range
in a proper closed subspace. Thus nonzero mixing alone cannot replace dense
combined exchange range. The response is live but is not faithful: an entire
nonzero coordinate axis has zero response. No physical access, IDT primitive
origin, Born, or full-QM conclusion is asserted.
-/

abbrev V := ℝ × ℝ

def response (x : V) : ℝ := x.2 ^ 4

/-- Projection onto the coordinate invisible to the response. -/
def crossOperator : V →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0

@[simp] theorem crossOperator_apply (x : V) : crossOperator x = (x.1, 0) := rfl

def P (_x y : V) : V := crossOperator y

def Q (x _y : V) : V := -crossOperator x

/-- The block entries are A = D = 0, B = E, C = -E. -/
def blockTangent : (V × V) →L[ℝ] (V × V) :=
  (crossOperator.comp (ContinuousLinearMap.snd ℝ V V)).prod
    (-(crossOperator.comp (ContinuousLinearMap.fst ℝ V V)))

@[simp] theorem blockTangent_apply (x y : V) :
    blockTangent (x, y) = (P x y, Q x y) := rfl

theorem response_hasFDerivAt (x : V) :
    HasFDerivAt response
      ((4 * x.2 ^ 3) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  simpa [response] using
    (hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 4

theorem response_differentiable : Differentiable ℝ response :=
  fun x => (response_hasFDerivAt x).differentiableAt

theorem response_fderiv (x : V) :
    fderiv ℝ response x =
      (4 * x.2 ^ 3) • ContinuousLinearMap.snd ℝ ℝ ℝ :=
  (response_hasFDerivAt x).fderiv

theorem response_nonnegative (x : V) : 0 ≤ response x := by
  dsimp [response]
  positivity

@[simp] theorem response_zero : response 0 = 0 := by simp [response]

theorem response_live : response (0, 1) = 1 := by norm_num [response]

theorem response_not_faithful : ((1, 0) : V) ≠ 0 ∧ response (1, 0) = 0 := by
  norm_num [response]

theorem response_uniform_scaling (r : ℝ) (x : V) :
    response (r • x) = r ^ 4 * response x := by
  simp [response, mul_pow]

theorem response_strict_attenuation_witness :
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧ (0 : ℝ) < (1 / 2 : ℝ) ^ 4 ∧
    ∀ x : V, response ((1 / 2 : ℝ) • x) =
      (1 / 2 : ℝ) ^ 4 * response x := by
  exact ⟨by norm_num, by norm_num, by norm_num, response_uniform_scaling (1 / 2)⟩

/-- Raw balance uses the actual analytic derivative, not a named coefficient. -/
theorem raw_response_balance (x y : V) :
    fderiv ℝ response x (P x y) + fderiv ℝ response y (Q x y) = 0 := by
  simp [response_fderiv, P, Q]

theorem exchange_hasFDerivAt (z : V × V) :
    HasFDerivAt (fun p : V × V => (P p.1 p.2, Q p.1 p.2)) blockTangent z := by
  exact blockTangent.hasFDerivAt

theorem exchange_fderiv_at_vacuum :
    fderiv ℝ (fun p : V × V => (P p.1 p.2, Q p.1 p.2)) 0 = blockTangent :=
  (exchange_hasFDerivAt 0).fderiv

theorem exchange_hasDerivAt_vacuum_ray (x y : V) :
    HasDerivAt (fun t : ℝ => (P (t • x) (t • y), Q (t • x) (t • y)))
      (blockTangent (x, y)) 0 := by
  have h := blockTangent.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).smul_const (x, y))
  simpa [Function.comp_def, blockTangent, P, Q, crossOperator] using h

theorem crossOperator_nonzero : crossOperator ≠ 0 := by
  intro h
  have hv := congrArg (fun L : V →L[ℝ] V => (L (1, 0)).1) h
  norm_num at hv

theorem exchange_nonzero : (P (0, 0) (1, 0), Q (0, 0) (1, 0)) ≠ 0 := by
  norm_num [P, Q]

/-- The combined B,C range misses every vector with nonzero second coordinate. -/
theorem combined_range_invisible (p : V × V) :
    (crossOperator p.1 + (-crossOperator) p.2).2 = 0 := by simp

theorem combined_range_not_dense :
    ¬ DenseRange (fun p : V × V => crossOperator p.1 + (-crossOperator) p.2) := by
  intro hd
  have hrange : Set.range (fun p : V × V =>
      crossOperator p.1 + (-crossOperator) p.2) ⊆ {z : V | z.2 = 0} := by
    rintro z ⟨p, rfl⟩
    exact combined_range_invisible p
  have hclosed : IsClosed {z : V | z.2 = 0} :=
    isClosed_eq continuous_snd continuous_const
  have hzero := closure_minimal hrange hclosed (hd (0, 1))
  norm_num at hzero

/-- Failure of the quadratic parallelogram identity in the live direction. -/
theorem response_not_parallelogram :
    ¬ ∀ x y : V, response (x + y) + response (x - y) =
      2 * response x + 2 * response y := by
  intro h
  have hh := h (0, 1) (0, 1)
  norm_num [response] at hh

theorem response_I3_live_direction :
    ReferenceNormalizationCountermodels.thirdOrderDifference
      (fun t : ℝ => response (0, t)) 1 1 1 = 36 := by
  norm_num [ReferenceNormalizationCountermodels.thirdOrderDifference, response]

/-- Data only: this ledger neither upgrades nor closes a theory claim. -/
structure ControlScope where
  control : String
  retained : String
  omitted : String
  limitation : String

def controlScopes : List ControlScope := [
  ⟨"quartic_invisible_direction_nonzero_cross_operator",
    "nonnegative differentiable live response, uniform strict attenuation, actual raw balance, actual common linear vacuum tangent, nonzero cross operator and exchange",
    "dense combined B,C range",
    "the exchanged coordinate is invisible; response is not faithful and fails the parallelogram law; I3 in the live direction is 36; no primitive or full-QM claim"⟩]

end

end IDT.QMClosure.DenseExchangeCountermodels
