import Proofs.QMClosure.RationalFiniteDistribution
import Proofs.QMClosure.RawPlanePhaseProcessComparisonControl

/-!
# Classical process laws do not originate the raw response comparison

Rational finite distributions provide a mathematical completion of any raw
carrier. Their TV data processing and independent-reference laws coexist with
the actual plane control's pure-preparation midpoint obstruction. The response
extension below preserves that obstruction on Dirac inputs. No identification
of TV with the original response, calibrated comparison, or physical outcome
probabilities is assumed or concluded.
-/

namespace IDT.QMClosure.RawClassicalProcessEnvelope

noncomputable section

open RationalFiniteDistribution

variable {V W : Type*}

/-- Every deterministic map with a left inverse preserves this finite TV. -/
theorem tv_map_eq_of_leftInverse (f : V → W) (g : W → V)
    (h : Function.LeftInverse g f) (μ ν : FinDist V) :
    tv (map f μ) (map f ν) = tv μ ν := by
  have undo (ρ : FinDist V) : map g (map f ρ) = ρ := by
    rw [map_comp, show g ∘ f = id from funext h, map_id]
  apply le_antisymm (tv_map_le f μ ν)
  have hh := tv_map_le g (map f μ) (map f ν)
  rw [undo μ, undo ν] at hh
  exact hh

theorem gate_fourfold (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap) (p : V × V) :
    F (F (F (F p))) = p := by
  rw [hsquare, hsquare]
  rfl

/-- The square-swap raw gate acts isometrically after classical completion. -/
theorem gate_pushforward_tv (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap) (μ ν : FinDist (V × V)) :
    tv (map F μ) (map F ν) = tv μ ν :=
  tv_map_eq_of_leftInverse F (fun p => F (F (F p))) (gate_fourfold F hsquare) μ ν

/-- Double finite expectation of an arbitrary original real response. -/
def Qbar (Q : V → W → ℝ) (μ : FinDist V) (ν : FinDist W) : ℝ :=
  μ.coeff.sum fun x a => ν.coeff.sum fun y b => (a : ℝ) * (b : ℝ) * Q x y

@[simp] theorem Qbar_dirac (Q : V → W → ℝ) (x : V) (y : W) :
    Qbar Q (dirac x) (dirac y) = Q x y := by
  classical
  simp [Qbar, dirac]

/-- A chosen pure midpoint remains distinct from classical half-mixture
unless both endpoints and the midpoint coincide. -/
theorem pure_midpoint_mixture_wall (mid : V → V → V) (x y : V)
    (h : dirac (mid x y) =
      mixture (1 / 2) (by norm_num) (by norm_num) (dirac x) (dirac y)) :
    x = y ∧ x = mid x y := by
  obtain ⟨hx, hy⟩ := half_mixture_dirac (mid x y) x y h
  exact ⟨hx.trans hy.symm, hx⟩

section ActualPlane

open RawPlanePhaseFamily RawPlanePhaseGeometry RawPlanePhaseGramKernel
open RawPlanePhaseGramControl RawPlanePhaseMidpointControl

/-- The original exact positive midpoint defect survives the pure embedding. -/
theorem plane_Qbar_midpoint_defect :
    Qbar RawPlanePhaseProcessComparisonControl.Q (dirac (ref (-3)))
        (dirac (mid fourX fourY)) -
      (Qbar RawPlanePhaseProcessComparisonControl.Q (dirac (ref (-3))) (dirac fourX) +
       Qbar RawPlanePhaseProcessComparisonControl.Q (dirac (ref (-3))) (dirac fourY)) / 2 =
      1 / 10 := by
  simpa only [Qbar_dirac, RawPlanePhaseProcessComparisonControl.Q,
    ← distance_square_eq] using negative_three_squared_defect

theorem plane_Qbar_midpoint_violation :
    Qbar RawPlanePhaseProcessComparisonControl.Q (dirac (ref (-3)))
        (dirac (mid fourX fourY)) >
      (Qbar RawPlanePhaseProcessComparisonControl.Q (dirac (ref (-3))) (dirac fourX) +
       Qbar RawPlanePhaseProcessComparisonControl.Q (dirac (ref (-3))) (dirac fourY)) / 2 := by
  linarith [plane_Qbar_midpoint_defect]

/-- The selected coherent pure midpoint cannot be supplied by classical mixing. -/
theorem plane_midpoint_not_classical_mixture :
    dirac (mid fourX fourY) ≠
      mixture (1 / 2) (by norm_num) (by norm_num) (dirac fourX) (dirac fourY) := by
  intro h
  have hxy := (pure_midpoint_mixture_wall mid fourX fourY h).1
  have hdist := negative_three_squares
  rw [hxy] at hdist
  linarith [hdist.2.1, hdist.2.2]

end ActualPlane

end
end IDT.QMClosure.RawClassicalProcessEnvelope
