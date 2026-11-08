import Proofs.QMClosure.NativeStationaryNoiseCharacterization

/-!
# Countable history carriers and stationary native samples

A probability law on a countable whole history carrier is sent to the explicit
real native sample carrier by a supplied measurable deterministic map. If the
resulting sample law is stationary after two native smoothing steps, that law
is a Dirac measure at its actual coordinate means.

Whole-carrier countability, deterministic sampling, real coordinates and exact
native stationarity are explicit hypotheses. The conclusion concerns the
pushed-forward sample law. Infinite histories of finite-alphabet processes can
form an uncountable carrier. Stochastic output kernels and approximate
stationarity require separate hypotheses and analysis.
-/

namespace IDT.QMClosure.CountableHistoryNativeNoiseWall

noncomputable section

open MeasureTheory
open NativeStationaryNoiseCharacterization

/-- Two-step stationary native sampling of a countable whole history carrier is deterministic. -/
theorem map_eq_dirac_of_twoStepStationary {H : Type*} [Countable H] [MeasurableSpace H]
    (ρ : Measure H) [IsProbabilityMeasure ρ] (f : H → Sample) (hf : Measurable f)
    (h : TwoStepStationary (ρ.map f)) :
    ρ.map f = Measure.dirac
      (∫ x : Sample, x.1 ∂(ρ.map f), ∫ x : Sample, x.2 ∂(ρ.map f)) := by
  letI : IsProbabilityMeasure (ρ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hrange : (Set.range f).Countable := Set.countable_range f
  have hfull : (ρ.map f) (Set.range f) = 1 := by
    rw [Measure.map_apply hf hrange.measurableSet]
    have hpre : f ⁻¹' Set.range f = Set.univ := by
      ext x
      simp
    rw [hpre, measure_univ]
  exact eq_dirac_of_twoStepStationary_countable_concentration
    (ρ.map f) h (Set.range f) hrange hfull

/-- First-output stationary native sampling of a countable whole history carrier is deterministic. -/
theorem map_eq_dirac_of_firstMarginalStationary {H : Type*} [Countable H] [MeasurableSpace H]
    (ρ : Measure H) [IsProbabilityMeasure ρ] (f : H → Sample) (hf : Measurable f)
    (h : FirstMarginalStationary (ρ.map f)) :
    ρ.map f = Measure.dirac
      (∫ x : Sample, x.1 ∂(ρ.map f), ∫ x : Sample, x.2 ∂(ρ.map f)) :=
  map_eq_dirac_of_twoStepStationary ρ f hf (twoStepStationary_of_stationary (ρ.map f) h)

end
end IDT.QMClosure.CountableHistoryNativeNoiseWall
