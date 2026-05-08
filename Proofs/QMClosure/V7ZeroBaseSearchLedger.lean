namespace IDT
namespace QMClosure

/-!
V7 zero-base and executable-search recovery.

This file preserves sections 174.138-174.210: zero-base reset, ZB1/ZB2/U0,
programmatic search, closed metric-orientation selector hits, and the later
failure against the full angle/metric-composition target.
-/

structure V7ZeroBaseCandidate where
  startsBelowExistingResearchPrimitives : Prop
  avoidsPrimitiveHilbertBornMetric : Prop
  producesRecords : Prop
  keepsUnexposedAlternativesActive : Prop
  delayedComplexityPlausible : Prop
  quantitativeReadoutLawMissing : Prop

def V7ZeroBaseCandidateHonest (c : V7ZeroBaseCandidate) : Prop :=
  c.startsBelowExistingResearchPrimitives
    ∧ c.avoidsPrimitiveHilbertBornMetric
    ∧ c.producesRecords
    ∧ c.keepsUnexposedAlternativesActive
    ∧ c.delayedComplexityPlausible
    ∧ c.quantitativeReadoutLawMissing

def v7ZB1ZB2Recovered : V7ZeroBaseCandidate :=
  {
    startsBelowExistingResearchPrimitives := True,
    avoidsPrimitiveHilbertBornMetric := True,
    producesRecords := True,
    keepsUnexposedAlternativesActive := True,
    delayedComplexityPlausible := True,
    quantitativeReadoutLawMissing := True
  }

structure V7U0SearchProgram where
  executableDiscoveryTool : Prop
  negativeControlsPresent : Prop
  residueCriticalMotifSurvives : Prop
  arbitraryLookupTablesRejected : Prop
  compactLawLevelTargetRequired : Prop
  provesPrimitiveBase : Prop

def V7U0SearchProgramHonest (p : V7U0SearchProgram) : Prop :=
  p.executableDiscoveryTool
    ∧ p.negativeControlsPresent
    ∧ p.residueCriticalMotifSurvives
    ∧ p.arbitraryLookupTablesRejected
    ∧ p.compactLawLevelTargetRequired
    ∧ ¬ p.provesPrimitiveBase

def v7U0SearchProgramRecovered : V7U0SearchProgram :=
  {
    executableDiscoveryTool := True,
    negativeControlsPresent := True,
    residueCriticalMotifSurvives := True,
    arbitraryLookupTablesRejected := True,
    compactLawLevelTargetRequired := True,
    provesPrimitiveBase := False
  }

structure V7ClosedSelectorRoute where
  noSignallingBellTsirelsonToyHit : Prop
  importControlsRejectDirectBellParity : Prop
  metricBottleneckResponseToyHit : Prop
  fullBornAngleCurveFailed : Prop
  metricCompositionFailed : Prop
  nextPrimitiveIsNormalizedOverlap : Prop

def V7ClosedSelectorRouteHonest (r : V7ClosedSelectorRoute) : Prop :=
  r.noSignallingBellTsirelsonToyHit
    ∧ r.importControlsRejectDirectBellParity
    ∧ r.metricBottleneckResponseToyHit
    ∧ r.fullBornAngleCurveFailed
    ∧ r.metricCompositionFailed
    ∧ r.nextPrimitiveIsNormalizedOverlap

def v7ClosedSelectorRouteRecovered : V7ClosedSelectorRoute :=
  {
    noSignallingBellTsirelsonToyHit := True,
    importControlsRejectDirectBellParity := True,
    metricBottleneckResponseToyHit := True,
    fullBornAngleCurveFailed := True,
    metricCompositionFailed := True,
    nextPrimitiveIsNormalizedOverlap := True
  }

theorem v7_zero_base_candidate_recovered_with_readout_wall :
    V7ZeroBaseCandidateHonest v7ZB1ZB2Recovered :=
  And.intro trivial <|
    And.intro trivial <|
      And.intro trivial <|
        And.intro trivial <|
          And.intro trivial trivial

theorem v7_u0_search_recovered_as_discovery_tool_not_proof :
    V7U0SearchProgramHonest v7U0SearchProgramRecovered :=
  And.intro trivial <|
    And.intro trivial <|
      And.intro trivial <|
        And.intro trivial <|
          And.intro trivial (by intro h; exact h)

theorem v7_closed_selector_hit_and_wall_recovered :
    V7ClosedSelectorRouteHonest v7ClosedSelectorRouteRecovered :=
  And.intro trivial <|
    And.intro trivial <|
      And.intro trivial <|
        And.intro trivial <|
          And.intro trivial trivial

end QMClosure
end IDT
