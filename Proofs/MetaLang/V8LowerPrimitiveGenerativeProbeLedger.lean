namespace IDT.MetaLang.V8

/-! Data-only research direction ledger. These are proposed local construction
rules and bounded executable questions, not new primitive axioms or theorems.
The campaign retains every candidate, including failures and untested leads. -/

inductive GenerativeProbeStatus where
  | exploratory_finite
  | not_tested
  | not_attempted
deriving DecidableEq, Repr

inductive GenerativeCancellation where
  | oppositePairs
  | triangle
deriving DecidableEq, Repr

structure GenerativePrimitiveProposal where
  id : String
  suppliedRule : String
  missingOrigin : String
deriving Repr

def lowerPrimitiveGenerativeInputs : List GenerativePrimitiveProposal :=
  [ ⟨"context_local_bags",
      "Finite bags of cyclic oriented labels inside one supplied context",
      "Derive physical contexts and labels; no new global history ontology"⟩,
    ⟨"parallel_union", "Disjoint union adds label multiplicities",
      "Derive admissible coherent parallel alternatives"⟩,
    ⟨"serial_pairs", "Cartesian pairs compose by cyclic label addition modulo m",
      "Derive admissible serial composition and the C_m label law"⟩,
    ⟨"cancellation",
      "For even m, e_j + e_(j+m/2) ~ 0; for C3, e_0 + e_1 + e_2 ~ 0",
      "Derive these local cancellation relations from the context-first base"⟩,
    ⟨"detector", "Proposed ordered signed pair counts include diagonal pairs",
      "Derive pairwise detector form, its diagonal inclusion, and coefficients"⟩ ]

structure GenerativeProbeFamily where
  id : String
  cycleOrder : Nat
  cancellation : GenerativeCancellation
  normalForm : String
  detector : String
  variants : List String
  status : GenerativeProbeStatus := .exploratory_finite
deriving Repr

def generativeHalfIntegerGrid : List (Int × Nat) :=
  [(-2, 1), (-3, 2), (-1, 1), (-1, 2), (0, 1),
    (1, 2), (1, 1), (3, 2), (2, 1)]

def lowerPrimitiveGenerativeFamilies : List GenerativeProbeFamily :=
  [ ⟨"c2_diagonal", 2, .oppositePairs, "d0 = n0 - n1",
      "sum_i d_i^2", ["history_c2_diagonal"], .exploratory_finite⟩,
    ⟨"c3_triangle", 3, .triangle, "(n0 - n2, n1 - n2)",
      "ordered pair kernel K = [1, -1/2, -1/2]",
      ["history_c3_triangle"], .exploratory_finite⟩,
    ⟨"c4_diagonal", 4, .oppositePairs, "d_i = n_i - n_(i+2)",
      "sum_i d_i^2", ["history_c4_diagonal"], .exploratory_finite⟩,
    ⟨"c6_diagonal", 6, .oppositePairs, "d_i = n_i - n_(i+3)",
      "sum_i d_i^2", ["history_c6_diagonal"], .exploratory_finite⟩,
    ⟨"c8_diagonal", 8, .oppositePairs, "d_i = n_i - n_(i+4)",
      "sum_i d_i^2", ["history_c8_diagonal"], .exploratory_finite⟩,
    ⟨"c4_raw_cardinality", 4, .oppositePairs, "d_i = n_i - n_(i+2)",
      "sum_j n_j before cancellation (negative control)",
      ["history_c4_raw_cardinality"], .exploratory_finite⟩,
    ⟨"c4_residual_l1", 4, .oppositePairs, "d_i = n_i - n_(i+2)",
      "sum_i abs(d_i) (alternative readout control)",
      ["history_c4_residual_l1"], .exploratory_finite⟩,
    ⟨"c4_diagonal_square", 4, .oppositePairs, "d_i = n_i - n_(i+2)",
      "(sum_i d_i^2)^2 (alternative readout control)",
      ["history_c4_diagonal_square"], .exploratory_finite⟩,
    ⟨"c6_kernel_grid", 6, .oppositePairs, "d_i = n_i - n_(i+3)",
      "ordered pair kernel K = [1, a, -a, -1, -a, a]",
      ["history_c6_kernel_a2_n4", "history_c6_kernel_a2_n3", "history_c6_kernel_a2_n2",
        "history_c6_kernel_a2_n1", "history_c6_kernel_a2_p0", "history_c6_kernel_a2_p1",
        "history_c6_kernel_a2_p2", "history_c6_kernel_a2_p3", "history_c6_kernel_a2_p4"], .exploratory_finite⟩,
    ⟨"c8_kernel_grid", 8, .oppositePairs, "d_i = n_i - n_(i+4)",
      "ordered pair kernel K = [1, a, 0, -a, -1, -a, 0, a]",
      ["history_c8_kernel_a2_n4", "history_c8_kernel_a2_n3", "history_c8_kernel_a2_n2",
        "history_c8_kernel_a2_n1", "history_c8_kernel_a2_p0", "history_c8_kernel_a2_p1",
        "history_c8_kernel_a2_p2", "history_c8_kernel_a2_p3", "history_c8_kernel_a2_p4"], .exploratory_finite⟩,
    ⟨"c8_quartic", 8, .oppositePairs, "d_i = n_i - n_(i+4)",
      "A^2 - 2*B^2; A = sum_i d_i^2; B = d0*d1-d0*d3+d1*d2+d2*d3",
      ["history_c8_quartic"], .exploratory_finite⟩ ]

structure GenerativeBoundedProbe where
  id : String
  scope : String
  status : GenerativeProbeStatus := .not_tested
deriving Repr

def lowerPrimitiveGenerativeProbeBounds : String :=
  "Enumerate every nonnegative raw bag with total multiplicity <= 2; all ordered pairs and triples. Do not clip union, serial-product, cancellation-insertion, or continuation outputs."

def lowerPrimitiveGenerativeProbeObligations : List GenerativeBoundedProbe :=
  [ ⟨"nonnegative_weight", "All bounded bags; preserve negative witnesses", .exploratory_finite⟩,
    ⟨"empty_zero", "Empty bag weight is zero", .exploratory_finite⟩,
    ⟨"cancellation_descent",
      "Insert every cancellation generator into every bounded base; compare normal forms and detector values",
      .exploratory_finite⟩,
    ⟨"continuation_descent",
      "Compare generator insertion under union and under left/right serial continuation by every bounded bag",
      .exploratory_finite⟩,
    ⟨"serial_norm_multiplicativity",
      "Selected diagnostic W(P serial Q) = W(P)*W(Q), not an arbitrary-state-map admissibility law",
      .exploratory_finite⟩,
    ⟨"third_order_interference",
      "Sorkin I3 for all bounded triples under supplied parallel union", .exploratory_finite⟩,
    ⟨"two_alternative_interference",
      "Seek nonadditivity under parallel union; retain exact witnesses", .exploratory_finite⟩,
    ⟨"source_screen",
      "Source proposals remain unsupported with no registered prediction adapter; standalone exact probe outcomes are separate and cannot upgrade source or physical status",
      .exploratory_finite⟩ ]

structure GenerativeKernelSelectionProbe where
  id : String
  kernel : String
  hypothesisCount : Nat
  bagCount : Nat
  distinctCancellationGenerators : Nat
  condition : String
  status : GenerativeProbeStatus := .not_tested
deriving Repr

def lowerPrimitiveGenerativeKernelSelection : List GenerativeKernelSelectionProbe :=
  [ ⟨"c3_kernel_selection", "K = [1, a, a]; a in the half-integer grid", 9, 10, 1,
      "Require W(n+c)=W(n) for every bounded reference n, not only W(c)=0",
      .exploratory_finite⟩,
    ⟨"c4_kernel_selection", "K = [1, a, b, a]; a,b in the half-integer grid", 81, 15, 2,
      "Require W(n+c)=W(n) for every bounded reference n, not only W(c)=0",
      .exploratory_finite⟩ ]

def lowerPrimitiveGenerativeKernelSelectionBoundary : String :=
  "These 90 separate hypotheses test coefficients only within the supplied quadratic ordered-pair class, diagonal inclusion, cyclic symmetry, and K0=1. They do not derive the pair ansatz, cancellation, Born readout, or physical selection; I3=0 is a consequence of the supplied quadratic ansatz, not independent evidence."

structure GenerativeFiniteOutcome where
  candidate : String
  diagnostic : String
  cases : Nat
  failures : Nat
  witness : String
deriving Repr

def lowerPrimitiveGenerativeFiniteOutcomes : List GenerativeFiniteOutcome :=
  [ ⟨"history_c3_triangle", "serial_weight_multiplicativity", 100, 0, "none within domain"⟩,
    ⟨"history_c3_triangle", "i3", 1000, 0, "none within domain; fringe [4,1,1]"⟩,
    ⟨"history_c6_diagonal", "serial_weight_multiplicativity", 784, 144,
      "x=y=e4+e5; W(x serial y)=6 versus W(x)*W(y)=4"⟩,
    ⟨"history_c8_diagonal", "serial_weight_multiplicativity", 2025, 256,
      "x=y=e6+e7; W(x serial y)=6 versus W(x)*W(y)=4"⟩,
    ⟨"history_c4_raw_cardinality", "readout_invariance", 30, 30,
      "empty -> e1+e3 changes W from 0 to 2"⟩,
    ⟨"history_c4_residual_l1", "i3", 3375, 624, "(e3,e3,e1) gives I3=2"⟩,
    ⟨"history_c4_diagonal_square", "i3", 3375, 1668, "three e0 inputs give I3=36"⟩,
    ⟨"history_c8_quartic", "serial_weight_multiplicativity", 2025, 0, "none within domain"⟩,
    ⟨"history_c8_quartic", "i3", 91125, 51592, "three e0 inputs give I3=36"⟩,
    ⟨"selection_c4_a2_-4_b2_-2", "reference_invariance", 30, 18,
      "K=[1,-2,-1,-2]; n=e3, c=e0+e2 changes W from 1 to -7 despite W(c)=0"⟩ ]

structure GenerativeProbeRunRecord where
  reportPath : String
  reportSha256Field : String
  historySubmission : String
  historyObservation : String
  mainVariantCount : Nat
  sourceCollectionCount : Nat
  additionalKernelCount : Nat
  contextualKernelChecks : Nat
  sourceStatus : String
  coefficientSelection : String
  presentationSummary : String
  status : GenerativeProbeStatus
deriving Repr

def lowerPrimitiveGenerativeCompletedRun : GenerativeProbeRunRecord :=
  { reportPath := "data/generative_history_search/campaign-v1.json.gz"
    reportSha256Field := "b5dc0709b55ca22b4defad1f2951e2add2197bd63498e84194777fe2f65070c5"
    historySubmission := "a38a5e6956633ccb190c69a28c0922409120883754ed4d90f8d57d713c78c444"
    historyObservation := "0f44e9426000ab344ea93f6ce396476fd643fde2d242e94af2aa2f8f15ed0f70"
    mainVariantCount := 27
    sourceCollectionCount := 11
    additionalKernelCount := 90
    contextualKernelChecks := 2520
    sourceStatus := "all 11 unsupported; no registered prediction adapter; candidate verdict unchanged"
    coefficientSelection := "C3 uniquely a=-1/2 in 90 checks; C4 uniquely a=0,b=-1 in 2430 checks, within supplied class"
    presentationSummary := "C6 a=-1 gives signed scalar weights; a=1/2 has the C3 lattice presentation. All 81 label products and 66 bounded weights checked; C6/C3 bag-resource bounds differ."
    status := .exploratory_finite }

structure GenerativeRemainingBridge where
  id : String
  obligation : String
  status : GenerativeProbeStatus := .not_attempted
deriving Repr

def lowerPrimitiveGenerativeRemainingBridges : List GenerativeRemainingBridge :=
  [ ⟨"physical_selection", "Select an accessible physical carrier rather than a passing finite construction", .not_attempted⟩,
    ⟨"local_cancellation_origin", "Derive cancellation and cyclic serial labels from local primitive rules", .not_attempted⟩,
    ⟨"local_detector_origin", "Derive detector pair structure and diagonal inclusion rather than assume them", .not_attempted⟩,
    ⟨"normalization_actualization", "Derive normalized readout and actualization, including null totals", .not_attempted⟩,
    ⟨"accessible_operations", "Derive accessible contexts, references, and operation-sensitive observational equivalence", .not_attempted⟩,
    ⟨"composites_continuum", "Establish physical composites and continuum closure beyond supplied bag operations", .not_attempted⟩,
    ⟨"qm_sm_gr", "Derive the remaining quantum, Standard Model, and gravity structure without importing it", .not_attempted⟩ ]

def lowerPrimitiveGenerativeReadoutAlternatives : List String :=
  [ "Quadratic signed diagonal count and C3 rational pair kernel",
    "Raw cardinality, L1, and squared quadratic C4 controls",
    "Every half-integer C6 and C8 kernel coefficient from -2 to 2",
    "C8 quartic norm; distinct detector degree is retained, not filtered away" ]

def lowerPrimitiveGenerativeUntestedLeads : List GenerativeBoundedProbe :=
  [ ⟨"c8_irrational_kernel",
      "Retain a = +/-sqrt(2)/2 in the C8 pair kernel; rational-grid failure cannot reject C8",
      .not_tested⟩ ]

def lowerPrimitiveGenerativeExistingBoundaries : List String :=
  [ "PairHistoryMeasureProbe supplies add, mul, and weight; finite signatures do not select a carrier",
    "HistoryMergeDescent assumes additive history evaluation and a supplied continuation grammar",
    "TypedRewriteStructureUnderdeterminationProbe does not derive a dagger or unique parallel product from bare rewrites",
    "NativeAmplitudeObservability supplies its expression grammar; observability is grammar-relative",
    "NativeOperationBridge does not require arbitrary admissible state maps to be algebra homomorphisms",
    "PairHistoryAdapterSafety rejects only real projection before composition (0 versus 1/2), not real theory",
    "V8ContextFirstPrimitiveBase treats global histories as compatibility scaffold, not primitives" ]

def lowerPrimitiveGenerativeProbeClaimBoundary : String :=
  "Generating scalar amplitude-like bag arithmetic from supplied context-local bags, cancellation, serial labels, and detectors is a conditional mathematical construction, not theory validation. All supplied cyclic products are commutative; the full algebra of quantum measurement and dynamics operations is not derived. Executable finite outcomes are not universal proofs, formal proof cards, Born-rule derivations, or QM/SM/GR closure."

end IDT.MetaLang.V8
