/-!
# Operational primitive research ledger

Authoritative research-plan metadata for the parent-reviewed operational route.
These stages describe research tasks, not manifest proof statuses. Compiling this
file checks its metadata, not the mathematical statements written as strings.
Checked evidence names point to inspected declarations; planned artifacts are
kept separately and never serve as checked evidence. Kernel authority remains in
the cited source theorems under their actual hypotheses.

No entry closes the original Hilbert-carrier or Born obligations, derives full
QM or GR, fixes physical scales, or explains dark matter or dark energy.
-/

namespace IDT.MetaLang.V8OperationalPrimitiveResearchLedger

inductive ResearchStage where
  /-- A kernel theorem conditional on its supplied mathematical contract. -/
  | conditionalKernelTheorem
  /-- An analytic result whose Lean formalization remains unchecked. -/
  | inFormalization
  /-- An analytic result awaiting a Lean artifact. -/
  | analyticAwaitingFormalization
  /-- An unresolved physical justification or interpretation obligation. -/
  | openPhysicalBridge
  deriving Repr, DecidableEq

inductive ReviewState where
  | parentAccepted
  | kernelCheckedIndependentReviewPending
  | notYetKernelChecked
  | openObligation
  deriving Repr, DecidableEq

structure CheckedEvidence where
  sourcePath : String
  declarations : List String
  deriving Repr, DecidableEq

structure ResearchTask where
  id : String
  stage : ResearchStage
  review : ReviewState
  assumptions : List String
  conclusions : List String
  checkedEvidence : List CheckedEvidence
  plannedArtifacts : List String
  dependencies : List String
  limits : List String
  deriving Repr, DecidableEq

def operationalPositiveReadout : ResearchTask := {
  id := "operational_positive_readout"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supplied additive commutative monoid and complete additive two-port T.",
    "Diagonal transparency and T squared equals swap on every input.",
    "Real W is nonnegative everywhere, W(0)=0, and pair weight is conserved on every input."]
  conclusions := [
    "Derived antipodes extend the supplied monoid to an additive group.",
    "T determines a genuine half and additive J with J squared equal to minus identity.",
    "W is quadratic and its algebraic Sorkin third-order expression I3 vanishes."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/TransparentSwapRoot.lean"
      declarations := ["IDT.QMClosure.TransparentSwapRoot.reconstruct_operation"] },
    { sourcePath := "Proofs/QMClosure/OperationalQuadraticReconstruction.lean"
      declarations := [
        "IDT.QMClosure.OperationalQuadraticReconstruction.groupFromAntipodes",
        "IDT.QMClosure.OperationalQuadraticReconstruction.reconstruct_positive_operation"] }]
  plannedArtifacts := []
  dependencies := []
  limits := ["Physical justification of addition, the root laws, positivity and all-input conservation remains open."] }

def mixerRecordNaturality : ResearchTask := {
  id := "mixer_record_naturality"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Source and target mixers satisfy the supplied additive transparent square-swap contracts.",
    "Naturality means exact full-carrier unnormalized L intertwining the two complete mixers."]
  conclusions := [
    "L(0)=0 together with intertwining is equivalent to additivity and phase compatibility.",
    "An arbitrary intertwiner is affine with phase-compatible additive part.",
    "Observed Q(L(0))=0 suffices for positive-quadratic pullback, allowing null affine shift.",
    "Independent source-root transfer reconstructs the record weight assuming observed vacuum W(L(0))=0, output nonnegativity and global output conservation."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/MixerRecordNaturality.lean"
      declarations := [
        "IDT.QMClosure.MixerRecordNaturality.vacuum_intertwines_iff",
        "IDT.QMClosure.MixerRecordNaturality.affine_classification",
        "IDT.QMClosure.MixerRecordNaturality.positive_quadratic_pullback",
        "IDT.QMClosure.MixerRecordNaturality.reconstruct_record_weight"] }]
  plannedArtifacts := []
  dependencies := ["operational_positive_readout"]
  limits := [
    "Total conservation does not derive channel naturality or branch conservation.",
    "No events or probability actualization are derived."] }

def positiveQuadraticPolarization : ResearchTask := {
  id := "positive_quadratic_polarization"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := ["An additive commutative group with globally positive real quadratic Q."]
  conclusions := [
    "Real polarization is symmetric and biadditive; positivity on integer combinations yields Cauchy-Schwarz.",
    "Q(x-y)=0 iff Q(x+z)=Q(y+z) for every reference z.",
    "Dominated positive quadratic readouts descend through Q-null directions."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/PositiveQuadraticPolarization.lean"
      declarations := [
        "IDT.QMClosure.PositiveQuadraticPolarization.symmetric",
        "IDT.QMClosure.PositiveQuadraticPolarization.add_left",
        "IDT.QMClosure.PositiveQuadraticPolarization.add_right",
        "IDT.QMClosure.PositiveQuadraticPolarization.cauchy_schwarz",
        "IDT.QMClosure.PositiveQuadraticPolarization.null_iff_all_reference_tests",
        "IDT.QMClosure.PositiveQuadraticPolarization.dominated_null_invisibility"] }]
  plannedArtifacts := []
  dependencies := []
  limits := ["No carrier scalar action, topology or divisibility is supplied or inferred here."] }

def nonadditiveClassicalControl : ResearchTask := {
  id := "nonadditive_classical_swap_root"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := ["Explicit Fin 4 raw carrier with max merge, reversible two-port route and weights [0,1,1,2]."]
  conclusions := [
    "The raw route is transparent, squares to swap and conserves nonnegative weight.",
    "It fails max-merge additivity and the merge admits no antipode for state 1.",
    "Dropping coherent additivity from this route contract does not force the additive reconstruction."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NonadditiveClassicalSwapRoot.lean"
      declarations := [
        "IDT.QMClosure.NonadditiveClassicalSwapRoot.transparent",
        "IDT.QMClosure.NonadditiveClassicalSwapRoot.square",
        "IDT.QMClosure.NonadditiveClassicalSwapRoot.bijective",
        "IDT.QMClosure.NonadditiveClassicalSwapRoot.weight_conservation",
        "IDT.QMClosure.NonadditiveClassicalSwapRoot.route_not_merge_additive",
        "IDT.QMClosure.NonadditiveClassicalSwapRoot.one_has_no_merge_inverse"] }]
  plannedArtifacts := []
  dependencies := []
  limits := ["This control establishes no minimality theorem for the primitive contract."] }

def jointReadoutFrontier : ResearchTask := {
  id := "quadratic_joint_readout_frontier"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Arbitrary additive group and one common family of globally positive quadratic fine-record weights.",
    "Normalized probability rows realized with common kappa>0 on preparations 2E+F, 2E-F, E+2F, E-2F.",
    "Finite record set and fixed stochastic responses.",
    "Attainment controls use a separately supplied real plane with four effects."]
  conclusions := [
    "400(2A-1)^2+225(2B-1)^2 <= 144; parity equivalence is derived without a calibration premise.",
    "Four-effect real-plane controls attain the whole ellipse and the robust frontier for epsilon in [0,3/10]."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/QuadraticJointReadoutFrontier.lean"
      declarations := [
        "IDT.QMClosure.QuadraticJointReadoutFrontier.joint_score_ellipse",
        "IDT.QMClosure.QuadraticJointReadoutFrontier.parity_equivalent",
        "IDT.QMClosure.QuadraticJointReadoutFrontier.marginal_error_frontier"] },
    { sourcePath := "Proofs/QMClosure/QuadraticJointReadoutControls.lean"
      declarations := [
        "IDT.QMClosure.QuadraticJointReadoutControls.whole_ellipse_attained",
        "IDT.QMClosure.QuadraticJointReadoutControls.robust_frontier_attained"] }]
  plannedArtifacts := []
  dependencies := ["positive_quadratic_polarization"]
  limits := [
    "Probability and event interpretation are supplied.",
    "No instrument, state update or actualization is derived."] }

def positiveGramKernel : ResearchTask := {
  id := "positive_quadratic_gram_and_hermitian_kernel"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "An additive group with globally positive real quadratic Q.",
    "For the complex kernel: additive J, J squared equals minus identity, and Q(Jx)=Q(x)."]
  conclusions := [
    "Full finite real and complex Gram positive semidefiniteness.",
    "A finite additive carrier has Q identically zero."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/PositiveQuadraticGram.lean"
      declarations := [
        "IDT.QMClosure.PositiveQuadraticGram.gram_nonnegative",
        "IDT.QMClosure.PositiveQuadraticGram.finite_carrier_zero"] },
    { sourcePath := "Proofs/QMClosure/QuadraticHermitianKernel.lean"
      declarations := [
        "IDT.QMClosure.QuadraticHermitianKernel.complex_gram_nonnegative",
        "IDT.QMClosure.QuadraticHermitianKernel.posSemidef"] }]
  plannedArtifacts := []
  dependencies := ["positive_quadratic_polarization"]
  limits := [
    "Kernel checked and independently accepted under the stated mathematical assumptions.",
    "No topology or scalar action on the native carrier is supplied; no Hilbert completion is yet proved."] }

def rawMedialAddition : ResearchTask := {
  id := "raw_medial_addition"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Raw set, chosen zero, idempotent medial binary m and bookend m(m(x,y),m(y,x))=y.",
    "No input additive structure or port bijectivity."]
  conclusions := [
    "Port bijectivity follows from the supplied laws using injective-H localization and reflected finite inverse terms.",
    "The raw laws reconstruct a canonical additive group, half and phase.",
    "Canonical addition is unique relative to the chosen zero among operations with both zero laws that satisfy compatibility with m."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/MedialSwapRoot.lean"
      declarations := [
        "IDT.QMClosure.MedialSwapRoot.portH_injective"] },
    { sourcePath := "Proofs/QMClosure/MedialPortLocalization.lean"
      declarations := [
        "IDT.QMClosure.MedialSwapRoot.raw_portA_bijective",
        "IDT.QMClosure.MedialSwapRoot.raw_portB_bijective",
        "IDT.QMClosure.MedialSwapRoot.canonical_add_unique",
        "IDT.QMClosure.MedialSwapRoot.raw_reconstruction",
        "IDT.QMClosure.MedialSwapRoot.canonicalGroup"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "Exact medial equality means row/column 2-by-2 full-preparation commutation.",
    "It is neither mere locality/no-signalling nor an inevitable physical primitive."] }

def diagonalNormalization : ResearchTask := {
  id := "diagonal_normalization"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Raw medial binary m with bookend, without idempotence.",
    "Complete-operation front end: raw set, chosen zero, T squared equals swap and medial first channel.",
    "Positive readout additionally assumes real W, W(0)=0, global nonnegativity and conservation on all input pairs."]
  conclusions := [
    "D(x)=m(x,x) is involutive and D(m(x,y))=m(Dx,Dy).",
    "n=D composed with m is idempotent, medial and bookend.",
    "Pair conservation yields W(Dx)=W(x), hence conservation for n.",
    "The normalized operation reconstructs a group and, under the positive-readout contract, quadratic readout and algebraic I3=0.",
    "The complete raw T front end requires no input addition, port bijectivity or transparency premise."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/MedialPortLocalization.lean"
      declarations := [
        "IDT.QMClosure.MedialSwapRoot.DiagonalNormalization.diagonal_involutive",
        "IDT.QMClosure.MedialSwapRoot.DiagonalNormalization.diagonal_map",
        "IDT.QMClosure.MedialSwapRoot.DiagonalNormalization.normalized_laws",
        "IDT.QMClosure.MedialSwapRoot.DiagonalNormalization.diagonal_preserves_readout",
        "IDT.QMClosure.MedialSwapRoot.DiagonalNormalization.normalized_conserves_readout",
        "IDT.QMClosure.MedialSwapRoot.DiagonalNormalization.normalizedGroup",
        "IDT.QMClosure.MedialSwapRoot.DiagonalNormalization.normalized_positive_readout",
        "IDT.QMClosure.MedialSwapRoot.CompleteOperation.group",
        "IDT.QMClosure.MedialSwapRoot.CompleteOperation.positive_readout"] }]
  plannedArtifacts := [
    "ANALYTIC ONLY: classify the original diagonal D as affine at the chosen origin and analyze possible null shifts; not checked by the normalization artifact."]
  dependencies := ["raw_medial_addition"]
  limits := [
    "The group and readout conclusions concern the normalized operation; original T is not asserted additive.",
    "The original diagonal need not fix the chosen zero.",
    "D and n are mathematical normal forms; physical unary implementation and copying an unknown state are not established."] }

def canonicalHilbertCompletion : ResearchTask := {
  id := "canonical_hilbert_completion"
  stage := .inFormalization
  review := .notYetKernelChecked
  assumptions := [
    "The positive quadratic Hermitian kernel contract and a genuine half for density of the native image."]
  conclusions := [
    "Analytic construction: free complex space on the carrier, kernel form, null quotient and metric completion.",
    "Analytic target: additive phi, phi(Jx)=i phi(x), norm(phi(x)) squared equals W(x), dense native image and unique unitary dense realization."]
  checkedEvidence := []
  plannedArtifacts := [
    "UNCHECKED in-progress artifact: Proofs/QMClosure/CanonicalQuadraticHilbert.lean.",
    "Formalize the free-space/null-quotient completion and dense realization.",
    "Candidate library interfaces only: PreInnerProductSpace.Core and UniformSpace.Completion."]
  dependencies := ["positive_quadratic_gram_and_hermitian_kernel", "operational_positive_readout"]
  limits := [
    "Complex structure is an output of the construction, not an assumed native complex scalar action.",
    "The native carrier may be incomplete or degenerate.",
    "Physical availability of completion states and processes is not established.",
    "The original hilbert_carrier_derivation and Born obligations remain open."] }

def recordEffects : ResearchTask := {
  id := "record_effects_after_completion"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Canonical completion plus finite dominated positive quadratic phase-invariant branch forms resolving the total readout Q, with sum_r q_r(x)=Q(x) for every x, or a natural channel resolution."]
  conclusions := [
    "Analytic target: bounded complex effects summing to identity.",
    "Analytic target: natural affine channels descend to contractions after null quotient under the resolution contract."]
  checkedEvidence := []
  plannedArtifacts := ["Formalize bounded effects and resolved channel descent after completion; artifact name not assigned."]
  dependencies := ["canonical_hilbert_completion", "mixer_record_naturality", "positive_quadratic_polarization"]
  limits := ["No actualization, projectivity, repeatability or state update is derived."] }

def openBridge (id : String) (obligation : String) : ResearchTask := {
  id := id
  stage := .openPhysicalBridge
  review := .openObligation
  assumptions := []
  conclusions := []
  checkedEvidence := []
  plannedArtifacts := []
  dependencies := []
  limits := [obligation] }

/-- Global obligations remain live independently of the conditional theorems. -/
def globalBridges : List ResearchTask := [
  openBridge "physical_raw_root_medial_all_input_closure"
    "Physically justify the raw root, exact medial law and closure over all inputs.",
  openBridge "real_archimedean_readout_codomain"
    "Justify the real Archimedean readout codomain rather than silently treating it as derived.",
  openBridge "probability_actualization"
    "Derive or explicitly supply the probability/event actualization bridge.",
  openBridge "physical_state_process_completeness"
    "Justify physically available completion states and processes.",
  openBridge "continuous_dynamics"
    "Close continuous dynamics without importing the desired quantum dynamics.",
  openBridge "tensor_local_tomography_bell"
    "Close tensor/composite, local-tomography and Bell obligations.",
  openBridge "physical_scales"
    "First-principles hbar, G and alpha remain unresolved; calibrated anchors do not close them."]

def researchTasks : List ResearchTask := [
  operationalPositiveReadout, mixerRecordNaturality, positiveQuadraticPolarization,
  nonadditiveClassicalControl, jointReadoutFrontier, positiveGramKernel,
  rawMedialAddition, diagonalNormalization, canonicalHilbertCompletion, recordEffects]

def ledger : List ResearchTask := researchTasks ++ globalBridges

end IDT.MetaLang.V8OperationalPrimitiveResearchLedger
