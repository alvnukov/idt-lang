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
    "This kernel artifact alone does not construct completion; see canonical_hilbert_completion."] }

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
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Additive group with globally positive real quadratic Q and additive J with J squared equal to minus identity and Q(Jx)=Q(x).",
    "Density of the feature image additionally uses a supplied additive half with half(x)+half(x)=x."]
  conclusions := [
    "The free complex space carries the kernel semidefinite form; separated completion constructs an actual complete complex Hilbert output.",
    "Feature inner products equal the kernel, squared feature norm equals Q, and the feature respects addition and J.",
    "Feature equality is exactly Q-null difference, equivalently equality of all canonical coherent-reference readouts.",
    "The complex span of the feature image is dense in general; the feature image itself is dense with the supplied additive half."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/CanonicalQuadraticHilbert.lean"
      declarations := [
        "IDT.QMClosure.CanonicalQuadraticHilbert.Free",
        "IDT.QMClosure.CanonicalQuadraticHilbert.Hilbert",
        "IDT.QMClosure.CanonicalQuadraticHilbert.inner_feature",
        "IDT.QMClosure.CanonicalQuadraticHilbert.norm_feature_sq",
        "IDT.QMClosure.CanonicalQuadraticHilbert.feature_add",
        "IDT.QMClosure.CanonicalQuadraticHilbert.feature_phase",
        "IDT.QMClosure.CanonicalQuadraticHilbert.feature_eq_iff",
        "IDT.QMClosure.CanonicalQuadraticHilbert.feature_eq_iff_all_reference_tests",
        "IDT.QMClosure.CanonicalQuadraticHilbert.dense_span_feature",
        "IDT.QMClosure.CanonicalQuadraticHilbert.denseRange_feature"] }]
  plannedArtifacts := []
  dependencies := ["positive_quadratic_gram_and_hermitian_kernel"]
  limits := [
    "Complex scalars and topology belong to the constructed output, not the native input carrier.",
    "The native carrier may be incomplete or degenerate.",
    "Physical availability of completion states and processes is not established.",
    "Unitary uniqueness is recorded separately in the accepted canonical_hilbert_uniqueness task.",
    "The original hilbert_carrier_derivation and Born obligations remain open."] }

def rawOperationalHilbertFacade : ResearchTask := {
  id := "raw_operational_hilbert_facade"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "RawOperationalHilbert.Data on raw V supplies chosen zero, raw complete T, T squared equal to swap and global mediality of its first channel.",
    "Real W has zero weight at the chosen zero, is globally nonnegative and is conserved on all input pairs.",
    "No algebraic or topological typeclass on raw V is an input."]
  conclusions := [
    "The diagonal-normalized operation reconstructs the canonical additive group, positive quadratic weight, phase and genuine half.",
    "An actual complete complex Hilbert output and feature map from the original raw V are constructed.",
    "The feature respects canonical addition and phase, has squared norm W, and identifies exactly null differences and equality of all canonical coherent-reference tests.",
    "The feature image is dense using the operationally reconstructed half."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawOperationalHilbert.lean"
      declarations := [
        "IDT.QMClosure.RawOperationalHilbert.Data",
        "IDT.QMClosure.RawOperationalHilbert.Data.derivedGroup",
        "IDT.QMClosure.RawOperationalHilbert.Data.carrier_add",
        "IDT.QMClosure.RawOperationalHilbert.Data.quadratic",
        "IDT.QMClosure.RawOperationalHilbert.Data.phase",
        "IDT.QMClosure.RawOperationalHilbert.Data.Hilbert",
        "IDT.QMClosure.RawOperationalHilbert.Data.feature",
        "IDT.QMClosure.RawOperationalHilbert.Data.norm_feature_sq",
        "IDT.QMClosure.RawOperationalHilbert.Data.feature_add",
        "IDT.QMClosure.RawOperationalHilbert.Data.feature_phase",
        "IDT.QMClosure.RawOperationalHilbert.Data.feature_eq_iff",
        "IDT.QMClosure.RawOperationalHilbert.Data.feature_eq_iff_all_reference_tests",
        "IDT.QMClosure.RawOperationalHilbert.Data.denseRange_feature"] }]
  plannedArtifacts := []
  dependencies := ["diagonal_normalization", "canonical_hilbert_completion"]
  limits := [
    "Original T is not asserted additive; reconstructed addition concerns its mathematical diagonal normal form.",
    "Normalization does not assert physical copying or process availability.",
    "The supplied raw laws are not justified from the original IDT primitive base here.",
    "The original Hilbert-carrier and Born obligations remain open."] }

def normalizedMixerGeneratedProcessWall : ResearchTask := {
  id := "normalized_mixer_generated_process_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Fixed finite wire set and explicit Circuit syntax: identity, distinct-wire normalized transparent additive pair mixer T, permutations and composition.",
    "T squared equals swap; readout conclusions additionally use a globally positive real quadratic Q conserved by T.",
    "Retained-output null and phase obstructions use retained lossless weight; the exact-vacuum phase obstruction uses the reconstructed half and no readout."]
  conclusions := [
    "The generated circuits preserve coherent sum and total conserved readout.",
    "Literal vacuum input/output on all other wires forces retained output y=x; exact quarter-phase output forces x=0 without a readout premise.",
    "Retained lossless weight forces identity modulo Q-null directions; quarter-phase output forces Q(x)=0.",
    "A fixed reference with exact phase correctness at x and zero does not evade the obstruction because circuit evolution is additive.",
    "Selecting the A branch twice gives half(Jx) with weight Q(x)/4.",
    "The full coherent-reference family can distinguish x from Jx when Q(x)>0, using an explicit reference; this is not a statement about every individual test."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/MixerGeneratedProcessWall.lean"
      declarations := [
        "IDT.QMClosure.MixerGeneratedProcessWall.Circuit",
        "IDT.QMClosure.MixerGeneratedProcessWall.Circuit.preserves_sum",
        "IDT.QMClosure.MixerGeneratedProcessWall.Circuit.preserves_readout",
        "IDT.QMClosure.MixerGeneratedProcessWall.exact_vacuum_identity",
        "IDT.QMClosure.MixerGeneratedProcessWall.reconstructed_exact_phase_forces_zero",
        "IDT.QMClosure.MixerGeneratedProcessWall.lossless_identity_mod_null",
        "IDT.QMClosure.MixerGeneratedProcessWall.reconstructed_phase_requires_null",
        "IDT.QMClosure.MixerGeneratedProcessWall.fixed_reference_phase_requires_null",
        "IDT.QMClosure.MixerGeneratedProcessWall.selected_two_A_branch",
        "IDT.QMClosure.MixerGeneratedProcessWall.coherent_reference_test"] }]
  plannedArtifacts := []
  dependencies := ["operational_positive_readout", "positive_quadratic_polarization"]
  limits := [
    "This wall concerns only the explicitly normalized transparent gate language; decorated raw T is outside it.",
    "Variable-width embedding, physical discard, coherent-reference availability and branch selection are not established.",
    "The branch fraction Q(x)/4 is an algebraic weight, not an event probability.",
    "Mathematical phase existence does not establish that these processes generate a phase gate.",
    "This restricted wall does not rule out physical phase gates in a separately justified process language."] }

def canonicalHilbertUniqueness : ResearchTask := {
  id := "canonical_hilbert_uniqueness"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Native additive group, globally positive real quadratic Q and additive quarter-turn J preserving Q.",
    "A complete comparison complex Hilbert output with feature family realizing the same kernel.",
    "Whole-output equivalence additionally requires dense generated complex span of the comparison features."]
  conclusions := [
    "There is a unique feature-preserving complex linear isometric embedding into the comparison output.",
    "Without a density premise, its exact range is the closed complex span of the comparison features.",
    "With dense generated complex span, there is a unique feature-preserving complex linear isometry equivalence onto the whole comparison output.",
    "An additive comparison feature map preserving squared norm Q and phase covariance realizes the same kernel; the dense-span equivalence follows under these operational conditions."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/CanonicalHilbertUniqueness.lean"
      declarations := [
        "IDT.QMClosure.CanonicalHilbertUniqueness.embedding_feature",
        "IDT.QMClosure.CanonicalHilbertUniqueness.embedding_unique",
        "IDT.QMClosure.CanonicalHilbertUniqueness.range_embedding",
        "IDT.QMClosure.CanonicalHilbertUniqueness.existsUnique_equivalence",
        "IDT.QMClosure.CanonicalHilbertUniqueness.inner_eq_kernel_of_weight_phase",
        "IDT.QMClosure.CanonicalHilbertUniqueness.existsUnique_equivalence_of_weight_phase"] }]
  plannedArtifacts := []
  dependencies := ["canonical_hilbert_completion"]
  limits := [
    "No native topology, scalar action, half or definiteness premise is required; the zero readout is allowed.",
    "The comparison Hilbert structure belongs to an output realization, not to the native input carrier.",
    "Uniqueness is among feature-preserving complex linear isometries, relative to Q and J.",
    "Uniqueness of mathematical realizations does not establish physically available states or processes."] }

def compositeProductKernel : ResearchTask := {
  id := "composite_product_kernel"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Core: three additive groups with compatible quarter-turn phases, separate additivity and phase alignment of p, and universal QC(p(x,y))=QA(x)*QB(y).",
    "The core uses positive quadratic QB and QC; a positive-quadratic QA premise is not needed there.",
    "Mixer adapter: positive quadratic QA, QB and QC; normalized additive transparent square-swap mixers in all three carriers with explicit alignment to the kernel phases.",
    "The adapter supplies separate exact full-carrier Intertwines laws in the two slots and the universal weight factorization law."]
  conclusions := [
    "The core forces K_C(p(x,y),p(x',y'))=K_A(x,x')*K_B(y,y').",
    "Separate mixer naturality gives affine slot maps; double centering removes the readout-null offsets p(x,0), p(0,y) and p(0,0).",
    "The normalized map is separately additive and phase-compatible while preserving the original readout and kernel.",
    "The original uncentered p has the product kernel; its two additive defects and two phase defects are QC-null."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/CompositeProductKernel.lean"
      declarations := [
        "IDT.QMClosure.CompositeProductKernel.product_kernel",
        "IDT.QMClosure.CompositeProductKernel.MixerBridge",
        "IDT.QMClosure.CompositeProductKernel.MixerBridge.normalized_add_phase",
        "IDT.QMClosure.CompositeProductKernel.normalized_readout",
        "IDT.QMClosure.CompositeProductKernel.normalized_kernel",
        "IDT.QMClosure.CompositeProductKernel.mixer_product_kernel",
        "IDT.QMClosure.CompositeProductKernel.observable_defects_null"] }]
  plannedArtifacts := []
  dependencies := ["mixer_record_naturality", "positive_quadratic_gram_and_hermitian_kernel"]
  limits := [
    "No strict native zero-offset equations p(x,0)=0 or p(0,y)=0 are assumed.",
    "There is no native half premise; the mixers provide their halves.",
    "Tensor completion, tensor exhaustion, physical product availability, monoidal coherence, Bell and actualization remain open."] }

def compositeProductControls : ResearchTask := {
  id := "composite_product_controls"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Explicit mathematical controls on supplied complex coordinate spaces, not reconstructed physical product primitives."]
  conclusions := [
    "Conjugating one product slot preserves separate additivity and multiplicative norm but reverses that slot's phase; the actual reconstructed-kernel comparison gives -i versus +i.",
    "A universally complex-bilinear product has all four basis product norms and both full reference-slice readout laws, yet its off-axis readout is 26/5 rather than the factor value 4.",
    "The raw signs N and -N have the same diagonal-normalized mixer; separate normalized naturality holds while the corresponding raw second-slot naturality fails."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/CompositeProductControls.lean"
      declarations := [
        "IDT.QMClosure.CompositeProductControls.ConjugateSlot.reconstructed_kernel_eq",
        "IDT.QMClosure.CompositeProductControls.ConjugateSlot.phase_right_reversed",
        "IDT.QMClosure.CompositeProductControls.ConjugateSlot.output_kernel_value",
        "IDT.QMClosure.CompositeProductControls.ConjugateSlot.factor_kernel_value",
        "IDT.QMClosure.CompositeProductControls.ConjugateSlot.reconstructed_kernel_factorization_fails",
        "IDT.QMClosure.CompositeProductControls.ReferenceSlices.scalar_left",
        "IDT.QMClosure.CompositeProductControls.ReferenceSlices.scalar_right",
        "IDT.QMClosure.CompositeProductControls.ReferenceSlices.basis_product_norms",
        "IDT.QMClosure.CompositeProductControls.ReferenceSlices.full_left_reference_slice",
        "IDT.QMClosure.CompositeProductControls.ReferenceSlices.full_right_reference_slice",
        "IDT.QMClosure.CompositeProductControls.ReferenceSlices.off_axis_value",
        "IDT.QMClosure.CompositeProductControls.ReferenceSlices.off_axis_factor_value",
        "IDT.QMClosure.CompositeProductControls.ReferenceSlices.full_factorization_fails",
        "IDT.QMClosure.CompositeProductControls.RawSign.normalized_rawB",
        "IDT.QMClosure.CompositeProductControls.RawSign.normalized_naturality_left",
        "IDT.QMClosure.CompositeProductControls.RawSign.normalized_rawB_naturality_right",
        "IDT.QMClosure.CompositeProductControls.RawSign.raw_naturality_fails"] }]
  plannedArtifacts := []
  dependencies := ["composite_product_kernel"]
  limits := [
    "ReferenceSlices refutes full readout factorization despite bilinearity and the reference-slice checks.",
    "RawSign separates normalized and raw naturality only; no separately checked kernel-equality result is recorded for that control.",
    "These controls do not establish physical products, tensor completion or exhaustion, monoidal coherence, Bell or actualization."] }

def operationalContextQuotient : ResearchTask := {
  id := "operational_context_quotient"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Generated contexts are finite one-hole compositions selecting either first or second output, with the hole in either input slot and all native reference preparations.",
    "ObservedData supplies universal observational square-swap and first-channel mediality relative to all tests in this grammar.",
    "Chosen zero and real readout with zero vacuum weight, global nonnegativity and conservation on all input pairs remain supplied."]
  conclusions := [
    "ObservationalEq is a congruence and the largest weight-preserving relation stable under both outputs in both input slots.",
    "Observed square-swap and mediality become exact laws on the quotient, yielding RawOperationalHilbert.Data and its Hilbert realization.",
    "For exact raw data, diagonal normalization preserves quadratic difference weight; each raw output in either input slot divides difference weight by two.",
    "A mathematical separating reference gives raw first-output weight equal to half the quadratic difference weight.",
    "Feature equality is exactly equality of all generated future-context tests, equivalently equality of first-output tests with every native reference.",
    "The quotient feature is injective, and the original feature image is dense."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/OperationalContextQuotient.lean"
      declarations := [
        "IDT.QMClosure.OperationalContextQuotient.Context",
        "IDT.QMClosure.OperationalContextQuotient.ObservationalEq",
        "IDT.QMClosure.OperationalContextQuotient.output_congr",
        "IDT.QMClosure.OperationalContextQuotient.relation_le_observationalEq",
        "IDT.QMClosure.OperationalContextQuotient.ObservedData.quotientData",
        "IDT.QMClosure.OperationalContextQuotient.ObservedData.feature_eq_iff_observationalEq",
        "IDT.QMClosure.OperationalContextQuotient.ObservedData.observationalEq_iff_single_tests",
        "IDT.QMClosure.OperationalContextQuotient.ObservedData.quotient_feature_injective",
        "IDT.QMClosure.OperationalContextQuotient.ObservedData.denseRange_feature"] },
    { sourcePath := "Proofs/QMClosure/RawOperationalSeparation.lean"
      declarations := [
        "IDT.QMClosure.RawOperationalSeparation.diagonal_distance",
        "IDT.QMClosure.RawOperationalSeparation.raw_first_left_distance",
        "IDT.QMClosure.RawOperationalSeparation.raw_first_right_distance",
        "IDT.QMClosure.RawOperationalSeparation.raw_second_left_distance",
        "IDT.QMClosure.RawOperationalSeparation.raw_second_right_distance",
        "IDT.QMClosure.RawOperationalSeparation.separating_reference",
        "IDT.QMClosure.RawOperationalSeparation.feature_eq_iff_raw_tests"] }]
  plannedArtifacts := []
  dependencies := ["raw_operational_hilbert_facade"]
  limits := [
    "All future tests means only the explicit generated one-hole grammar with all native references, not an arbitrary physical experiment.",
    "The universal observed laws are premises, not finite certification or an algorithm.",
    "Physical justification of the original laws and coverage of the reference/context family remain open.",
    "The separating reference is mathematical; no copying or manufacture of an unknown-input phase process is established.",
    "Density is not surjectivity and does not establish physically available completion states or processes."] }

def operationalContextControls : ResearchTask := {
  id := "operational_context_controls"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Explicit supplied complex-amplitude carrier with a Boolean NAND label and readout ignoring that label."]
  conclusions := [
    "An actual ObservedData instance satisfies the universal observed laws, nonnegativity, zero vacuum weight and conservation.",
    "Exact raw square-swap fails on labels (true,false), witnessed at the second output label.",
    "Exact raw first-channel mediality fails on labels (true,true,false,false).",
    "Preparations with amplitudes 1 and i have equal bare readout, but one legal first-output reference context distinguishes them with weights 1 and 0.",
    "Bare readout equality is neither observational equivalence nor a congruence for this control."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/OperationalContextControls.lean"
      declarations := [
        "IDT.QMClosure.OperationalContextControls.observedData",
        "IDT.QMClosure.OperationalContextControls.observed_square",
        "IDT.QMClosure.OperationalContextControls.observed_medial",
        "IDT.QMClosure.OperationalContextControls.exact_square_fails",
        "IDT.QMClosure.OperationalContextControls.exact_medial_fails",
        "IDT.QMClosure.OperationalContextControls.same_present_weight",
        "IDT.QMClosure.OperationalContextControls.referenceProbe_one",
        "IDT.QMClosure.OperationalContextControls.referenceProbe_I",
        "IDT.QMClosure.OperationalContextControls.same_weight_not_observational",
        "IDT.QMClosure.OperationalContextControls.bare_weight_equality_not_congruent"] }]
  plannedArtifacts := []
  dependencies := ["operational_context_quotient"]
  limits := [
    "No identification of this control's quotient with the complex plane is recorded.",
    "The supplied control is not a justification of physical primitive laws, physical reference availability or actualization."] }

def recordEffects : ResearchTask := {
  id := "record_effects_after_completion"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Native additive group with globally positive real quadratic Q and additive quarter-turn J preserving Q.",
    "A single branch is globally positive quadratic, invariant under the same J and dominated by Q.",
    "For a finite resolution, each q_r is globally positive quadratic, invariant under the same J, and sum_r q_r(x)=Q(x) for every x; domination then follows from the resolution."]
  conclusions := [
    "The residual Q-q is positive quadratic; the kernel and finite complex-coefficient synthesis squared norms decompose into branch and residual parts.",
    "A unique bounded contraction maps total features to branch features and has norm at most one.",
    "The branch effect is contraction-adjoint composed with contraction, has the branch kernel and diagonal readout, is positive, has norm at most one and is at most identity.",
    "Finite resolution implies branch domination, kernel summation and effects summing to identity: a mathematical finite POVM.",
    "Bounded-operator equality follows from all generating-feature matrix elements using dense complex span in both arguments."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/QuadraticReadoutEffects.lean"
      declarations := [
        "IDT.QMClosure.QuadraticReadoutEffects.Branch.residual_positive",
        "IDT.QMClosure.QuadraticReadoutEffects.Branch.synthesis_norm_sq",
        "IDT.QMClosure.QuadraticReadoutEffects.Branch.contraction_feature",
        "IDT.QMClosure.QuadraticReadoutEffects.Branch.contraction_norm_le",
        "IDT.QMClosure.QuadraticReadoutEffects.Branch.contraction_unique",
        "IDT.QMClosure.QuadraticReadoutEffects.Branch.effect_kernel",
        "IDT.QMClosure.QuadraticReadoutEffects.Branch.effect_diagonal",
        "IDT.QMClosure.QuadraticReadoutEffects.Branch.effect_positive",
        "IDT.QMClosure.QuadraticReadoutEffects.Branch.effect_norm_le",
        "IDT.QMClosure.QuadraticReadoutEffects.Branch.effect_le_one",
        "IDT.QMClosure.QuadraticReadoutEffects.Resolution.dominated",
        "IDT.QMClosure.QuadraticReadoutEffects.Resolution.kernel_sum",
        "IDT.QMClosure.QuadraticReadoutEffects.Resolution.sum_effect_eq_one",
        "IDT.QMClosure.QuadraticReadoutEffects.Resolution.finite_povm",
        "IDT.QMClosure.QuadraticReadoutEffects.operator_ext"] }]
  plannedArtifacts := []
  dependencies := ["canonical_hilbert_completion", "positive_quadratic_polarization"]
  limits := [
    "No native half, scalar action, topology, definiteness or finite-dimension premise is required.",
    "Dense-span matrix-element arguments do not use a diagonal-only shortcut.",
    "This constructs mathematical effects only; actualization, projectivity, state update, repeatability, physical instruments and physical availability of completed states remain open.",
    "Natural-channel adaptation is recorded separately as unfinished work."] }

def readoutEffectControls : ResearchTask := {
  id := "quadratic_readout_effect_controls"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Explicit mathematical coordinate controls on the supplied complex plane."]
  conclusions := [
    "Squared real and imaginary coordinates are positive quadratic dominated readouts resolving squared norm, but lack the required common phase invariance; the real-coordinate readout has no complex-linear expectation representation.",
    "Duplicated identity branches each satisfy the individual branch contract but fail total resolution; the duplicated effects do not sum to identity.",
    "Two half-identity effects satisfy the full positive, phase-invariant, bounded finite-resolution contract but are not projective."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/QuadraticReadoutEffectControls.lean"
      declarations := [
        "IDT.QMClosure.QuadraticReadoutEffectControls.coordinateBranch_positiveQuadratic",
        "IDT.QMClosure.QuadraticReadoutEffectControls.coordinateBranch_bounds",
        "IDT.QMClosure.QuadraticReadoutEffectControls.coordinateBranch_resolution",
        "IDT.QMClosure.QuadraticReadoutEffectControls.qRe_not_phase_invariant",
        "IDT.QMClosure.QuadraticReadoutEffectControls.qRe_has_no_complex_linear_effect",
        "IDT.QMClosure.QuadraticReadoutEffectControls.duplicatedBranch_individual_contract",
        "IDT.QMClosure.QuadraticReadoutEffectControls.duplicatedBranch_resolution_fails",
        "IDT.QMClosure.QuadraticReadoutEffectControls.duplicated_effects_finite_resolution_fails",
        "IDT.QMClosure.QuadraticReadoutEffectControls.resolved_nonprojective_control"] }]
  plannedArtifacts := []
  dependencies := ["record_effects_after_completion"]
  limits := [
    "These are supplied-coordinate mathematical models, not a canonical-space or raw-channel adapter.",
    "The controls do not supply actualization, physical instruments or state update."] }

def normalizedRecordEffects : ResearchTask := {
  id := "normalized_record_effects"
  stage := .inFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Raw source data and a finite dependent family of raw target data.",
    "Supplied exact normalized-channel Intertwines laws and universal sum of target weights W_r(L_r(x)) equal to source W(x).",
    "Raw quadratic forms, phases and halves are outputs of RawOperationalHilbert.Data; standalone branch positive-quadratic or phase-invariance premises are not supplied."]
  conclusions := [
    "Analytic target: finite resolution and positivity give observed branch vacuum W_r(L_r(0))=0 without strict L_r(0)=0.",
    "Analytic target: normalized naturality and raw reconstruction yield positive quadratic branch pullbacks invariant under the common source phase, packaged as QuadraticReadoutEffects.Resolution.",
    "Analytic target: natural affine target-feature channels extend to contractions after the null quotient."]
  checkedEvidence := []
  plannedArtifacts := [
    "UNCHECKED in-progress artifact: Proofs/QMClosure/NormalizedRecordEffects.lean."]
  dependencies := ["raw_operational_hilbert_facade", "mixer_record_naturality", "record_effects_after_completion"]
  limits := [
    "No checked normalized-record adapter is recorded yet.",
    "Channel naturality and universal resolution remain supplied bridge laws.",
    "No actualization, physical instrument, projectivity, state update or repeatability is established."] }

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
  rawMedialAddition, diagonalNormalization, canonicalHilbertCompletion,
  rawOperationalHilbertFacade, normalizedMixerGeneratedProcessWall,
  canonicalHilbertUniqueness, compositeProductKernel, compositeProductControls,
  operationalContextQuotient, operationalContextControls, recordEffects,
  readoutEffectControls, normalizedRecordEffects]

def ledger : List ResearchTask := researchTasks ++ globalBridges

end IDT.MetaLang.V8OperationalPrimitiveResearchLedger
