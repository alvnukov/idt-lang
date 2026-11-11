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
  plannedArtifacts := []
  dependencies := ["raw_medial_addition"]
  limits := [
    "The group and readout conclusions concern the normalized operation; original T is not asserted additive.",
    "The original diagonal need not fix the chosen zero.",
    "D and n are mathematical normal forms; the checked raw_doubled_normalization_compiler implements the normal form on supplied doubled preparations. Physical unary control on one unknown input and joint source availability remain open; copying an unknown state is not established."] }

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
    "Density is not surjectivity and does not establish physically available completion states or processes.",
    "The coherent_preparation_ray_interface bridge remains open; native coherent preparations are not identified with isolated physical rays."] }

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
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Raw source data and a finite dependent family of raw target data supply their complete raw operational laws and readout contracts.",
    "Family supplies only the channels, exact Intertwines laws for the reconstructed normalized mixers and universal total target-weight resolution of source weight.",
    "No raw algebraic typeclasses or standalone branch positive-quadratic, phase-invariance or domination premises are inputs."]
  conclusions := [
    "Finite resolution and positivity force observed branch vacuum W_r(L_r(0))=0 without strict L_r(0)=0.",
    "Affine normalized naturality and null translations give positive quadratic branch pullbacks invariant under the shared source phase.",
    "The family packages as QuadraticReadoutEffects.Resolution, with branch domination following from finite resolution.",
    "Effects on the source Hilbert output have expectations equal to the unnormalized target record weights, are positive, are at most identity and have norm at most one.",
    "The finite effects sum to identity and satisfy the mathematical finite POVM contract."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NormalizedRecordEffects.lean"
      declarations := [
        "IDT.QMClosure.NormalizedRecordEffects.Family",
        "IDT.QMClosure.NormalizedRecordEffects.Family.branch_vacuum",
        "IDT.QMClosure.NormalizedRecordEffects.Family.branch_quadratic",
        "IDT.QMClosure.NormalizedRecordEffects.Family.branch_phase_invariant",
        "IDT.QMClosure.NormalizedRecordEffects.Family.toResolution",
        "IDT.QMClosure.NormalizedRecordEffects.Family.branch_dominated",
        "IDT.QMClosure.NormalizedRecordEffects.Family.effect_expectation",
        "IDT.QMClosure.NormalizedRecordEffects.Family.effect_positive",
        "IDT.QMClosure.NormalizedRecordEffects.Family.effect_le_one",
        "IDT.QMClosure.NormalizedRecordEffects.Family.effect_norm_le",
        "IDT.QMClosure.NormalizedRecordEffects.Family.sum_effect_eq_one",
        "IDT.QMClosure.NormalizedRecordEffects.Family.finite_povm"] }]
  plannedArtifacts := []
  dependencies := ["raw_operational_hilbert_facade", "mixer_record_naturality", "record_effects_after_completion"]
  limits := [
    "Channel naturality and universal resolution remain supplied bridge laws.",
    "No actualization, physical instrument, projectivity, state update or repeatability is established.",
    "Physical availability of the coherent preparations and completed outputs remains open."] }

def coherentPortRayBoundary : ResearchTask := {
  id := "coherent_port_ray_boundary"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Explicit supplied complex-coordinate coherent mixer control.",
    "For normalized expectations, a supplied complex inner-product output and bounded complex-linear operator; positivity and completeness are not required.",
    "The bilinear comparison separately supplies a complex-bilinear map."]
  conclusions := [
    "Independent input phase classes do not preserve chosen port weights: the control gives weights 1 versus 0 and normalized ratios 1/2 versus 0.",
    "The mixer is covariant under simultaneous scalar multiplication, preserves nonzero pairs, and its normalized port ratio is invariant under common nonzero rescaling.",
    "Normalized complex-linear operator expectations are invariant under nonzero rescaling; genuine ray representatives remain nonzero.",
    "A supplied bilinear comparison is scalar covariant and inherits normalized-expectation invariance."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/CoherentPortRayBoundary.lean"
      declarations := [
        "IDT.QMClosure.CoherentPortRayBoundary.chosen_weight_one",
        "IDT.QMClosure.CoherentPortRayBoundary.chosen_weight_I",
        "IDT.QMClosure.CoherentPortRayBoundary.independent_phase_compatibility_fails",
        "IDT.QMClosure.CoherentPortRayBoundary.normalized_port_one",
        "IDT.QMClosure.CoherentPortRayBoundary.normalized_port_I",
        "IDT.QMClosure.CoherentPortRayBoundary.normalized_independent_phase_compatibility_fails",
        "IDT.QMClosure.CoherentPortRayBoundary.N_scalar",
        "IDT.QMClosure.CoherentPortRayBoundary.normalizedPortWeight_scalar",
        "IDT.QMClosure.CoherentPortRayBoundary.N_nonzero",
        "IDT.QMClosure.CoherentPortRayBoundary.normalizedExpectation_scalar",
        "IDT.QMClosure.CoherentPortRayBoundary.nonzero_rescaling",
        "IDT.QMClosure.CoherentPortRayBoundary.bilinear_left_scalar",
        "IDT.QMClosure.CoherentPortRayBoundary.bilinear_normalizedExpectation_scalar"] }]
  plannedArtifacts := []
  dependencies := ["operational_positive_readout", "record_effects_after_completion"]
  limits := [
    "No ray quotient construction, physical coherent lift, reference availability, separation by available effects or event-probability interpretation is established.",
    "The supplied bilinear comparison is not a tensor reconstruction.",
    "ProjectiveActionProof.ProjectiveFact denotes predicates, not a Hilbert-ray quotient; accepted predicate-action theorems are unchanged.",
    "A named frame, independent tensor ancilla or algebraic quarter-turn does not establish relative-phase preparation availability."] }

def scalarActualizationRefinement : ResearchTask := {
  id := "scalar_actualization_refinement"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A supplied shared scalar response F on all real weights in [0,1], with 0 <= F(t) <= 1, complement accounting F(1-t)=1-F(t), and balanced event-label refinement F(t/2)=F(t)/2 for every interval value.",
    "The finite-event adapter additionally supplies nonnegative branch weights with positive total, actual event probabilities p, and the assignment p(r)=F(q(r)/sum(q)).",
    "The restricted control supplies rational two-coordinate events in [0,1]^2, componentwise-compatible finite sums, rational attenuations and scalar events, preparation weight w_t(a,b)=a*t+b*(1-t), and alternative probability p(a,b)=(a+b)/2.",
    "The restricted disagreement and injectivity use one fixed irrational preparation t; the concrete bounded preparation is sqrt(2)/2."]
  conclusions := [
    "A bounded real error with complement antisymmetry and exact halving vanishes on [0,1]; consequently the supplied probability response F is identity without continuity, additivity, multiplicativity or measurability assumptions.",
    "Under its supplied assignment, the finite-event adapter gives p(r)=q(r)/sum(q); it does not generate event probabilities.",
    "The normalized squared response obeys probability bounds and complement accounting but violates balanced splitting; squaring and renormalizing records changes the coarse probability from 1/2 to 1/3 after the specified refinement.",
    "The restricted alternative assignment is positive, normalized, additive for every available finite compatible merge, and respects every rational refinement and rational scalar calibration.",
    "At fixed irrational t, w_t is injective, so the alternative assignment respects equality of weights at that preparation while disagreeing with w_t on the first port.",
    "Although forward rational refinements exist, this event image has no event of weight 2*t and no event of weight 2*(1-t); the two inverse-halving branches at the first port and its complement are absent."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ScalarActualizationRefinement.lean"
      declarations := [
        "IDT.QMClosure.ScalarActualizationRefinement.bounded_error_eq_zero",
        "IDT.QMClosure.ScalarActualizationRefinement.probability_response_eq_weight",
        "IDT.QMClosure.ScalarActualizationRefinement.supplied_finite_event_probability",
        "IDT.QMClosure.ScalarActualizationRefinement.squared_response_probability",
        "IDT.QMClosure.ScalarActualizationRefinement.squared_response_complement",
        "IDT.QMClosure.ScalarActualizationRefinement.squared_response_fails_balanced_split",
        "IDT.QMClosure.ScalarActualizationRefinement.squared_weight_refinement_counterexample"] },
    { sourcePath := "Proofs/QMClosure/RestrictedActualizationControls.lean"
      declarations := [
        "IDT.QMClosure.RestrictedActualizationControls.probability_bounds",
        "IDT.QMClosure.RestrictedActualizationControls.probability_accounting",
        "IDT.QMClosure.RestrictedActualizationControls.probability_finite_accounting",
        "IDT.QMClosure.RestrictedActualizationControls.complete_refinement_normalization",
        "IDT.QMClosure.RestrictedActualizationControls.probability_rational_refinement",
        "IDT.QMClosure.RestrictedActualizationControls.rational_scalar_calibration",
        "IDT.QMClosure.RestrictedActualizationControls.irrational_weight_injective",
        "IDT.QMClosure.RestrictedActualizationControls.fixed_preparation_weight_noncontextual",
        "IDT.QMClosure.RestrictedActualizationControls.alternative_disagrees",
        "IDT.QMClosure.RestrictedActualizationControls.no_event_weight_twice_preparation",
        "IDT.QMClosure.RestrictedActualizationControls.no_event_weight_twice_complement",
        "IDT.QMClosure.RestrictedActualizationControls.fixed_preparation_countermodel"] }]
  plannedArtifacts := []
  dependencies := ["record_effects_after_completion"]
  limits := [
    "The shared scalar response, actual event probabilities, event-label accounting laws and richness of available weights remain supplied bridges, not consequences of quadratic readout or reconstructed effects.",
    "The restricted fixed-preparation control is not a counterexample to one universal scalar response shared across preparations.",
    "The specific missing inverse branches do not show that every restricted domain fails or that the full real domain is necessary; suitable restricted domains with inverse-branch closure may still support rigidity.",
    "No physical event adapter, actual-event generator, general no-signalling result, Born-rule closure or full-QM closure is established."] }

def calibratedEffectActualization : ResearchTask := {
  id := "calibrated_effect_actualization"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A supplied complete complex Hilbert space H, with the full effect interval of bounded complex-linear operators 0 <= E <= I.",
    "A single context-independent EventLaw p on effects supplies p(I)=1, nonnegative probabilities and additivity for every positive operator pair whose sum is at most I; values outside the effect interval are unrestricted and unused.",
    "A supplied unit vector psi and its matched rank-one effect P_psi satisfy the supplied calibration p(P_psi)=1."]
  conclusions := [
    "Partial additivity and positivity derive monotonicity, probability bounds and complement accounting on effects.",
    "Real homogeneity p(tE)=t*p(E) for t in [0,1] follows from EventLaw rather than being assumed.",
    "An arbitrary-dimensional operator block bound and order squeeze give p(E) <= Re<psi,E psi>; applying the same bound to I-E gives equality for every effect.",
    "The conditional theorem uses no Gleason theorem, normality, continuity or supplied probability homogeneity."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/CalibratedEffectActualization.lean"
      declarations := [
        "IDT.QMClosure.CalibratedEffectActualization.EventLaw",
        "IDT.QMClosure.CalibratedEffectActualization.probability_mono",
        "IDT.QMClosure.CalibratedEffectActualization.probability_scale",
        "IDT.QMClosure.CalibratedEffectActualization.effect_block_bound",
        "IDT.QMClosure.CalibratedEffectActualization.probability_le_expectation",
        "IDT.QMClosure.CalibratedEffectActualization.calibrated_probability_eq_expectation"] }]
  plannedArtifacts := []
  dependencies := ["record_effects_after_completion", "coherent_port_ray_boundary", "scalar_actualization_refinement"]
  limits := [
    "The complete complex Hilbert space and full effect domain are supplied mathematical structures; physical availability of the effects is not established.",
    "Actual probability assignment, effect noncontextuality, partial additivity and matched-state calibration remain supplied event bridges.",
    "No actual-event generator, physical instrument, state update, Born-rule closure or full-QM closure is established."] }

def dyadicEffectDomainActualization : ResearchTask := {
  id := "dyadic_effect_domain_actualization"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A supplied subset D of effects on a complete complex Hilbert space contains I and the projector P of a supplied unit vector psi.",
    "DomainLaw supplies closure under complement, halving and every operator-admissible partial sum E+F <= I, including sums of effects from different contexts.",
    "A single context-independent probability assignment on D is nonnegative, normalized at I and additive on every such partial sum, with calibration p(P)=1."]
  conclusions := [
    "The domain laws imply order monotonicity, probability halving, iterated halving, bounded repeated sums, and dyadic scaling closure with probability homogeneity.",
    "Dyadic density and operator block comparisons, scaled by a sufficiently small power of one half, bound p(E) by every dyadic coefficient above Re<psi,E psi>.",
    "The resulting upper bound and complement accounting give p(E)=Re<psi,E psi> for every E in D.",
    "No all-real or all-rational scaling closure, supplied probability homogeneity, normality, continuity or dimension restriction is assumed."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/DyadicEffectDomainActualization.lean"
      declarations := [
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.effects",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.one_mem",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.complement_mem",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.half_mem",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.sum_mem",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.normalized",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.nonnegative",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.additive",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.probability_mono",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.probability_half",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.iterated_half",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.repeated_sum",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.dyadic_scale",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.exists_dyadic_between",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.probability_le_dyadic",
        "IDT.QMClosure.DyadicEffectDomainActualization.DomainLaw.calibrated_probability_eq_expectation"] }]
  plannedArtifacts := []
  dependencies := ["calibrated_effect_actualization"]
  limits := [
    "The domain, physical availability, closure under all cross-context operator-admissible partial sums, probability assignment and calibration remain supplied event bridges.",
    "The sum-closure and additive fields are distinct assumptions: neither same-context accounting nor mixing alone establishes availability of every positive-order comparison event.",
    "No actual-event generator, physical instrument, state update, Born-rule closure or full-QM closure is established."] }

def contextualActualizationControl : ResearchTask := {
  id := "contextual_actualization_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A supplied real symmetric two-by-two matrix representation SymmetricCoordinates has three tagged contexts i in {0,plus,minus} and events (i,a,b), for all real a,b in [0,1], embedded as b*I+(a-b)*P_i.",
    "The projectors are P_0=diag(1,0) and P_plus/minus=[[3/4,+/-sqrt(3)/4],[+/-sqrt(3)/4,1/4]]; supplied probabilities are p=a*c_i+b*(1-c_i), with c_0=1 and c_plus=c_minus=9/16."]
  conclusions := [
    "Every embedded event has positive-contraction quadratic bounds on all real vectors; the explicit complexExpectation expression is real and has the corresponding bounds on all complex vectors.",
    "Equality of embedded coordinate effects implies equality of probabilities, including distinct context tags, so the assignment descends to the supplied effect image.",
    "The assignment is bounded in [0,1], normalized, calibrated at P_0 and every real scalar effect, and respects complement and all real attenuations.",
    "Every finite coefficient-compatible same-context family has its embedded sum and additive probability.",
    "E_plus=P_plus/2 and E_minus=P_minus/2 have an admitted pair sum diag(3/4,1/4), but its probability 3/4 differs from the branch sum 9/16.",
    "Adding F=diag(1/4,3/4) gives I in coordinates, while the three assigned probabilities 9/32,9/32,1/4 sum to 13/16; cross-context accounting fails even when the pair sum and total are admitted."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ContextualActualizationControl.lean"
      declarations := [
        "IDT.QMClosure.ContextualActualizationControl.embedding_quadratic",
        "IDT.QMClosure.ContextualActualizationControl.embedding_positive_contraction",
        "IDT.QMClosure.ContextualActualizationControl.complexExpectation_real",
        "IDT.QMClosure.ContextualActualizationControl.complexExpectation_imaginary",
        "IDT.QMClosure.ContextualActualizationControl.embedding_complex_positive_contraction",
        "IDT.QMClosure.ContextualActualizationControl.probability_bounds",
        "IDT.QMClosure.ContextualActualizationControl.probability_of_embedding_eq",
        "IDT.QMClosure.ContextualActualizationControl.scalar_embedding",
        "IDT.QMClosure.ContextualActualizationControl.scalar_probability",
        "IDT.QMClosure.ContextualActualizationControl.normalized",
        "IDT.QMClosure.ContextualActualizationControl.complement_embedding",
        "IDT.QMClosure.ContextualActualizationControl.complement_probability",
        "IDT.QMClosure.ContextualActualizationControl.attenuation_embedding",
        "IDT.QMClosure.ContextualActualizationControl.attenuation_probability",
        "IDT.QMClosure.ContextualActualizationControl.halves",
        "IDT.QMClosure.ContextualActualizationControl.finite_same_context_embedding",
        "IDT.QMClosure.ContextualActualizationControl.finite_same_context_probability",
        "IDT.QMClosure.ContextualActualizationControl.preparation_certain",
        "IDT.QMClosure.ContextualActualizationControl.cross_context_pair_is_admitted",
        "IDT.QMClosure.ContextualActualizationControl.cross_context_pair_failure",
        "IDT.QMClosure.ContextualActualizationControl.cross_context_sum_identity",
        "IDT.QMClosure.ContextualActualizationControl.cross_context_normalization_failure"] }]
  plannedArtifacts := []
  dependencies := ["dyadic_effect_domain_actualization"]
  limits := [
    "This is a supplied symmetric-coordinate effect model with explicit real and complex quadratic verification, not a reconstructed carrier or continuous-operator Effect adapter.",
    "The assignment is operator/effect-noncontextual, not fixed-preparation numerical-weight-noncontextual. With rich scalar calibration, that additional numerical-weight noncontextuality would force the vector expectation.",
    "The result isolates missing cross-context joint accounting rather than absence of the displayed sum effects; it concerns only the supplied three-context image.",
    "No general contextuality classification, no-signalling result, physical event adapter, actual-event generator or full-QM closure is established."] }

def generatedEventConeControl : ResearchTask := {
  id := "generated_event_cone_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A supplied real symmetric two-by-two matrix coordinate model uses P_0=diag(1,0), P_plus/minus=[[3/4,+/-sqrt(3)/4],[+/-sqrt(3)/4,1/4]], and Q_i=I-P_i.",
    "C is the finite nonnegative real conic span of the six P_i,Q_i, with no topological closure or positive-semidefinite saturation; D={E in C | I-E in C}.",
    "A new coordinate-linear law L(E)=E00+E01/sqrt(3) is supplied; it is distinct from the three-context control's probability constants 1,9/16,9/16."]
  conclusions := [
    "L takes values 1,0 on P_0,Q_0; 1,0 on P_plus,Q_plus; and 1/2,1/2 on P_minus,Q_minus. It is nonnegative on C, normalized at I and bounded in [0,1] on D.",
    "Every supplied finite normalized cone-valued family has outcomes in D and total assigned value one; global coordinate linearity gives additivity for all admitted sums, real attenuation accounting and finite arbitrary-real convex mixing.",
    "Every admitted coordinate effect has positive-contraction quadratic bounds on all real and complex vectors; L respects coordinate equality.",
    "Calibration L(P_0)=1 holds, but L(P_plus)=1 differs from the first-basis-vector expectation 3/4.",
    "A=I/16 and B=(P_0+P_plus)/2 lie in D. S=A+B is in C and has positive-contraction bounds on every real and complex vector, but T=I-S is outside C and S is outside D.",
    "The exact witness has T's quadratic form ((x-2*sqrt(3)*y)^2+y^2)/16 >= 0, L(T)=-1/16 and L(S)=17/16. The latter is a value on an excluded mathematical sum, never an admitted outcome probability.",
    "Thus complete accounting on this admitted cone interval, even with real mixing, does not imply saturation under every positive-semidefinite operator-admissible sum."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/GeneratedEventConeControl.lean"
      declarations := [
        "IDT.QMClosure.GeneratedEventConeControl.L_add",
        "IDT.QMClosure.GeneratedEventConeControl.L_scale",
        "IDT.QMClosure.GeneratedEventConeControl.L_identity",
        "IDT.QMClosure.GeneratedEventConeControl.L_complement",
        "IDT.QMClosure.GeneratedEventConeControl.L_projector",
        "IDT.QMClosure.GeneratedEventConeControl.cone_L_nonnegative",
        "IDT.QMClosure.GeneratedEventConeControl.context_event_inDomain",
        "IDT.QMClosure.GeneratedEventConeControl.domain_bounds",
        "IDT.QMClosure.GeneratedEventConeControl.domain_positive_contraction",
        "IDT.QMClosure.GeneratedEventConeControl.domain_complex_positive_contraction",
        "IDT.QMClosure.GeneratedEventConeControl.domain_attenuation",
        "IDT.QMClosure.GeneratedEventConeControl.L_sum",
        "IDT.QMClosure.GeneratedEventConeControl.domain_convex_mixture",
        "IDT.QMClosure.GeneratedEventConeControl.normalized_family_inDomain",
        "IDT.QMClosure.GeneratedEventConeControl.normalized_family_accounting",
        "IDT.QMClosure.GeneratedEventConeControl.effect_noncontextual",
        "IDT.QMClosure.GeneratedEventConeControl.admitted_sum_additive",
        "IDT.QMClosure.GeneratedEventConeControl.calibration",
        "IDT.QMClosure.GeneratedEventConeControl.disagreement_with_first_basis_vector_expectation",
        "IDT.QMClosure.GeneratedEventConeControl.A_inDomain",
        "IDT.QMClosure.GeneratedEventConeControl.B_inDomain",
        "IDT.QMClosure.GeneratedEventConeControl.T_quadratic",
        "IDT.QMClosure.GeneratedEventConeControl.S_positive_contraction",
        "IDT.QMClosure.GeneratedEventConeControl.S_complex_positive_contraction",
        "IDT.QMClosure.GeneratedEventConeControl.L_S",
        "IDT.QMClosure.GeneratedEventConeControl.L_T",
        "IDT.QMClosure.GeneratedEventConeControl.T_not_inCone",
        "IDT.QMClosure.GeneratedEventConeControl.S_not_inDomain",
        "IDT.QMClosure.GeneratedEventConeControl.absent_sum_control"] }]
  plannedArtifacts := []
  dependencies := ["contextual_actualization_control", "dyadic_effect_domain_actualization"]
  limits := [
    "All normalized C-event families constitute a supplied larger domain; original randomized test histories sit inside it, but realizability of every such family from randomized original tests is not asserted.",
    "L is effect/operator-noncontextual and globally coordinate-additive, but not fixed-preparation numerical-weight-noncontextual or a non-Born state on the full quantum effect interval.",
    "Existing-sum accounting and real mixing do not establish physical availability or positive-order saturation; the witness shows failure of the closure required by DomainLaw.sum_mem.",
    "The coordinate model has no continuous-operator Effect adapter or physical event generator.",
    "No general no-signalling result, physical instrument, Born-rule closure or full-QM closure is established."] }

def conditionalRecordProbabilities : ResearchTask := {
  id := "conditional_record_probabilities"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Raw source Data V and dependent raw targets supply a finite NormalizedRecordEffects.Family f, including full-carrier normalized mixer naturality and total target-weight resolution.",
    "A supplied raw preparation x has source.weight(x)>0; normalizedFeature is inverse-norm complex scalar multiplication of source.feature(x) in the reconstructed source.Hilbert, with no independent Hilbert-space input.",
    "Supply DyadicEffectDomainActualization.DomainLaw D p on this reconstructed Hilbert space, membership of the matched projector of normalizedFeature in D, calibration of that projector to one, and membership of every f.effect(r) in D."]
  conclusions := [
    "Positive source weight makes normalizedFeature a mathematical unit vector; the unnormalized Family.effect_expectation identity and norm_feature_sq give its normalized expectation as target_r.weight(f.channel(r,x))/source.weight(x).",
    "The accepted conditional dyadic theorem therefore gives p(f.effect(r))=target_r.weight(f.channel(r,x))/source.weight(x) for every record r.",
    "The finite record probabilities lie in [0,1] and sum to one; the combined theorem packages the ratio formula, finite normalization and probability bounds.",
    "The individual bounds require only the supplied domain law and branch membership; positive source weight and matched calibration are additionally used for the ratio and normalized total."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ConditionalRecordProbabilities.lean"
      declarations := [
        "IDT.QMClosure.ConditionalRecordProbabilities.normalizedFeature_unit",
        "IDT.QMClosure.ConditionalRecordProbabilities.normalized_effect_expectation",
        "IDT.QMClosure.ConditionalRecordProbabilities.record_probability",
        "IDT.QMClosure.ConditionalRecordProbabilities.record_probabilities_sum",
        "IDT.QMClosure.ConditionalRecordProbabilities.record_probability_bounds",
        "IDT.QMClosure.ConditionalRecordProbabilities.conditional_record_probabilities"] }]
  plannedArtifacts := []
  dependencies := ["raw_operational_hilbert_facade", "normalized_record_effects", "dyadic_effect_domain_actualization"]
  limits := [
    "The domain, effect membership, all DomainLaw closure/accounting laws and matched-state calibration remain supplied event bridges.",
    "Mathematical feature normalization supplies no native normalization operation or physically available preparation, and does not establish physical effect or event availability.",
    "No actual outcome generator, physical instrument, state update, original-IDT bridge, Born-rule closure or full-QM closure is established."] }

def nativeMixerEventConeExclusion : ResearchTask := {
  id := "native_mixer_event_cone_exclusion"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the supplied scalar-wire encoding of CompositeProductControls.RawSign.N, with pair coefficients a=(1+i)/2 and b=(1-i)/2, in the MixerGeneratedProcessWall Circuit grammar of identity, pair mixer, permutation and sequential composition.",
    "Two scalar source wires and one supplied vacuum wire are embedded in three wires; the selected output port is zero.",
    "The extension obstruction supplies one coordinate assignment p with nonnegative p(F), old values p(P_0)=1 and p(Q_plus)=p(Q_0)=0, and the two explicit arbitrary-real mixture accounting equations for leftMixture and rightMixture. Their displayed zero-padding contributions are zero."]
  conclusions := [
    "On input (z,w,0), chronological words (01,02,01) and (01,12,02) give selected amplitudes -(1+i)*z/4+(3+i)*w/4 and -(1-i)*z/4+(3-i)*w/4.",
    "Every native circuit conserves total input weight; the half-mixture of these circuits also conserves total weight, and its selected-port weight equals the complex quadratic expression of F=(1/8,5/8,-1/4) for every complex pair.",
    "F is a positive contraction on all complex vectors, but L(F)=1/8-1/(4*sqrt(3))<0, so F lies outside the old cone and its domain; no imaginary-coordinate response is chosen.",
    "Positive epsilon=1/(4*sqrt(3))-1/8, r=1/sqrt(3), and s=5/8-3/(4*sqrt(3)) satisfy F+epsilon*P_0=r*Q_plus+s*Q_0. Half scaling and zero padding give two valid convex-mixture presentations of the same coordinate effect.",
    "The supplied assignment cannot obey both displayed real-mixture accounting laws while retaining the old three event values and nonnegative p(F). This is a checked finite extension obstruction, not a universal actualization theorem."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeMixerEventConeExclusion.lean"
      declarations := [
        "IDT.QMClosure.NativeMixerEventConeExclusion.cPlus_selected",
        "IDT.QMClosure.NativeMixerEventConeExclusion.cMinus_selected",
        "IDT.QMClosure.NativeMixerEventConeExclusion.native_total_weight",
        "IDT.QMClosure.NativeMixerEventConeExclusion.compressed_total_weight",
        "IDT.QMClosure.NativeMixerEventConeExclusion.native_selected_weight",
        "IDT.QMClosure.NativeMixerEventConeExclusion.F_complex_positive_contraction",
        "IDT.QMClosure.NativeMixerEventConeExclusion.L_F",
        "IDT.QMClosure.NativeMixerEventConeExclusion.L_F_negative",
        "IDT.QMClosure.NativeMixerEventConeExclusion.F_not_inCone",
        "IDT.QMClosure.NativeMixerEventConeExclusion.F_not_inDomain",
        "IDT.QMClosure.NativeMixerEventConeExclusion.old_event_probabilities",
        "IDT.QMClosure.NativeMixerEventConeExclusion.coefficient_bounds",
        "IDT.QMClosure.NativeMixerEventConeExclusion.extension_operator_identity",
        "IDT.QMClosure.NativeMixerEventConeExclusion.mixture_operator_identity",
        "IDT.QMClosure.NativeMixerEventConeExclusion.mixture_weights_valid",
        "IDT.QMClosure.NativeMixerEventConeExclusion.left_zero_padding",
        "IDT.QMClosure.NativeMixerEventConeExclusion.right_zero_padding",
        "IDT.QMClosure.NativeMixerEventConeExclusion.no_nonnegative_extension"] }]
  plannedArtifacts := []
  dependencies := ["normalized_mixer_generated_process_wall", "generated_event_cone_control"]
  limits := [
    "Scalar-wire encoding, vacuum, selected-port event interpretation and the two arbitrary-real mixture accounting laws remain supplied assumptions, not consequences of bare conserved weight or dyadic circuit mixing.",
    "The coordinate assignment supplies effect noncontextuality; the obstruction does not assume or establish a global linear probability law.",
    "The result is a finite countermodel exclusion, not a Born-rule theorem, full-QM closure, physical actual-event generator, universal availability claim or continuous-operator Effect adapter."] }

def nativeMixerGroupPortGeometry : ResearchTask := {
  id := "native_mixer_group_port_geometry"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Use the supplied complex scalar-wire mixer with all pair gates, or connected routing that makes those pair placements available, together with permutations and circuit composition at fixed finite width N.",
    "The independently reviewed analytic route uses standard compact Lie group and topological closure results not yet formalized here.",
    "Vacuum compression and port readout are separate supplied mathematical operations; physical encoding and ancillary availability are not established."]
  conclusions := [
    "Independently reviewed analytic result awaiting formalization: for N>=3 the topological closure G_N consists of unitary U fixing the uniform vector and having determinant in mu4={1,i,-1,-i}; widths two and one give a four-element group and a trivial group respectively.",
    "Analytic route: a three-wire K=A*B^-1 has determinant one and trace 1/2 on the uniform-orthogonal complement, giving an infinite-order circle; J=A*K*A^-1 has the additive matrix commutator witness (K*J-J*K)_(0,0)=i/4.",
    "Analytic route: the two Lie circles generate SU(2), embedded triples generate su(N-1), and the determinant supplies four components. This route is not a checked Lean proof.",
    "Analytic boundary: fixed-width port projectors cannot distinguish the uniform-vector projector from I/N.",
    "Analytic compression result: two vacuum ancillas give finite compressed port effects approaching c*P_psi for all rays at c=1/(16*n), with strengths allowed to vary along the sequence. Unbounded ancillary width can make the limiting strength approach one."]
  checkedEvidence := []
  plannedArtifacts := [
    "Independently reviewed analytic route; no current Lean proof artifact is assigned."]
  dependencies := ["normalized_mixer_generated_process_wall", "generated_event_cone_control",
    "native_mixer_infinite_order", "vacuum_port_effect_completion"]
  limits := [
    "Topological closure is not exact finite-word reachability. An exact fixed-strength finite slice can be empty: at n=3, c=1/48 is not dyadic, so approximation may require varying strengths.",
    "A one-ancilla vector-completion argument alone does not establish two-wire circuit reachability.",
    "Physical scalar encoding, vacuum ancillas, selected-port realization and probability calibration remain open bridges.",
    "Passing a probability assignment to limits requires a separately justified condition; it is not inferred from circuit approximation.",
    "No exact matched-state projector test, universal physical availability, Born-rule closure, actual-event generation or full-QM closure is established."] }

def dyadicMixtureLinearization : ResearchTask := {
  id := "dyadic_mixture_linearization"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A supplied rational vector space V has an event domain D containing zero; a single real-valued assignment p has p(0)=0.",
    "D is closed under midpoints, p((x+y)/2)=(p(x)+p(y))/2 for all x,y in D, and the full rational linear span of D is V.",
    "The optional continuous real extension additionally uses the supplied finite rational coordinate space Fin d -> Q, with coordinatewise inclusion into Fin d -> R; dimension zero is allowed."]
  conclusions := [
    "There is a unique rational-linear functional on V agreeing with p on D, with no finite-dimensional assumption on the generic theorem.",
    "The proof uses dyadic graph mixtures and integer saturation to clear rational denominators; no boundedness, positivity, arbitrary-mixture accounting or continuity is assumed.",
    "For finite rational coordinates, ell(q)=sum_i ell(e_i)*q_i. A finite sum of continuous real coordinate projections constructs the unique continuous real-linear extension with the same coefficients.",
    "The finite-coordinate existence/uniqueness theorem agrees with p at cast points of D; the extension agrees with ell at every rational coordinate point."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/DyadicMixtureLinearization.lean"
      declarations := [
        "IDT.QMClosure.DyadicMixtureLinearization.exists_unique_rational_linear_extension",
        "IDT.QMClosure.DyadicMixtureLinearization.rational_linear_coordinate_formula",
        "IDT.QMClosure.DyadicMixtureLinearization.continuousRealExtension_apply",
        "IDT.QMClosure.DyadicMixtureLinearization.continuousRealExtension_agrees",
        "IDT.QMClosure.DyadicMixtureLinearization.continuousRealExtension_unique",
        "IDT.QMClosure.DyadicMixtureLinearization.exists_unique_continuous_real_extension"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "The domain, its spanning property and midpoint probability accounting remain supplied; no native event-domain generation follows.",
    "The generic rational-linear theorem does not assert real linearity or continuity on an arbitrary real ambient space.",
    "The finite-coordinate corollary supplies a mathematical extension, not automatic agreement with a separate probability assignment on irrational events outside cast(D).",
    "No positivity theorem, density-matrix representation, physical availability, probability actualization or full-QM closure is asserted."] }

def vacuumPortEffectCompletion : ResearchTask := {
  id := "vacuum_port_effect_completion"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A supplied finite complex vector psi on Fin n has coordinateWeight(psi)=1; c is a supplied nonnegative real scalar.",
    "The general completion theorem assumes the sufficient budget normSq(1-sqrt(c)*sum(psi)) <= 2*(1-c). The uniform-strength theorem additionally assumes n>=1.",
    "The input embedding adds two zero coordinates; no group-density, circuit-realizability, physical-port or probability-law premise is supplied."]
  conclusions := [
    "Writing d=1-sqrt(c)*sum(psi), explicit ancillary entries d/2+t and d/2-t, for real t=sqrt((1-c-normSq(d)/2)/2), sum to d and have total squared weight 1-c under the budget.",
    "The completed vector with data entries sqrt(c)*psi has coordinate sum one and total squared weight one.",
    "Compression against every complex input x, without an input-normalization assumption, gives squared overlap c*|sum(conj(psi)*x)|^2.",
    "The coordinate Cauchy-Schwarz bound proves that the uniform positive strength c=1/(16*n) satisfies the sufficient budget for every unit psi when n>=1."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/VacuumPortEffectCompletion.lean"
      declarations := [
        "IDT.QMClosure.VacuumPortEffectCompletion.completionAncilla_sum",
        "IDT.QMClosure.VacuumPortEffectCompletion.completionAncilla_weight",
        "IDT.QMClosure.VacuumPortEffectCompletion.completedVector_sum",
        "IDT.QMClosure.VacuumPortEffectCompletion.completedVector_weight",
        "IDT.QMClosure.VacuumPortEffectCompletion.completedVector_overlap_weight",
        "IDT.QMClosure.VacuumPortEffectCompletion.exists_two_coordinate_completion",
        "IDT.QMClosure.VacuumPortEffectCompletion.normSq_sum_le_dimension",
        "IDT.QMClosure.VacuumPortEffectCompletion.uniformStrength_budget",
        "IDT.QMClosure.VacuumPortEffectCompletion.uniform_two_coordinate_completion"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "This is supplied-coordinate mathematical geometry only. The budget is a sufficient criterion; no converse or characterization of all completions is asserted.",
    "A completed vector is not a finite native circuit. Group density, exact circuit realization and physical ancillary or port availability do not follow from this result.",
    "The zero-coordinate input embedding has no asserted physical vacuum interpretation or probability law.",
    "No actual outcome generator, physical calibration, Born-rule closure or full-QM closure is established."] }

def nativeMixerInfiniteOrder : ResearchTask := {
  id := "native_mixer_infinite_order"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the existing supplied complex scalar mixer in the native circuit grammar on three wires; A and B are its explicit pair-gate matrices for wires 01 and 12.",
    "The fixed chronological native word is (12,12,12,01), with matrix K=A*B^3. The universal nonidentity theorem assumes only a positive natural exponent."]
  conclusions := [
    "The pair-gate action and the action of the exact existing native circuit word equal their explicit matrix actions, so the result is linked to the circuit grammar.",
    "The zero-sum plane embedding W(x,y)=(x,y,-x-y) has an explicit left inverse and satisfies K*W=W*M for the explicit two-coordinate matrix M.",
    "C=2*M satisfies C^2=C-4*I. Its power traces equal the integer sequence s_0=2, s_1=1, s_(n+2)=s_(n+1)-4*s_n, which is odd at every positive index.",
    "M^n=I would force the odd trace to equal the even integer 2^(n+1); the intertwining and left inverse give K^n!=I for every positive n.",
    "This is a universal exact algebraic theorem about the matrix of one fixed native word; it uses no eigenvalue, algebraic-integer, unitarity or topological hypothesis for the obstruction."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeMixerInfiniteOrder.lean"
      declarations := [
        "IDT.QMClosure.NativeMixerInfiniteOrder.gate01_action",
        "IDT.QMClosure.NativeMixerInfiniteOrder.gate12_action",
        "IDT.QMClosure.NativeMixerInfiniteOrder.native_word_action",
        "IDT.QMClosure.NativeMixerInfiniteOrder.left_inverse",
        "IDT.QMClosure.NativeMixerInfiniteOrder.intertwines",
        "IDT.QMClosure.NativeMixerInfiniteOrder.C_eq_two_smul",
        "IDT.QMClosure.NativeMixerInfiniteOrder.C_quadratic",
        "IDT.QMClosure.NativeMixerInfiniteOrder.traceSequence_odd",
        "IDT.QMClosure.NativeMixerInfiniteOrder.C_pow_recurrence",
        "IDT.QMClosure.NativeMixerInfiniteOrder.trace_C_pow",
        "IDT.QMClosure.NativeMixerInfiniteOrder.C_pow_scale",
        "IDT.QMClosure.NativeMixerInfiniteOrder.M_pow_ne_one",
        "IDT.QMClosure.NativeMixerInfiniteOrder.K_pow_intertwines",
        "IDT.QMClosure.NativeMixerInfiniteOrder.native_word_infinite_order"] }]
  plannedArtifacts := []
  dependencies := ["normalized_mixer_generated_process_wall"]
  limits := [
    "The matrix action link is checked for the stated coordinate circuit, not a physical-wire encoding bridge.",
    "Infinite order alone does not formalize a circle subgroup, full Lie-group closure, density, circuit universality, physical continuity or probability interpretation.",
    "The group-classification route remains analytic and unchecked despite this separate checked ingredient.",
    "No physical availability, actual-event generator, Born-rule closure or full-QM closure is established."] }

def nativeWireEffectSpan : ResearchTask := {
  id := "native_wire_effect_span"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A supplied rational coordinate space for n-wire Hermitian effects uses n diagonal coordinates and real and imaginary off-diagonal coordinates for i<j; complex scalar wires and the existing native mixer remain supplied.",
    "Each pair experiment uses Fin n plus one fresh zero-input vacuum coordinate; selected-port events and classical half mixing remain supplied availability and accounting assumptions.",
    "The event coordinates are P_i, the single pair-mixer effect H_ij with diagonal entries 1/2,1/2 and imaginary off-diagonal entry -1/2, and the half mixture F_ij of two three-gate words with diagonal entries 1/8,5/8 and real off-diagonal entry -1/4.",
    "The unique-readout theorem assumes a domain D containing zero and every P_i, H_ij and F_ij, closure of D under rational half sums, one coordinate-noncontextual readout p with p(0)=0, and midpoint accounting on every pair in D."]
  conclusions := [
    "For every n, pair i<j and complex input, the generic native adapters give exactly the H_ij selected-port weight and the F_ij half-mixture weight. Every native circuit preserves total squared-norm readout on the supplied zero-input extension.",
    "Signed rational recovery Y_ij=P_i+P_j-2*H_ij and X_ij=(1/2)*P_i+(5/2)*P_j-4*F_ij recovers every coordinate basis vector; membership of the displayed events in D implies its rational span is the whole coordinate space.",
    "Under the supplied zero, midpoint and membership laws, there exists a unique rational-linear functional on the whole coordinate space agreeing with p on D. No Lie-group density premise is used.",
    "At n=2 the explicit rational-linear control has values 1,0 on P_0,P_1, 1/2 on H_01 and 1/16 on F_01. Each of these four events and its identity complement has control value in [0,1]; every nonnegative finite rational combination of these eight supplied events has nonnegative value.",
    "The explicit N=(1/128)*P_0+(64/128)*P_1-(8/128)*X_01 is a positive contraction for every complex input, yet its control readout equals -1/128. Thus this finite calibration and cone positivity do not establish positivity on the full positive-effect interval."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeWireEffectSpan.lean"
      declarations := [
        "IDT.QMClosure.NativeWireEffectSpan.recover_Y",
        "IDT.QMClosure.NativeWireEffectSpan.recover_X",
        "IDT.QMClosure.NativeWireEffectSpan.native_span_eq_top",
        "IDT.QMClosure.NativeWireEffectSpan.native_H_weight",
        "IDT.QMClosure.NativeWireEffectSpan.native_F_weight",
        "IDT.QMClosure.NativeWireEffectSpan.all_port_resolution",
        "IDT.QMClosure.NativeWireEffectSpan.unique_rational_readout",
        "IDT.QMClosure.NativeWireEffectSpan.control_values",
        "IDT.QMClosure.NativeWireEffectSpan.control_calibration",
        "IDT.QMClosure.NativeWireEffectSpan.control_nonnegative_combinations",
        "IDT.QMClosure.NativeWireEffectSpan.negativeControl_positive_contraction",
        "IDT.QMClosure.NativeWireEffectSpan.control_negative"] }]
  plannedArtifacts := []
  dependencies := ["normalized_mixer_generated_process_wall", "native_mixer_event_cone_exclusion", "dyadic_mixture_linearization"]
  limits := [
    "Each pair test is a separate experiment with a fresh vacuum coordinate; no simultaneous measurement of the spanning family, basis independence or coordinate cardinality theorem is asserted.",
    "Signed rational basis recovery is mathematical linear algebra, not physical subtraction or availability of every positive effect.",
    "The control is nonnegative only on nonnegative finite rational combinations of the eight displayed generator/complement events; no positivity theorem for all native circuit words is asserted.",
    "A unique rational-linear readout and the displayed finite calibration do not establish a globally positive state, positive-semidefinite density matrix or physical probability law.",
    "No full positive-domain closure, physical event availability, actual outcome generator, Born-rule closure or full-QM closure is established."] }

def nativeAttenuationCalibratedSelection : ResearchTask := {
  id := "native_attenuation_calibrated_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Selection uses the supplied rational Coord(n+1) space with distinguished wire 0 and one coordinate-noncontextual domain readout p, zero in D with p(0)=0, midpoint closure/accounting on D, and every P_i in D.",
    "The identity coordinate I=sum_i P_i lies in D with p(I)=1, p is nonnegative on D, and matched basis calibration supplies p(P_0)=1.",
    "For every upper pair i<j and every natural m, D contains each of E_0,E_2,E_4,E_6 below. Separate H_ij or F_ij availability is unnecessary.",
    "The circuit adapter uses the existing supplied complex mixer on Fin n plus Fin k, with every ancillary input zero and all ancillary outputs retained. Physical availability of separate finite tests at arbitrarily large fresh-wire widths remains supplied."]
  conclusions := [
    "For t=(1/16)^m, the rational families are E_0=(t^2/2)*P_i+(1/2)*P_j+(t/2)*Y_ij, E_2=(t^2/8)*P_i+(1/2)*P_j+(t/4)*X_ij, E_4=(t^2/32)*P_i+(1/2)*P_j-(t/8)*Y_ij, and E_6=(t^2/128)*P_i+(1/2)*P_j-(t/16)*X_ij.",
    "At m=0, Y_ij=2*E_0-P_i-P_j and X_ij=4*E_2-(1/2)*P_i-2*P_j. Thus P_i,E_0(0),E_2(0) supply full rational span; zero and midpoint laws give a unique rational-linear extension agreeing with p on D.",
    "For a rational-linear ell with ell(P_j)=0, nonnegativity on all four families for every m forces ell(X_ij)=ell(Y_ij)=0 by scalar geometric convergence. Normalization, nonnegative diagonals and ell(P_0)=1 then give ell(v)=v_00 for every rational coordinate v on Fin(n+1).",
    "The domain theorem concludes p(v)=v_00 for every v in D under the stated membership, positivity, midpoint and calibration hypotheses.",
    "Literal finite circuit words attenuate wire i using k fresh ancillary wires and then mix i,j selecting j, with selected amplitude b*a^k*x_i+a*x_j, a=(1+i)/2 and b=(1-i)/2. The complete prefix state retains ancillary leakage b*a^l*x_i on wire l, and all-port squared-norm readout is conserved.",
    "For every complex input and natural m, the four E_r quadratic forms equal exact selected-port squared norms at the finite attenuation lengths 8m+r for r=0,2,4,6.",
    "For every finite cutoff M, the explicit rational-linear counter-readout has values 1,0 on P_0,P_1, identity value 1, Y value 0 and strictly positive X value t_M/16. All four family values lie in [0,1] for m<=M, yet its E_6(M+1) value is exactly -7*t_M^2/32768<0."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAttenuationReadout.lean"
      declarations := [
        "IDT.QMClosure.NativeAttenuationReadout.recover_Y",
        "IDT.QMClosure.NativeAttenuationReadout.recover_X",
        "IDT.QMClosure.NativeAttenuationReadout.native_attenuation_span_eq_top",
        "IDT.QMClosure.NativeAttenuationReadout.t_tendsto_zero",
        "IDT.QMClosure.NativeAttenuationReadout.pair_vanish",
        "IDT.QMClosure.NativeAttenuationReadout.basis_calibrated_selection",
        "IDT.QMClosure.NativeAttenuationReadout.domain_basis_calibrated_selection"] },
    { sourcePath := "Proofs/QMClosure/NativeAttenuationCircuit.lean"
      declarations := [
        "IDT.QMClosure.NativeAttenuationCircuit.prefix_eval",
        "IDT.QMClosure.NativeAttenuationCircuit.prefix_leak",
        "IDT.QMClosure.NativeAttenuationCircuit.selected_action",
        "IDT.QMClosure.NativeAttenuationCircuit.all_port_resolution",
        "IDT.QMClosure.NativeAttenuationCircuit.selected_E0",
        "IDT.QMClosure.NativeAttenuationCircuit.selected_E2",
        "IDT.QMClosure.NativeAttenuationCircuit.selected_E4",
        "IDT.QMClosure.NativeAttenuationCircuit.selected_E6"] },
    { sourcePath := "Proofs/QMClosure/NativeAttenuationCutoffControl.lean"
      declarations := [
        "IDT.QMClosure.NativeAttenuationCutoffControl.calibration",
        "IDT.QMClosure.NativeAttenuationCutoffControl.cross_coordinate_positive",
        "IDT.QMClosure.NativeAttenuationCutoffControl.readout_Y",
        "IDT.QMClosure.NativeAttenuationCutoffControl.cutoff_bounds",
        "IDT.QMClosure.NativeAttenuationCutoffControl.next_depth_value",
        "IDT.QMClosure.NativeAttenuationCutoffControl.finite_cutoff_countermodel"] }]
  plannedArtifacts := []
  dependencies := ["native_wire_effect_span", "dyadic_mixture_linearization", "normalized_mixer_generated_process_wall"]
  limits := [
    "The all-depth positivity premise quantifies over every natural m. The universal finite-cutoff countermodel shows why finitely many depth checks cannot replace it.",
    "The finite circuit syntax keeps every ancillary output; it uses no discard, reset, postselection or infinite physical circuit. Physical availability of arbitrarily many fresh wires across separate tests remains a bridge.",
    "Only scalar geometric convergence is used for selection, with no continuity premise for p or ell, arbitrary real mixing, Lie-group classification or circuit-density premise.",
    "Selection identifies the mathematical pure coordinate extension at distinguished basis wire 0, not arbitrary vector preparations or a general mixed-state positive-semidefinite representation. The domain theorem asserts agreement of p only on D.",
    "Physical native-event availability, coordinate noncontextuality, midpoint event/accounting laws and matched calibration remain supplied premises.",
    "No physical actual-event generator, Born-rule closure or full-QM closure is established."] }

def nativeContextualProbabilityControl : ResearchTask := {
  id := "native_contextual_probability_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Keep the existing supplied complex native mixer and literal circuit grammar unchanged, including conserved structural squared-norm weights.",
    "For a finite normalized complex output x, let w_i=normSq(x_i), sum_i w_i=1, and assign q_i=w_i^2/(sum_j w_j^2).",
    "FairProtocol has native-circuit leaves and binary fair mixtures; leaf assignments use q and mixture assignments recursively average probability vectors. This fair randomization is supplied syntax."]
  conclusions := [
    "The denominator is strictly positive on every normalized finite output; q is nonnegative, normalized and bounded by one, with exact identity-basis calibration.",
    "The assignment is covariant under output permutations, unchanged on data outputs by inert vacuum padding with zero ancillary probabilities, and invariant under equality of complete evaluated native circuit maps.",
    "For every native circuit from a basis source, structural output weights remain normalized and assigned probabilities are normalized and bounded. Every finite FairProtocol retains those bounds and normalization and satisfies syntactic midpoint accounting.",
    "On Fin 3 at input e_0, c=T_01 has weights (1/2,1/2,0) and assigned q_0=1/2, while c'=T_01 then T_12 has weights (1/2,1/4,1/4) and assigned q_0=2/3.",
    "The selected output-0 amplitudes of c,c' agree for every complex input, hence their complete selected-weight profiles agree, despite the different assigned probabilities. No function of the deterministic all-input selected-weight profile can reproduce this assignment on every native circuit.",
    "Thus the supplied native circuit algebra, conserved structural weights, full-process equivalence, normalization, identity-basis calibration and syntactic fair mixing do not alone imply individual-event profile sufficiency or independence from operations on other outputs."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeContextualProbabilityControl.lean"
      declarations := [
        "IDT.QMClosure.NativeContextualProbabilityControl.denominator_pos",
        "IDT.QMClosure.NativeContextualProbabilityControl.probability_nonneg",
        "IDT.QMClosure.NativeContextualProbabilityControl.probability_le_one",
        "IDT.QMClosure.NativeContextualProbabilityControl.probability_sum",
        "IDT.QMClosure.NativeContextualProbabilityControl.basis_calibration",
        "IDT.QMClosure.NativeContextualProbabilityControl.probability_permutation",
        "IDT.QMClosure.NativeContextualProbabilityControl.probability_vacuum_data",
        "IDT.QMClosure.NativeContextualProbabilityControl.probability_vacuum_ancilla",
        "IDT.QMClosure.NativeContextualProbabilityControl.circuit_output_normalized",
        "IDT.QMClosure.NativeContextualProbabilityControl.circuit_probability_bounds",
        "IDT.QMClosure.NativeContextualProbabilityControl.circuit_probability_sum",
        "IDT.QMClosure.NativeContextualProbabilityControl.identity_calibration",
        "IDT.QMClosure.NativeContextualProbabilityControl.complete_process_equivalence",
        "IDT.QMClosure.NativeContextualProbabilityControl.syntactic_midpoint",
        "IDT.QMClosure.NativeContextualProbabilityControl.protocol_probability_bounds",
        "IDT.QMClosure.NativeContextualProbabilityControl.protocol_probability_sum",
        "IDT.QMClosure.NativeContextualProbabilityControl.selected_amplitude_equal",
        "IDT.QMClosure.NativeContextualProbabilityControl.selected_profile_equal",
        "IDT.QMClosure.NativeContextualProbabilityControl.witness_before_weights",
        "IDT.QMClosure.NativeContextualProbabilityControl.witness_after_weights",
        "IDT.QMClosure.NativeContextualProbabilityControl.witness_before_probability",
        "IDT.QMClosure.NativeContextualProbabilityControl.witness_after_probability",
        "IDT.QMClosure.NativeContextualProbabilityControl.spectator_operation_changes_probability",
        "IDT.QMClosure.NativeContextualProbabilityControl.no_selected_profile_readout"] }]
  plannedArtifacts := []
  dependencies := ["normalized_mixer_generated_process_wall", "native_attenuation_calibrated_selection"]
  limits := [
    "The assignment is a mathematical countermodel to automatic profile sufficiency, not a physical probability proposal, a change to native dynamics or a QuarticContextTransport result.",
    "It does not descend to the current rational coordinate-domain event law; syntactic midpoint accounting does not provide midpoint accounting after individual-event profile identifications.",
    "Spectator-output locality, deterministic all-input selected-profile sufficiency and mixture-event profile sufficiency remain distinct premises. Spectator-output locality excludes this witness; no theorem equating these premises is asserted.",
    "Probability-preserving descent for the relevant full event profiles, including required mixture-event identifications, remains a supplied bridge rather than a consequence of the listed controls.",
    "No Bell no-signalling claim, physical actual-event generator, Born-rule closure or full-QM closure is established."] }

def rawNativeScalarCircuitBridge : ResearchTask := {
  id := "raw_native_scalar_circuit_bridge"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use existing RawOperationalHilbert.Data d: the original raw operation, chosen zero, global square-to-swap and medial laws, nonnegative real weight W with W(chosenZero)=0, and all-input weight conservation.",
    "Use only d's reconstructed group, phase, half, canonical Hilbert output and feature F; no independent Hilbert carrier or complex scalar action on raw V is supplied.",
    "The generic circuit invariant assumes one common reference v and raw inputs x_i satisfying F(x_i)=z_i*F(v) for arbitrary mathematical complex coordinates z_i. Scalar multiplication is only in d's constructed Hilbert output."]
  conclusions := [
    "The reconstructed normalized operation has feature outputs (a*F(x)+b*F(y),b*F(x)+a*F(y)), with a=(1+i)/2 and b=(1-i)/2.",
    "The syntax lift retargets the existing scalar Circuit to d.normalizedOperation while retaining identity, pair indices, permutations and chronological sequence.",
    "For every supplied common-reference feature relation F(x_i)=z_i*F(v), every lifted circuit obeys F(rawEval(c,x)_k)=scalarEval(c,z)_k*F(v) and W(rawEval(c,x)_k)=normSq(scalarEval(c,z)_k)*W(v).",
    "Input v at one source and chosenZero elsewhere automatically satisfies that feature relation with scalar basis input e_s. Its selected output weight is normSq(scalarEval(c,e_s)_k)*W(v), including null references and all-null models.",
    "The corresponding relative weight equals the scalar selected squared norm only under the additional explicit hypothesis W(v)>0."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawNativeScalarCircuitBridge.lean"
      declarations := [
        "IDT.QMClosure.RawNativeScalarCircuitBridge.feature_normalized_fst",
        "IDT.QMClosure.RawNativeScalarCircuitBridge.feature_normalized_snd",
        "IDT.QMClosure.RawNativeScalarCircuitBridge.liftCircuit",
        "IDT.QMClosure.RawNativeScalarCircuitBridge.circuit_feature",
        "IDT.QMClosure.RawNativeScalarCircuitBridge.circuit_weight",
        "IDT.QMClosure.RawNativeScalarCircuitBridge.circuit_weight_ratio",
        "IDT.QMClosure.RawNativeScalarCircuitBridge.single_feature",
        "IDT.QMClosure.RawNativeScalarCircuitBridge.single_circuit_feature",
        "IDT.QMClosure.RawNativeScalarCircuitBridge.single_circuit_weight",
        "IDT.QMClosure.RawNativeScalarCircuitBridge.single_circuit_weight_ratio"] }]
  plannedArtifacts := []
  dependencies := ["raw_operational_hilbert_facade", "normalized_mixer_generated_process_wall"]
  limits := [
    "The adapter concerns the mathematically reconstructed d.normalizedOperation; physical access to this normalization control remains open.",
    "The original raw operation differs through its diagonal involution D(x)=first(T_raw(x,x)). This mathematical expression supplies no copying procedure for an unknown raw input.",
    "The general invariant is conditional on the supplied feature relation and establishes no availability of arbitrary complex raw preparations. The basis-input construction is an algebraic theorem, not physical preparation availability.",
    "No raw state of weight one, actual calibration, physical wire availability, probability interpretation, coordinate noncontextuality, midpoint accounting or full-QM closure follows.",
    "Finite wire arrays represent coherent alternatives, not tensor composites. No general raw faithfulness, Gaussian quotient or denominator-consistency result is asserted."] }

def nativeEventProbabilityBridge : ResearchTask := {
  id := "native_event_probability_bridge"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For general factorization, supply any e:S->A and pi:S->R with a chosen zero in R. Kernel constancy means e(s)=e(t) implies pi(s)=pi(t).",
    "The concrete Event grammar has zero, total, basis_i, all four attenuation(q,m) leaves and binary fair mixtures. Its independent structural profile evaluates actual attenuation selected circuits and averages mixture profiles.",
    "ProbabilityLaw on Event(n+1) supplies real probabilities, zero value 0, total value 1, basis_0 calibration 1, global event nonnegativity, fair-mixture averaging and full-profile probability sufficiency for every syntax event, including mixtures."]
  conclusions := [
    "A total factor q exists exactly when kernel constancy holds; any two such factors agree on range(e), with no uniqueness assertion outside the image.",
    "For every event and complex input, profile(s,x)=quadratic(effect(s),x), independently of any probability law. The total profile sums all data input weights, while attenuation leaves evaluate literal retained-ancilla circuits.",
    "Under a supplied ProbabilityLaw, equal effects have equal all-input profiles and hence equal probability. Factoring through D=range(effect) transfers zero, midpoint, representative, nonnegativity, normalization and calibration laws to the committed attenuation selection and gives prob(s)=effect(s)_00.",
    "For every event and complex input, its profile is nonnegative and bounded above by the total input squared-norm weight.",
    "The explicit canonicalProbabilityLaw evaluates each profile at basis input single_0(1), satisfies every supplied law and establishes mathematical nonemptiness of ProbabilityLaw for each n.",
    "All ProbabilityLaw probability functions agree extensionally on this certified event grammar, and every such law assigns every event a probability in [0,1]. This is function equality, not an assertion identifying proof fields of law structures.",
    "The canonical model is a downstream mathematical consistency witness appended after selection; its definition and existence are not premises of the conditional selection argument."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeEventProbabilityBridge.lean"
      declarations := [
        "IDT.QMClosure.NativeEventProbabilityBridge.factorization_iff_fibre_constancy",
        "IDT.QMClosure.NativeEventProbabilityBridge.factors_agree_on_range",
        "IDT.QMClosure.NativeEventProbabilityBridge.profile_soundness",
        "IDT.QMClosure.NativeEventProbabilityBridge.equal_effect_implies_equal_profile",
        "IDT.QMClosure.NativeEventProbabilityBridge.probability_factors",
        "IDT.QMClosure.NativeEventProbabilityBridge.probability_selected",
        "IDT.QMClosure.NativeEventProbabilityBridge.profile_nonnegative",
        "IDT.QMClosure.NativeEventProbabilityBridge.profile_le_total",
        "IDT.QMClosure.NativeEventProbabilityBridge.canonicalProbabilityLaw",
        "IDT.QMClosure.NativeEventProbabilityBridge.probabilityLaw_nonempty",
        "IDT.QMClosure.NativeEventProbabilityBridge.probability_unique",
        "IDT.QMClosure.NativeEventProbabilityBridge.probability_bounds"] }]
  plannedArtifacts := []
  dependencies := ["native_attenuation_calibrated_selection", "native_contextual_probability_control"]
  limits := [
    "The identity effect is represented by the total event; it is not one selected output of an identity circuit.",
    "The concrete grammar provides explicit rational coordinates only for its named leaves and finite mixtures. No generic rational effect extraction for arbitrary native circuits is assumed or asserted.",
    "Full-profile sufficiency on all event syntax, physical availability of every finite ancillary width, fair-coin availability, mixture accounting and matched calibration remain supplied bridges.",
    "Spectator-output locality, deterministic all-input profile sufficiency and all-mixture profile sufficiency remain different premises; the contextual countermodel supplies none of them physically.",
    "The canonical witness concerns this mathematical grammar at one basis input. It asserts no probability-law existence on arbitrary physical event domains and imports no Born premise into the uniqueness argument.",
    "Extensional uniqueness is limited to probability functions on the certified grammar; arbitrary total coordinate factors remain unconstrained outside range(effect).",
    "No physical actual-event generator, arbitrary-preparation selection, general mixed-state reconstruction, Born-rule closure or full-QM closure is established."] }

def nativeThreeWireSpectatorLocality : ResearchTask := {
  id := "native_three_wire_spectator_locality"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The matrix core uses NativeMixerInfiniteOrder.Mat3 and spectator B=T_12. Invariants explicitly require U*U_conjTranspose=I and U_conjTranspose*U=I, preservation of the uniform vector, and determinant in {1,i,-1,-i}.",
    "The native adapter uses the existing complex three-wire Circuit grammar, including identity, distinct-wire pair, permutation and sequence constructors.",
    "A general A-valued readout pi on native three-wire circuits respects equality of complete evaluated maps and is invariant under postcomposition by T_12, the supplied spectator-output locality law."]
  conclusions := [
    "Under the explicit matrix invariants, full selected squared-norm equality on every complex three-wire input identifies the selected rows exactly. Preservation of ones supplies the phase reference for the three norm comparisons.",
    "The relative matrix R=V*U_conjTranspose fixes the selected row and column. Its remaining block is [[z,1-z],[1-z,z]], with determinant 2z-1. The fourth-root determinant condition yields R=B^r for some r<4.",
    "Full all-input selected squared-norm profile equality is equivalent to V=B^r*U for some r<4 under the explicit matrix invariants.",
    "The actual native circuit adapter proves matrix action on every vector and derives all three invariants for every constructor. It realizes B^r*U by an appended spectator circuit; the suffix claim is evaluation equality, not a decomposition of the original syntax.",
    "Complete-map invariance plus supplied post-T_12 spectator locality imply deterministic full-input selected-profile sufficiency for every A-valued readout on native three-wire circuits.",
    "T_02 and T_02^3 have equal selected weight normSq(z)/2 on every compressed input (z,w,0). The real probe pi(c)=Im(c.eval(e_2)_0) respects both readout premises yet returns -1/2 and +1/2. Thus those generic premises do not imply compressed-profile descent."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeThreeWireStabilizer.lean"
      declarations := [
        "IDT.QMClosure.NativeThreeWireStabilizer.selected_rows_equal",
        "IDT.QMClosure.NativeThreeWireStabilizer.stabilizer_classification",
        "IDT.QMClosure.NativeThreeWireStabilizer.selected_readout_iff_suffix"] },
    { sourcePath := "Proofs/QMClosure/NativeThreeWireLocality.lean"
      declarations := [
        "IDT.QMClosure.NativeThreeWireLocality.circuit_action",
        "IDT.QMClosure.NativeThreeWireLocality.circuit_invariants",
        "IDT.QMClosure.NativeThreeWireLocality.appendSpectator_matrix",
        "IDT.QMClosure.NativeThreeWireLocality.full_selected_profile_readout",
        "IDT.QMClosure.NativeThreeWireLocality.compressed_profile_equal",
        "IDT.QMClosure.NativeThreeWireLocality.probeReadout_premises",
        "IDT.QMClosure.NativeThreeWireLocality.probeReadout_gate02",
        "IDT.QMClosure.NativeThreeWireLocality.probeReadout_gate02Cubed",
        "IDT.QMClosure.NativeThreeWireLocality.compressed_profile_descent_not_forced"] }]
  plannedArtifacts := []
  dependencies := ["normalized_mixer_generated_process_wall", "native_contextual_probability_control", "native_event_probability_bridge"]
  limits := [
    "The matrix theorem is conditional on explicit invariants; the separate adapter establishes them for actual native circuits. Arbitrary invariant-matrix realizability is not established.",
    "The readout transfer needs no readout positivity, normalization, calibration, continuity or Lie-group density premise. Physical justification of spectator-output locality remains supplied.",
    "The compressed-input countermodel concerns a general real readout, not a normalized probability law.",
    "The checked classification is restricted to three wires. Widths of four or more are not classified here, and determinant information alone does not establish their stabilizers.",
    "Classical-mixture effect equalities are not covered by the relative-unitary argument. Existing attenuation selection uses unbounded widths, vacuum compression and mixtures, so this result does not replace its full-profile probability premise.",
    "No physical availability, complex representation from primitives in this adapter, actual-event law, arbitrary mixed-state representation, Born-rule closure or full-QM closure is established."] }

def nativeDyadicSynthesis : ResearchTask := {
  id := "native_dyadic_synthesis"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Three Gaussian-integer numerators u, exponent k, pi=1+i, sum(u)=pi^k and sum(norm(u_j))=2^k.",
    "Equivalently, the represented complex vector u/pi^k has coherent sum one and total squared norm one.",
    "Use the existing actual native three-wire Circuit syntax with identity, normalized pair mixers, permutations and composition."]
  conclusions := [
    "Exact Gaussian parity and divisibility give a denominator step with an actual identity or pair-gate witness. Exponent-zero and exponent-one classifications include all-divisible representatives.",
    "Induction constructs a finite native circuit reducing every such three-vector to a basis vector.",
    "A literal native inverse uses three copies of each pair, inverse permutations and reversed composition. Composing with a source permutation constructs the vector from source basis zero.",
    "The vector-facing theorem assumes the represented vector's sum and squared norm directly and proves the corresponding Gaussian numerator normalizations."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeDyadicGaussianArithmetic.lean"
      declarations := [
        "IDT.QMClosure.NativeDyadicGaussianArithmetic.three_parity",
        "IDT.QMClosure.NativeDyadicGaussianArithmetic.sum_one_norm_one",
        "IDT.QMClosure.NativeDyadicGaussianArithmetic.sum_pi_norm_two",
        "IDT.QMClosure.NativeDyadicGaussianArithmetic.divide_pair"] },
    { sourcePath := "Proofs/QMClosure/NativeDyadicThreeVectorSynthesis.lean"
      declarations := [
        "IDT.QMClosure.NativeDyadicThreeVectorSynthesis.denominator_descent",
        "IDT.QMClosure.NativeDyadicThreeVectorSynthesis.legal_three_vector_reduces",
        "IDT.QMClosure.NativeDyadicThreeVectorSynthesis.inverseCircuit_left",
        "IDT.QMClosure.NativeDyadicThreeVectorSynthesis.legal_three_vector_synthesizes_from_zero",
        "IDT.QMClosure.NativeDyadicThreeVectorSynthesis.normalized_three_vector_synthesizes"] }]
  plannedArtifacts := [
    "A separate width-four native-circuit and selected-profile adapter using the checked explicit-invariant three-matrix synthesis."]
  dependencies := ["native_three_wire_spectator_locality"]
  limits := [
    "The checked result in these two files is three-coordinate vector synthesis in the supplied complex representation. The separate matrix artifact has its own explicit invariant contract; the width-four readout consequence remains open.",
    "No physical preparation availability, compressed-profile descent, classical-mixture profile law, actual-event generation or full-QM closure follows."] }

def nativeDyadicThreeMatrixSynthesis : ResearchTask := {
  id := "native_dyadic_three_matrix_synthesis"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A complex three-by-three matrix satisfies the existing Invariants: unitarity on both sides, preservation of the ones vector, and fourth-root determinant.",
    "Its first column is represented by Gaussian integers over a common power of 1+i."]
  conclusions := [
    "The first column has coherent sum one and squared norm one, so the checked vector theorem supplies an actual native circuit with that column.",
    "The relative matrix fixes the first basis column and row. The checked spectator classification reduces it to a power of T_12.",
    "Composing the actual column circuit and spectator word realizes the entire supplied matrix exactly."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeDyadicThreeMatrixSynthesis.lean"
      declarations := [
        "IDT.QMClosure.NativeDyadicThreeMatrixSynthesis.first_column_sum",
        "IDT.QMClosure.NativeDyadicThreeMatrixSynthesis.first_column_norm",
        "IDT.QMClosure.NativeDyadicThreeMatrixSynthesis.same_first_column_factor",
        "IDT.QMClosure.NativeDyadicThreeMatrixSynthesis.matrix_synthesis_of_dyadic_first_column"] }]
  plannedArtifacts := []
  dependencies := ["native_dyadic_synthesis", "native_three_wire_spectator_locality"]
  limits := [
    "The fourth-root determinant is an explicit hypothesis. This artifact does not establish that restriction for every arbitrary dyadic unitary matrix.",
    "Only first-column dyadic data are required under the full invariant contract. No wider-width adapter, physical preparation availability or readout actualization follows."] }

def nativeDyadicWiderFrontier : ResearchTask := {
  id := "native_dyadic_wider_frontier"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "For analytic vector synthesis, D=Z[i,1/2], pi=1+i, sum(v)=1 and sum(normSq(v_j))=1.",
    "The matrix route additionally requires dyadic unitary completion fixing the ones vector; the readout route supplies complete-process equality and locality for every spectator pair."]
  conclusions := [
    "Independently reviewed analytic extension, not checked: through dimension five, four odd numerators of one residue class can be split by equal-denominator preparatory gates. The minimum finite pi-valuation of their differences decreases until two classes can be paired.",
    "Four identical odd numerators cannot occur in a legal vector of dimension four or five: the sum/norm equations give 3*norm(c)+2*Re(c*conj(a))=0, contradicting odd norm(c).",
    "The analytic extension gives vector and matrix synthesis through dimension five and deterministic full-profile locality through circuit width six. These consequences are not kernel evidence.",
    "The explicit six-vector in native_dyadic_six_wire_obstruction is excluded by reduction modulo five. Together with the analytic through-five result this locates the first unrestricted legal-vector failure at dimension six; smallest-dimension status remains analytic.",
    "A necessary condition for a row or column of a uniform-fixing dyadic unitary is that its coordinate differences generate D. This condition is not asserted sufficient.",
    "Even with primitive differences, monotone denominator descent can fail: u=(-1,-1,-1,-1,3-i,-3-3i), denominator pi^5, has sum pi^5 and total numerator norm 32. Its differences generate D, but all moves not increasing the least denominator exponent preserve four identical odd coordinates; any odd/even pair raises the exponent."]
  checkedEvidence := []
  plannedArtifacts := [
    "Checked four-odd preparatory descent and the dimension-four/five identical-coordinate exclusion.",
    "A checked primitive-difference monotone-descent control, followed by a strategy allowing denominator increases or using unitary completion."]
  dependencies := ["native_dyadic_synthesis", "native_dyadic_six_wire_obstruction"]
  limits := [
    "Neither the six-vector obstruction nor the monotone-descent wall disproves arbitrary-width matrix synthesis.",
    "For larger-width locality the exact sufficient group obligation is that the native selected-row stabilizer is generated by spectator gates. Full arithmetic-unitary synthesis is a stronger route, not a necessary premise.",
    "No compressed-profile, mixture-law, physical-availability or QM closure follows."] }

def nativeDyadicSixWireObstruction : ResearchTask := {
  id := "native_dyadic_six_wire_obstruction"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The explicit six-vector has four coordinates (1+i)/4 and two coordinates -i/2.",
    "Use the actual native Circuit grammar at width six. A Gaussian dyadic residue relation sends i to 3 modulo five."]
  conclusions := [
    "The explicit vector has coherent sum one and total squared norm one.",
    "Every input coordinate has residue one. Actual native identity, pair, permutation and sequence operations preserve the all-one residue property; a basis vector cannot have that property.",
    "No actual native circuit reduces the vector to any basis vector. An explicit inverse-word construction also excludes preparing it from any basis vector."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeDyadicSixWireObstruction.lean"
      declarations := [
        "IDT.QMClosure.NativeDyadicSixWireObstruction.circuit_preserves_one",
        "IDT.QMClosure.NativeDyadicSixWireObstruction.no_native_reduction",
        "IDT.QMClosure.NativeDyadicSixWireObstruction.no_native_preparation",
        "IDT.QMClosure.NativeDyadicSixWireObstruction.six_wire_vector_obstruction"] }]
  plannedArtifacts := []
  dependencies := ["normalized_mixer_generated_process_wall"]
  limits := [
    "This is a legal-vector countermodel to unrestricted synthesis from sum and norm alone. It is not a counterexample to synthesis of dyadic unitary matrices fixing ones.",
    "The separate analytic ideal argument shows this vector cannot be a row or column of such a unitary. The checked circuit obstruction alone makes no smallest-dimension assertion.",
    "No physical preparation, actual-event probability or QM closure is established."] }

def nativeThreeWireResidueProbability : ResearchTask := {
  id := "native_three_wire_residue_probability"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the actual native complex three-wire Circuit grammar with source basis zero.",
    "The probability definition reduces Gaussian dyadic scalar outputs into F_3[i]. It assigns zero, one or one half according as the real residue is zero, one or two.",
    "Kernel finite checks cover every three-coordinate residue vector of coherent sum one and norm one. No map from all complex numbers to characteristic three is supplied."]
  conclusions := [
    "A functional Gaussian dyadic reduction relation connects actual complex evaluation to the residue evaluation for every circuit constructor.",
    "The resulting probability function is nonnegative and normalized on every finite native three-wire circuit, with calibration for every circuit preparing a literal basis state.",
    "Equal selected complex amplitudes at the source have equal probability. In particular, equal prepared states and complete evaluated maps have equal probability; every source-fixing prefix is invisible.",
    "Output permutations and spectator pairs preserve the corresponding selected probabilities. The checked three-wire locality theorem also gives deterministic full-input selected-profile sufficiency.",
    "For T_01 followed by T_12, output one has probability one half and squared amplitude one quarter. Thus these fixed-width premises do not select the squared-amplitude probability.",
    "Let A=T_02 output two, B=T_01 then T_12 then T_01 output zero, C=T_12 output one, D=T_01 then T_12 then T_02 output two. The two fair sums of their squared-amplitude profiles agree for every complex input.",
    "Their probabilities are respectively one half, one, zero and zero. Fair-mixture accounting therefore assigns three quarters versus zero to those equal profiles, refuting two-mixture profile sufficiency for this law."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeThreeWireResidueProbability.lean"
      declarations := [
        "IDT.QMClosure.NativeThreeWireResidueProbability.finite_frame",
        "IDT.QMClosure.NativeThreeWireResidueProbability.reduces_functional",
        "IDT.QMClosure.NativeThreeWireResidueProbability.circuit_reduces",
        "IDT.QMClosure.NativeThreeWireResidueProbability.probability_nonnegative",
        "IDT.QMClosure.NativeThreeWireResidueProbability.probability_normalized",
        "IDT.QMClosure.NativeThreeWireResidueProbability.probability_basis_state",
        "IDT.QMClosure.NativeThreeWireResidueProbability.probability_amplitude_eq",
        "IDT.QMClosure.NativeThreeWireResidueProbability.probability_prepared_eq",
        "IDT.QMClosure.NativeThreeWireResidueProbability.probability_output_permutation",
        "IDT.QMClosure.NativeThreeWireResidueProbability.probability_spectator_pair",
        "IDT.QMClosure.NativeThreeWireResidueProbability.probability_source_fixing_prefix",
        "IDT.QMClosure.NativeThreeWireResidueProbability.probability_full_selected_profile",
        "IDT.QMClosure.NativeThreeWireResidueProbability.probability_not_born",
        "IDT.QMClosure.NativeThreeWireResidueProbability.equal_two_mixture_profiles",
        "IDT.QMClosure.NativeThreeWireResidueProbability.two_mixture_profile_sufficiency_fails"] }]
  plannedArtifacts := []
  dependencies := ["native_three_wire_spectator_locality", "native_event_probability_bridge"]
  limits := [
    "This is a mathematical countermodel, not a physical probability proposal. The source is fixed to basis zero; arbitrary physical preparations are not covered.",
    "Its three-wire consistency does not imply a consistent larger-width law. The separate checked four-wire extension obstruction excludes the specified compatible extension.",
    "The mixture theorem compares selected outputs of separate circuits, not simultaneous orthogonal outputs of one circuit. It refutes profile descent of their arithmetic fair mixtures.",
    "An independently checked analytic argument shows discontinuity along the existing infinite-order native word K: its residue has order three, while powers in one nonzero congruence class approach identity in the complex representation. This continuity boundary is not a checked theorem here.",
    "No physical actual-event generation, probability continuity, general mixed-state reconstruction or original Born/QM closure is established."] }

def nativeThreeWireProbabilityExtensionWall : ResearchTask := {
  id := "native_three_wire_probability_extension_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A proposed four-wire law is nonnegative and normalized, invariant under spectator-output pairs, and respects equality of the prepared basis-zero output state.",
    "The extension contradiction needs only three explicit padding agreements: after u=(01,02), outputs one and two match the three-wire values one half; after v=(01,13,01,swap03), output three matches the three-wire value one.",
    "The separate quantitative bound additionally assumes output-permutation covariance, and needs none of these residue-law padding values."]
  conclusions := [
    "After u followed by 03, locality keeps outputs one and two at one half. Normalization and nonnegativity force output three to zero.",
    "The suffix (12,02,12,02) preserves output-three probability. The long word and v prepare exactly the same state (-i/2,(3+i)/4,0,(1+i)/4). Prepared-state equality contradicts the padded probability one.",
    "Both concrete padding identities and the three probability values are checked. The specific three-wire law has no extension satisfying these finite structural premises and agreements; the extension need not retain a scalar-residue formula.",
    "Independently of residue calibration, (01,13,02,03) prepares (-1/2,1/2,1/2,1/2). Prepared-state equality and output covariance equalize the last three probabilities. Spectator locality and positivity give zero <= P(01,13; output 1) <= one third."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeThreeWireProbabilityExtensionWall.lean"
      declarations := [
        "IDT.QMClosure.NativeThreeWireProbabilityExtensionWall.prepared_states_equal",
        "IDT.QMClosure.NativeThreeWireProbabilityExtensionWall.no_four_wire_law_with_three_facts",
        "IDT.QMClosure.NativeThreeWireProbabilityExtensionWall.initial_is_padded",
        "IDT.QMClosure.NativeThreeWireProbabilityExtensionWall.right_is_padded",
        "IDT.QMClosure.NativeThreeWireProbabilityExtensionWall.no_residue_probability_extension",
        "IDT.QMClosure.NativeThreeWireProbabilityExtensionWall.balanced_prepares",
        "IDT.QMClosure.NativeThreeWireProbabilityExtensionWall.equal_coordinate_probabilities",
        "IDT.QMClosure.NativeThreeWireProbabilityExtensionWall.attenuation_probability_bound"] }]
  plannedArtifacts := []
  dependencies := ["native_three_wire_residue_probability"]
  limits := [
    "This rejects the specified three-wire law's extension. The one-third bound does not select the squared-amplitude value one quarter or establish a unique four-wire law.",
    "The contradiction uses only the displayed padding instances. It does not construct generic embeddings or physical vacuum availability.",
    "No probability continuity, arbitrary-input probability law, physical actualization or original Born/QM closure follows."] }

def nativeStableAmplitudeOrbitWall : ResearchTask := {
  id := "native_stable_amplitude_orbit_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Actual three-wire words (01,02,12,02,12) and (02,12,02,01,12), source basis zero.",
    "Spectator processes use native pairs and permutations avoiding selected port zero, with any finite number of fresh zero spectators."]
  conclusions := [
    "The words prepare u=(-1/4,(7+i)/8,(3-i)/8) and v=(-1/4,(7-i)/8,(3+i)/8). Both have sum one, squared norm one and the same selected amplitude.",
    "Functional Gaussian dyadic reduction modulo five sends i to three. All spectators of u have zero residue, whereas the first spectator of v has residue three.",
    "Actual native spectator circuits preserve all-zero residue. Neither direction of connection exists after any fixed finite zero padding.",
    "This excludes unrestricted stable spectator-orbit connectivity as a proof of selected-amplitude probability sufficiency."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeStableAmplitudeOrbitWall.lean"
      declarations := [
        "IDT.QMClosure.NativeStableAmplitudeOrbitWall.related_functional",
        "IDT.QMClosure.NativeStableAmplitudeOrbitWall.prepareU_eval",
        "IDT.QMClosure.NativeStableAmplitudeOrbitWall.prepareV_eval",
        "IDT.QMClosure.NativeStableAmplitudeOrbitWall.circuit_preserves_zero",
        "IDT.QMClosure.NativeStableAmplitudeOrbitWall.no_stable_spectator_connection",
        "IDT.QMClosure.NativeStableAmplitudeOrbitWall.no_reverse_stable_spectator_connection",
        "IDT.QMClosure.NativeStableAmplitudeOrbitWall.stable_amplitude_orbit_wall"] }]
  plannedArtifacts := []
  dependencies := ["native_dyadic_six_wire_obstruction"]
  limits := [
    "This is a circuit-orbit obstruction, not a probability countermodel. No law is shown to distinguish the preparations.",
    "The selected output is untouched throughout the obstruction. Splitting that output or comparing coherent copies is not excluded.",
    "Extra normalization and embedding relations may force equality across distinct spectator orbits. No impossibility of scalar probability factorization is asserted."] }

def nativeBinaryPhaseCountMass : ResearchTask := {
  id := "native_binary_phase_count_mass"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Binary leaves are actual recursive finite products; phase is the number of B choices modulo four.",
    "At each required depth 4*k+1, nonnegative real phase weights have total counted mass p and first-A-subtree mass r. Weights may vary freely with depth."]
  conclusions := [
    "Actual leaf-fibre cardinalities satisfy the phaseCount recurrence, including its exceptional depth-zero base.",
    "Exact four-step formulas bound |r-p/2| by p/[2*(4^k-1)] for k >= 1.",
    "Archimedean order forces r=p/2 when those counted identities hold at every required depth, without continuity or cross-depth identification of weights."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeBinaryPhaseCounting.lean"
      declarations := [
        "IDT.QMClosure.NativeBinaryPhaseCounting.phaseCount_unique",
        "IDT.QMClosure.NativeBinaryPhaseCounting.phaseCount_four",
        "IDT.QMClosure.NativeBinaryPhaseCounting.phaseCount_four_add_one",
        "IDT.QMClosure.NativeBinaryPhaseCounting.mass_deviation_bound",
        "IDT.QMClosure.NativeBinaryPhaseCounting.phase_count_mass_halving"] },
    { sourcePath := "Proofs/QMClosure/NativeBinaryLeaves.lean"
      declarations := [
        "IDT.QMClosure.NativeBinaryLeaves.rootA_phase",
        "IDT.QMClosure.NativeBinaryLeaves.leafCount_eq",
        "IDT.QMClosure.NativeBinaryLeaves.sum_by_phase"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "This is a counted-mass theorem. Actual probability identities come from the separate checked native adapter.",
    "An isolated finite depth gives a bound, not exact halving. No physical resource availability follows."] }

def nativeVacuumProbabilityFamily : ResearchTask := {
  id := "native_vacuum_probability_family"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Law assigns real probabilities to actual native circuits, a marked source basis port and an output, for each finite wire type.",
    "Supplied fields: nonnegativity, normalization, prepared-state equality, output-permutation covariance, spectator-pair locality and preservation of old probabilities under constructorwise fresh-zero embeddings."]
  conclusions := [
    "Every native constructor has an explicit vacuum embedding; its prepared state is the old state followed by zeros.",
    "Fresh ports have zero probability; a pair conserves the sum of its two probabilities; equal prepared coordinates in one state have equal probabilities.",
    "Comparison with a fresh vacuum port proves zero probability for every zero-amplitude output. Calibration follows for all actual basis-state preparations.",
    "The separate squared-amplitude canonicalLaw witnesses mathematical nonemptiness. It is not a premise of probability selection."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeVacuumProbabilityFamily.lean"
      declarations := [
        "IDT.QMClosure.NativeVacuumProbabilityFamily.pad_prepared",
        "IDT.QMClosure.NativeVacuumProbabilityFamily.vacuum_probability_zero",
        "IDT.QMClosure.NativeVacuumProbabilityFamily.pair_probability_sum",
        "IDT.QMClosure.NativeVacuumProbabilityFamily.equal_coordinate_probabilities",
        "IDT.QMClosure.NativeVacuumProbabilityFamily.zero_amplitude_probability_zero",
        "IDT.QMClosure.NativeVacuumProbabilityFamily.basis_calibration",
        "IDT.QMClosure.NativeVacuumProbabilityFamily.canonicalLaw"] }]
  plannedArtifacts := []
  dependencies := ["native_three_wire_probability_extension_wall"]
  limits := [
    "Law is an explicit conditional contract, not a physically justified probability assignment.",
    "There is no arbitrary cross-type relabel axiom, input-source covariance, scalar-amplitude sufficiency, mixture law, continuity or independent calibration field.",
    "The native representation and arbitrary finite vacuum availability remain mathematical premises."] }

def nativeBinaryRefinementSelection : ResearchTask := {
  id := "native_binary_refinement_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The checked nativeVacuumProbabilityFamily.Law contract over all finite wire types and constructorwise fresh-zero embeddings.",
    "Every finite binary refinement uses actual native pair gates with all wires retained.",
    "Real Archimedean probabilities; no probability continuity, scalar sufficiency or mixture-profile sufficiency premise."]
  conclusions := [
    "Each level pads the previous actual circuit and folds disjoint native pairs in a literal finite list order.",
    "Pair conservation proves total descendant mass and first-A-subtree mass in the same root-first tree. Depth one is exactly the literal vacuum split.",
    "A depth-m leaf has amplitude a^m times its fourth-root phase times the root amplitude. Equal phase gives equal coordinate probabilities within that prepared state.",
    "Phase weights are chosen from actual output fibres, with no extra resource premise. Checked leaf cardinalities supply both counted-mass identities.",
    "For every source, native circuit and selected output, both outputs of the literal vacuum split have half its original probability.",
    "The finite-depth adapter proves |r-p/2| <= p/[2*(4^k-1)] from depth 4*k+1. Its stated Law contract remains global; it is not a finite experimental validation theorem."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeBinaryRefinement.lean"
      declarations := [
        "IDT.QMClosure.NativeBinaryRefinement.appendPairs_child_sum",
        "IDT.QMClosure.NativeBinaryRefinement.total_leaf_probability",
        "IDT.QMClosure.NativeBinaryRefinement.rootA_probability",
        "IDT.QMClosure.NativeBinaryRefinement.tree_one_eq_split",
        "IDT.QMClosure.NativeBinaryRefinement.leaf_amplitude",
        "IDT.QMClosure.NativeBinaryRefinement.counted_native_masses",
        "IDT.QMClosure.NativeBinaryRefinement.native_finite_refinement_bound",
        "IDT.QMClosure.NativeBinaryRefinement.native_vacuum_split_halves",
        "IDT.QMClosure.NativeBinaryRefinement.native_vacuum_split_fresh_halves"] }]
  plannedArtifacts := []
  dependencies := ["native_binary_phase_count_mass", "native_vacuum_probability_family"]
  limits := [
    "This is conditional exact native split halving, not general Born uniqueness.",
    "It uses unbounded finite-width compatibility, which the checked fixed-three-wire countermodel lacks.",
    "Physical vacuum availability, actual-event generation and general probability-preserving coarse-profile descent remain open."] }

def nativeCoherentScalarSufficiency : ResearchTask := {
  id := "native_coherent_scalar_sufficiency"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The checked native probability-family contract and its vacuum-split halving theorem.",
    "All circuits use literal sum wire types, the same original marked source, constructorwise block lifts and retained fresh wires."]
  conclusions := [
    "Halving transfers to an existing zero-amplitude partner by padding one fresh wire and swapping the two initially zero ports.",
    "An actual two-block dilation prepares (a*cstate,b*dstate). Both branch probability formulas follow from output-wise splitting, complete prepared-state comparison and spectator locality.",
    "The right-branch argument explicitly commutes disjoint block circuits at the evaluated-state level before removing spectator suffixes. No spectator prefix is discarded by locality alone.",
    "Two levels of dilation place selected outputs of c and d in the equal-scale middle branches ab=ba=1/2. Their probabilities are the corresponding original probabilities divided by four.",
    "For any two actual circuits with the same finite wire type and marked source, equality of selected complex amplitudes implies equality of their probabilities, even at different selected ports."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeZeroPortSplitting.lean"
      declarations := [
        "IDT.QMClosure.NativeZeroPortSplitting.internal_zero_partner_prepared",
        "IDT.QMClosure.NativeZeroPortSplitting.internal_zero_partner_halves"] },
    { sourcePath := "Proofs/QMClosure/NativeCoherentBranchDilation.lean"
      declarations := [
        "IDT.QMClosure.NativeCoherentBranchDilation.blocks_reverse_order",
        "IDT.QMClosure.NativeCoherentBranchDilation.duplicate_probabilities",
        "IDT.QMClosure.NativeCoherentBranchDilation.dilation_prepared",
        "IDT.QMClosure.NativeCoherentBranchDilation.dilation_probabilities"] },
    { sourcePath := "Proofs/QMClosure/NativeScalarAmplitudeSufficiency.lean"
      declarations := [
        "IDT.QMClosure.NativeScalarAmplitudeSufficiency.comparison_middle_amplitudes",
        "IDT.QMClosure.NativeScalarAmplitudeSufficiency.same_source_amplitude_sufficiency"] }]
  plannedArtifacts := []
  dependencies := ["native_binary_refinement_selection"]
  limits := [
    "No scalar-sufficiency, classical mixture, arbitrary cross-type relabel or input-source covariance premise is added.",
    "This does not assert stable spectator-orbit connectivity or general coarse-effect descent.",
    "Selection of the actual squared-amplitude formula is supplied by the separate checked numerator-response theorem. No physical probability law or original Born/QM closure follows."] }

def gaussianIntegerQuadraticSelection : ResearchTask := {
  id := "gaussian_integer_quadratic_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A real-valued function q on Gaussian integers with q(0)=0, q(1)=1, invariance under multiplication by i, and the parallelogram identity."]
  conclusions := [
    "The parallelogram recurrence determines every natural affine line.",
    "Rotation invariance fixes the mixed unit terms; the four integer coordinate quadrants give q(g)=Re(g)^2+Im(g)^2.",
    "Neither positivity nor continuity is needed for this algebraic classification."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/GaussianIntegerQuadraticSelection.lean"
      declarations := [
        "IDT.QMClosure.GaussianIntegerQuadraticSelection.nat_affine",
        "IDT.QMClosure.GaussianIntegerQuadraticSelection.nat_orthogonal_pair",
        "IDT.QMClosure.GaussianIntegerQuadraticSelection.gaussian_integer_quadratic_selection"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "This module classifies a supplied function. Construction of that function from actual circuit probabilities is a separate obligation."] }

def nativeGaussianDyadicClosure : ResearchTask := {
  id := "native_gaussian_dyadic_closure"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "An actual finite native circuit, any finite wire type, marked source basis port and selected output."]
  conclusions := [
    "Every selected prepared amplitude has a Gaussian integer numerator and a power-of-two denominator.",
    "An existential residue relation propagates through every circuit constructor; the final statement forgets the residue proof device."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeGaussianDyadicClosure.lean"
      declarations := [
        "IDT.QMClosure.NativeGaussianDyadicClosure.native_output_gaussian_dyadic"] }]
  plannedArtifacts := []
  dependencies := ["native_dyadic_six_wire_obstruction"]
  limits := [
    "No probability law is used. This is closure of actual circuit outputs, not synthesis of all legal vectors or arbitrary complex preparations."] }

def nativeGaussianProbabilitySelection : ResearchTask := {
  id := "native_gaussian_probability_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The existing real-valued native probability-family Law: nonnegative normalized probabilities, prepared-state equality, output-permutation covariance, spectator-pair locality and preservation under all finite fresh-zero embeddings.",
    "Actual finite normalized native circuits prepared from a marked basis source. No extra calibration, scalar sufficiency, mixture, continuity or arbitrary-input probability field is supplied."]
  conclusions := [
    "Events are actual circuits in a canonical doubling tower. Literal padding compares levels without a cross-type relabel axiom.",
    "A Gaussian numerator witness has amplitude g/2^k and weighted probability 4^k*P. Actual real-half attenuation and same-source scalar sufficiency make that probability independent of the witness and exponent.",
    "Actual zero, unit, rotation and addition circuits supply every Gaussian integer witness independently of any chosen Law. The canonical squared-amplitude Law is not used in this construction.",
    "A two-block dilation followed by a selected pair produces i*(x-y)/2 and (x+y)/2 with total probability (Px+Py)/2. This gives the response parallelogram identity.",
    "Normalization, phase invariance and Gaussian integer classification select the numerator response. The original circuit itself witnesses its Gaussian-dyadic output, so P(c,i)=normSq(cstate_i) for every actual finite native event.",
    "Every two supplied Laws have extensionally identical probability fields. Agreement with canonicalLaw is a corollary after independent selection."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeGaussianResponse.lean"
      declarations := [
        "IDT.QMClosure.NativeGaussianResponse.exists_common_level",
        "IDT.QMClosure.NativeGaussianResponse.event_amplitude_sufficiency",
        "IDT.QMClosure.NativeGaussianResponse.weighted_independent",
        "IDT.QMClosure.NativeGaussianResponse.exists_witness_sum_difference",
        "IDT.QMClosure.NativeGaussianResponse.all_numerators_realizable",
        "IDT.QMClosure.NativeGaussianResponse.response_native_output",
        "IDT.QMClosure.NativeGaussianResponse.response_zero",
        "IDT.QMClosure.NativeGaussianResponse.response_one",
        "IDT.QMClosure.NativeGaussianResponse.response_rotate",
        "IDT.QMClosure.NativeGaussianResponse.response_parallelogram"] },
    { sourcePath := "Proofs/QMClosure/NativeProbabilityUniqueness.lean"
      declarations := [
        "IDT.QMClosure.NativeProbabilityUniqueness.response_eq_gaussian_norm",
        "IDT.QMClosure.NativeProbabilityUniqueness.native_probability_eq_normSq",
        "IDT.QMClosure.NativeProbabilityUniqueness.native_probabilities_equal",
        "IDT.QMClosure.NativeProbabilityUniqueness.probability_fields_equal",
        "IDT.QMClosure.NativeProbabilityUniqueness.native_probability_eq_canonical"] }]
  plannedArtifacts := []
  dependencies := [
    "native_coherent_scalar_sufficiency", "gaussian_integer_quadratic_selection",
    "native_gaussian_dyadic_closure"]
  limits := [
    "This is universal over actual finite native basis-prepared words under Law, not a finite numerical scan. The all-width probability contract remains a premise.",
    "It does not derive Law from IDT primitives, assert physical gate or vacuum availability, or construct actual outcomes.",
    "Arbitrary complex preparations, general measurement domains, mixed-state reconstruction, original physical Born closure and full QM remain outside this theorem.",
    "The raw-carrier transfer and weaker probability-codomain adapter are separate pending obligations."] }

def nativeHyperrealProbabilityWall : ResearchTask := {
  id := "native_hyperreal_probability_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the hyperreal probability codomain with its explicit positive infinitesimal epsilon. Keep the same six finite native structural conditions.",
    "For every standard complex amplitude z, assign (1-epsilon)*normSq(z)+epsilon*Re(z)."]
  conclusions := [
    "Every nonzero standard amplitude has strictly positive readout: its positive standard squared norm dominates the infinitesimal correction. Zero has zero readout.",
    "Coherent-sum and squared-norm conservation give normalization for every actual native basis preparation. Scalar dependence supplies prepared-state equality, covariance, locality and vacuum compatibility.",
    "The separate HyperrealContract satisfies all six structural conditions; all actual basis-state preparations are calibrated.",
    "The word (01,02) has output-zero amplitude i/2. Its literal fresh split has retained amplitude (-1+i)/4 and nonzero probability defect -epsilon/4 relative to half its old probability.",
    "Thus arbitrary ordered-field probabilities cannot simply replace the real/Archimedean codomain in the exact selection theorem."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeHyperrealProbabilityWall.lean"
      declarations := [
        "IDT.QMClosure.NativeHyperrealProbabilityWall.response_positive",
        "IDT.QMClosure.NativeHyperrealProbabilityWall.probability_normalized",
        "IDT.QMClosure.NativeHyperrealProbabilityWall.hyperreal_contract",
        "IDT.QMClosure.NativeHyperrealProbabilityWall.probability_basis_calibration",
        "IDT.QMClosure.NativeHyperrealProbabilityWall.witness_amplitude",
        "IDT.QMClosure.NativeHyperrealProbabilityWall.witness_split_amplitude",
        "IDT.QMClosure.NativeHyperrealProbabilityWall.retained_halving_defect",
        "IDT.QMClosure.NativeHyperrealProbabilityWall.native_split_not_half"] }]
  plannedArtifacts := []
  dependencies := ["native_vacuum_probability_family", "native_binary_refinement_selection"]
  limits := [
    "This is not an inhabitant of real-valued Law, a physical probability proposal or an experimental distinction. Global minimality of Archimedeanness is not asserted.",
    "A separate analytic real-valued cutoff control is nonnegative for words with at most L pair gates when 0 <= t <= 2^(-L)/(1+2^(-L)); its bounded grammar is not closed under unlimited continuation. This cutoff statement has no checked artifact here."] }

def nativeArchimedeanProbability : ResearchTask := {
  id := "native_archimedean_probability"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "LawOver has exactly the six native probability-family fields with an additive ordered carrier and a chosen normalization element one.",
    "Generic transport requires a monotone additive map to the reals preserving one; pullback uniqueness additionally requires injectivity.",
    "The checked specialization assumes an Archimedean linearly ordered additive commutative group with a distinguished positive one. No multiplication or division operation is supplied on it."]
  conclusions := [
    "All six fields transport to the checked real Law without alteration. Real probability selection gives the squared-amplitude value after the chosen embedding.",
    "An injective normalized additive order map transfers probability uniqueness back to the original carrier.",
    "Mathlib's Archimedean embedding supplies that map with precisely the stated additive group, linear order and positive-unit assumptions.",
    "For every actual Gaussian witness g/2^k, the intrinsic identity is (4^k) times P by natural repeated addition equals (Re(g)^2+Im(g)^2) times one by integer repeated addition."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeArchimedeanProbability.lean"
      declarations := [
        "IDT.QMClosure.NativeArchimedeanProbability.LawOver.toReal",
        "IDT.QMClosure.NativeArchimedeanProbability.mapped_native_probability_eq_normSq",
        "IDT.QMClosure.NativeArchimedeanProbability.native_probabilities_equal_of_injective",
        "IDT.QMClosure.NativeArchimedeanProbability.LawOver.archimedeanToReal",
        "IDT.QMClosure.NativeArchimedeanProbability.embedded_native_probability_eq_normSq",
        "IDT.QMClosure.NativeArchimedeanProbability.native_probabilities_equal",
        "IDT.QMClosure.NativeArchimedeanProbability.native_probability_denominator_identity"] }]
  plannedArtifacts := []
  dependencies := ["native_gaussian_probability_selection"]
  limits := [
    "Conditional uniqueness does not assert that every such carrier admits a LawOver; integers cannot supply the required halves.",
    "No field, rational scalar action, topology or completeness of the probability carrier is assumed. Real completeness is auxiliary embedding mathematics.",
    "Only the native probability codomain is weakened. Earlier raw positive weights and Hilbert completion may still require real scalars.",
    "Linear order is a sufficient contract, not a global minimality assertion; arbitrary partial orders require a separate separation argument."] }

def rawNativeDyadicSemantics : ResearchTask := {
  id := "raw_native_dyadic_semantics"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The existing RawOperationalHilbert.Data and its constructed additive carrier, additive half H, phase J and normalized operation.",
    "Native circuits lift constructor by constructor and start with one raw reference v and the chosen raw zero on the other wires."]
  conclusions := [
    "Additive H is inverse to doubling, so repeated multiplication by a power of two is injective on the reconstructed carrier.",
    "Each actual scalar output has a Gaussian numerator g and denominator 2^k correlated with the exact raw output H iterated k times on Re(g)*v+Im(g)*J(v).",
    "Equal scalar coefficients imply literal equal raw outputs without feature injectivity, feature-quotient probability descent, or positive reference weight.",
    "Equal complete scalar prepared arrays therefore give equal complete raw prepared arrays on the generated native domain."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawNativeDyadicSemantics.lean"
      declarations := [
        "IDT.QMClosure.RawNativeDyadicSemantics.halfPower_two_pow",
        "IDT.QMClosure.RawNativeDyadicSemantics.two_pow_nsmul_injective",
        "IDT.QMClosure.RawNativeDyadicSemantics.native_output_gaussian_correlated",
        "IDT.QMClosure.RawNativeDyadicSemantics.related_raw_unique",
        "IDT.QMClosure.RawNativeDyadicSemantics.same_amplitude_same_raw_output",
        "IDT.QMClosure.RawNativeDyadicSemantics.scalar_prepared_eq_raw"] }]
  plannedArtifacts := []
  dependencies := ["raw_native_scalar_circuit_bridge", "native_gaussian_probability_selection"]
  limits := [
    "All algebra is reconstructed from the raw contract. Only powers-of-two torsion is excluded; arbitrary odd torsion is not excluded here.",
    "The normalized operation may differ from the original raw operation. Its physical availability and normalization control remain supplied.",
    "Raw probability normalization, positivity, covariance, spectator locality and all-width vacuum compatibility remain separate conditions. Null references and all-null weights are allowed by this semantics theorem."] }

def rawNativeProbabilitySelection : ResearchTask := {
  id := "raw_native_probability_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A fixed RawOperationalHilbert.Data and raw reference v; circuit words are syntax labels interpreted by their lifted normalized raw operations.",
    "A RawLaw with the same six structural fields, using equality of complete raw prepared arrays for its prepared-state field."]
  conclusions := [
    "Exact scalar-to-raw prepared equality supplies the sole nontrivial field of RawLaw.toScalarLaw.",
    "Conditional native probability selection gives the scalar squared amplitude without a feature-descent or selected-amplitude probability premise.",
    "Raw output weight equals P times reference weight, including null references. Only the ratio formula requires strictly positive reference weight.",
    "The probability fields of any two supplied RawLaw instances agree extensionally."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawNativeProbabilitySelection.lean"
      declarations := [
        "IDT.QMClosure.RawNativeProbabilitySelection.RawLaw.toScalarLaw",
        "IDT.QMClosure.RawNativeProbabilitySelection.raw_probability_eq_normSq",
        "IDT.QMClosure.RawNativeProbabilitySelection.raw_probability_weight_identity",
        "IDT.QMClosure.RawNativeProbabilitySelection.raw_probability_eq_weight_ratio",
        "IDT.QMClosure.RawNativeProbabilitySelection.probability_fields_equal"] }]
  plannedArtifacts := []
  dependencies := ["raw_native_dyadic_semantics", "native_gaussian_probability_selection"]
  limits := [
    "Conditional uniqueness does not supply existence of a RawLaw for an arbitrary reference or raw model.",
    "The circuit syntax has raw semantics; no arbitrary scalar raw preparation is imported. The normalized raw gate may differ from the original operation.",
    "The six probability fields, physical gate/vacuum availability, actual-event generation and original Born/QM obligations remain separate."] }

def rawNativeProbabilityExistence : ResearchTask := {
  id := "raw_native_probability_existence"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The fixed raw operational contract, reconstructed normalized native circuits and one reference v.",
    "RawLaw retains exactly its six all-width structural fields and literal raw prepared-state equivalence."]
  conclusions := [
    "Nonempty RawLaw is equivalent to injectivity of the Gaussian action on the chosen reference.",
    "Equivalently, the reference has infinite additive order in the reconstructed group; no whole-carrier torsion-freeness is required.",
    "Necessity uses actual attenuated Gaussian numerator events, equal raw coordinate swaps and comparison with fresh zero ports.",
    "Sufficiency clears dyadic denominators and transfers the separate canonical scalar law through exact raw equality.",
    "Positive reference weight suffices; the literal zero reference cannot support this RawLaw."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawNativeProbabilityExistence.lean"
      declarations := [
        "IDT.QMClosure.RawNativeProbabilityExistence.raw_zero_probability_zero",
        "IDT.QMClosure.RawNativeProbabilityExistence.gaussianAction_kernel_trivial_of_rawLaw",
        "IDT.QMClosure.RawNativeProbabilityExistence.related_scalar_unique",
        "IDT.QMClosure.RawNativeProbabilityExistence.canonicalRawLaw",
        "IDT.QMClosure.RawNativeProbabilityExistence.rawLaw_nonempty_iff_gaussianAction_injective",
        "IDT.QMClosure.RawNativeProbabilityExistence.gaussianAction_injective_iff_referenceInfiniteOrder",
        "IDT.QMClosure.RawNativeProbabilityExistence.rawLaw_nonempty_iff_referenceInfiniteOrder",
        "IDT.QMClosure.RawNativeProbabilityExistence.rawLaw_nonempty_of_positive_weight",
        "IDT.QMClosure.RawNativeProbabilityExistence.no_rawLaw_zero"] }]
  plannedArtifacts := []
  dependencies := ["raw_native_dyadic_semantics", "raw_native_probability_selection"]
  limits := [
    "The downstream consistency witness is not a premise of the already checked conditional selector.",
    "Positive reference weight is sufficient; necessity of positive weight is not asserted. Zero reference and all-null weight cases are distinct.",
    "No physical probability existence, actual-event mechanism or original-gate uniqueness follows."] }

def originalGateProbabilityWall : ResearchTask := {
  id := "original_gate_probability_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Explicit complex-pair raw model: original gate is N in the first sector and minus N in the second; W is the sum of sector norm squares and reference is (1,1).",
    "The original-gate probability grammar uses actual pair operations, output permutations and composition, with exactly the analogous six all-width fields."]
  conclusions := [
    "The explicit rawData satisfies square-swap, global mediality and positive conserved W. Its reconstructed normalized operation is N on both sectors and differs from the original operation.",
    "Every sector weight t in [0,1] supplies all six structural probability fields for every finite original-gate circuit.",
    "The actual three-gate word 01;02;12 gives port-one probability (1+4t)/8 while the supplied W ratio is 3/8; agreement holds exactly at t=1/2.",
    "Interior parameters 1/4 and 3/4 give probabilities 1/4 and 1/2 with strictly positive raw readouts. The nonuniqueness uses no null-weight loophole."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/OriginalGateProbabilityWall.lean"
      declarations := [
        "IDT.QMClosure.OriginalGateProbabilityWall.rawData",
        "IDT.QMClosure.OriginalGateProbabilityWall.normalized_operation",
        "IDT.QMClosure.OriginalGateProbabilityWall.original_differs_from_normalized",
        "IDT.QMClosure.OriginalGateProbabilityWall.law",
        "IDT.QMClosure.OriginalGateProbabilityWall.supplied_weight_positive",
        "IDT.QMClosure.OriginalGateProbabilityWall.witness_port_one",
        "IDT.QMClosure.OriginalGateProbabilityWall.witness_probability_eq_ratio_iff",
        "IDT.QMClosure.OriginalGateProbabilityWall.original_probability_nonunique",
        "IDT.QMClosure.OriginalGateProbabilityWall.quarter_not_weight_ratio",
        "IDT.QMClosure.OriginalGateProbabilityWall.three_quarter_not_weight_ratio",
        "IDT.QMClosure.OriginalGateProbabilityWall.alternative_readouts_strictly_positive"] }]
  plannedArtifacts := []
  dependencies := ["raw_operational_hilbert_facade", "raw_native_probability_selection"]
  limits := [
    "This countermodel restricts transfer to the original gate; normalized-only conditional uniqueness is unaffected.",
    "Mixed original/normalized grammars and additional internal operations are not formalized in this module.",
    "This is a mathematical freedom in invariant-sector weights, not a physical choice of t or a full Born/QM result."] }

def weightFreeRawProbability : ResearchTask := {
  id := "weight_free_raw_probability"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Only a raw chosen zero, complete binary operation, exact square-swap law and global first-channel mediality.",
    "The unchanged six-field all-width raw probability law for reconstructed normalized native words.",
    "An explicit diagonal-transparency law only when identifying the reconstructed gate with the original operation."]
  conclusions := [
    "The identically zero auxiliary weight completes the four-field operational data to the checked raw facade without a supplied weight premise.",
    "An evaluator on arbitrary raw functions agrees literally with the reconstructed normalized native arrays without supplying algebra on the raw type.",
    "Conditional probability selection, field uniqueness and exact reference-infinite-order existence transfer to this weight-free contract.",
    "Erasing an arbitrary compatible weight preserves the reconstructed group, normalized gate and literal prepared arrays; the probability-law types are equivalent with identical probability fields.",
    "Under explicit diagonal transparency, the normalized operation and literal original evaluator coincide."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/WeightFreeRawProbability.lean"
      declarations := [
        "IDT.QMClosure.WeightFreeRawProbability.RawOperationalData",
        "IDT.QMClosure.WeightFreeRawProbability.evalRaw",
        "IDT.QMClosure.WeightFreeRawProbability.rawPrepared_eq_prepared",
        "IDT.QMClosure.WeightFreeRawProbability.probability_eq_normSq",
        "IDT.QMClosure.WeightFreeRawProbability.probability_fields_equal",
        "IDT.QMClosure.WeightFreeRawProbability.law_nonempty_iff_reference_infiniteOrder",
        "IDT.QMClosure.WeightFreeRawProbability.erase_weight_rawPrepared",
        "IDT.QMClosure.WeightFreeRawProbability.weightErasureEquiv",
        "IDT.QMClosure.WeightFreeRawProbability.normalizedOperation_eq_original",
        "IDT.QMClosure.WeightFreeRawProbability.prepared_eq_original"] }]
  plannedArtifacts := []
  dependencies := ["raw_native_probability_existence", "raw_native_probability_selection"]
  limits := [
    "The auxiliary zero-weight feature space is trivial; probabilities respect literal raw equality, not equality of those features.",
    "No positive norm on the full carrier, physical observability, physical actualization, or justification of the six fields is asserted.",
    "Diagonal transparency is an extra condition for the original-gate case; the original-gate countermodel excludes removing it without replacement."] }

def sourceLocalOriginalSemantics : ResearchTask := {
  id := "source_local_original_semantics"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Retain r:WeightFreeRawProbability.RawOperationalData V with global square-swap and global first-channel mediality on all raw inputs. Write T=r.operation, m=MedialSwapRoot.firstChannel T, g=DiagonalNormalization.diagonal m, N=r.normalizedOperation and G=Prod.map g g.",
    "Source-local semantic transfer additionally assumes g(r.chosenZero)=r.chosenZero and g(v)=v for the one chosen source reference v. No weight, Hilbert structure, infinite reference order, probability Law or physically available unary g is supplied to the core.",
    "GenericOriginalLaw uses the same Native syntax and unchanged six-field all-width structural contract as WeightFreeRawProbability.Law; only prepared_eq is formulated with the existing WeightFreeRawProbability.originalPrepared."]
  conclusions := [
    "Parent-accepted kernel-checked source-local contract: the retained raw laws imply g composed with g is identity, g(m(x,y))=m(g(x),g(y)), and N=G composed with T=T composed with G. These identities do not require any chosen-zero fixed-point premise.",
    "Square-swap implies T is injective. Consequently N(x,y)=T(x,y) if and only if g(x)=x and g(y)=y.",
    "Pointwise g-fixed input arrays remain g-fixed under the original raw evaluator, and original and normalized evaluators agree as complete arrays on every such input and native word. The two fixed-point assumptions therefore give equality of all full source-generated prepared arrays.",
    "Exact structural characterization: both the chosen zero and source reference are g-fixed if and only if originalPrepared and prepared agree as full arrays for source 0 and the single pair 0 1 word on Fin 2, if and only if they agree for every finite wire type, source index and native word.",
    "Under the two fixed-point premises, GenericOriginalLaw and WeightFreeRawProbability.Law convert in both directions and form an equivalence preserving the entire identical probability field. Conditional selection and extensional field uniqueness transfer through the existing probability_eq_normSq theorem without a canonicalLaw premise.",
    "Under these same premises, Nonempty (GenericOriginalLaw r v) is equivalent to ReferenceInfiniteOrder r v through the existing weight-free existence criterion. The fixed-point assumptions alone do not construct a law.",
    "Strictness control: reuse OriginalGateProbabilityWall.operation on complex pairs, whose g(zPlus,zMinus)=(zPlus,-zMinus). Zero (0,0) and source (1,0) are fixed although global diagonal transparency fails at (0,1). The existing mixed source (1,1) is not fixed, leaving its original-gate probability nonuniqueness wall intact.",
    "Chosen-zero independence control: with the same square-swap and medial operation, choose zero (0,1) and source (1,0). The source is fixed but the chosen zero is not, and the one-pair original and normalized prepared arrays differ."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/SourceLocalOriginalSemantics.lean"
      declarations := [
        "IDT.QMClosure.SourceLocalOriginalSemantics.rawLaws",
        "IDT.QMClosure.SourceLocalOriginalSemantics.g",
        "IDT.QMClosure.SourceLocalOriginalSemantics.G",
        "IDT.QMClosure.SourceLocalOriginalSemantics.g_involutive",
        "IDT.QMClosure.SourceLocalOriginalSemantics.g_map",
        "IDT.QMClosure.SourceLocalOriginalSemantics.operation_injective",
        "IDT.QMClosure.SourceLocalOriginalSemantics.normalized_eq_after",
        "IDT.QMClosure.SourceLocalOriginalSemantics.operation_G",
        "IDT.QMClosure.SourceLocalOriginalSemantics.normalized_eq_before",
        "IDT.QMClosure.SourceLocalOriginalSemantics.gate_eq_iff",
        "IDT.QMClosure.SourceLocalOriginalSemantics.evalRaw_fixed",
        "IDT.QMClosure.SourceLocalOriginalSemantics.evalRaw_eq_on_fixed",
        "IDT.QMClosure.SourceLocalOriginalSemantics.basisInput_fixed",
        "IDT.QMClosure.SourceLocalOriginalSemantics.originalPrepared_eq_prepared",
        "IDT.QMClosure.SourceLocalOriginalSemantics.twoPortWord",
        "IDT.QMClosure.SourceLocalOriginalSemantics.OnePairAgreement",
        "IDT.QMClosure.SourceLocalOriginalSemantics.FullAgreement",
        "IDT.QMClosure.SourceLocalOriginalSemantics.fixed_iff_onePairAgreement",
        "IDT.QMClosure.SourceLocalOriginalSemantics.fixed_iff_fullAgreement",
        "IDT.QMClosure.SourceLocalOriginalSemantics.onePairAgreement_iff_fullAgreement",
        "IDT.QMClosure.SourceLocalOriginalSemantics.GenericOriginalLaw",
        "IDT.QMClosure.SourceLocalOriginalSemantics.toNormalizedLaw",
        "IDT.QMClosure.SourceLocalOriginalSemantics.toOriginalLaw",
        "IDT.QMClosure.SourceLocalOriginalSemantics.lawEquiv",
        "IDT.QMClosure.SourceLocalOriginalSemantics.toNormalizedLaw_probability",
        "IDT.QMClosure.SourceLocalOriginalSemantics.toOriginalLaw_probability",
        "IDT.QMClosure.SourceLocalOriginalSemantics.probability_eq_normSq",
        "IDT.QMClosure.SourceLocalOriginalSemantics.probability_fields_equal",
        "IDT.QMClosure.SourceLocalOriginalSemantics.law_nonempty_iff_reference_infiniteOrder",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.PairCarrier",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.fixedData",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.vacuumMovedData",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.fixedSource",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.g_fixedData",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.g_vacuumMovedData",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.fixedData_zero_fixed",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.fixedData_source_fixed",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.fixedData_fullAgreement",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.fixedData_not_globally_transparent",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.mixed_source_not_fixed",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.vacuumMovedData_source_fixed",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.vacuumMovedData_zero_not_fixed",
        "IDT.QMClosure.SourceLocalOriginalSemantics.Controls.vacuumMovedData_onePair_disagrees"] }]
  plannedArtifacts := []
  dependencies := ["weight_free_raw_probability", "diagonal_normalization",
    "native_preparation_naturality", "original_gate_probability_wall"]
  limits := [
    "This source-local kernel result weakens global diagonal transparency only. It retains the global square-swap and first-channel mediality assumptions of RawOperationalData on every raw input.",
    "The necessary-and-sufficient fixed-point characterization concerns equality of complete original and normalized prepared arrays. It does not claim these premises are necessary for original-law uniqueness or existence in general.",
    "The diagonal g is a term-defined mathematical normalizer, not an available unary native gate. Checking g(v) by the expression T(v,v) does not grant free preparation of two copies of v.",
    "Agreement is restricted to the chosen fixed source and vacuum sector, with every retained array coordinate included. No all-carrier transparency, arbitrary raw-reference availability, original-gate physical interpretation, actualization or full QM closure is established."] }

def mixedControlProbabilityWall : ResearchTask := {
  id := "mixed_control_probability_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A finite complex four-coordinate raw model, regrouped as two outer sectors each containing two internal coordinates; reference is (e1,e2).",
    "Actual original pair gate, reconstructed normalized pair gate and unary outer-sector swap are syntax generators.",
    "The six structural kinds of probability laws include strengthened spectator locality for every supplied local generator, including unary exchange."]
  conclusions := [
    "Each internal-coordinate total remains invariant under every named control; induction gives conservation on every mixed finite word.",
    "A continuum of positive-definite responses weights those internal coordinates and satisfies all six law kinds at every finite width.",
    "The actual three-gate witness with an appended outer swap gives probabilities 1/4 and 1/2 versus supplied weight ratio 3/8.",
    "The unary swap changes the prepared raw state. The ambiguity therefore survives actual use of the added control as well as its availability."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/MixedControlProbabilityWall.lean"
      declarations := [
        "IDT.QMClosure.MixedControlProbabilityWall.rawData",
        "IDT.QMClosure.MixedControlProbabilityWall.normalizedGate_eq_operation",
        "IDT.QMClosure.MixedControlProbabilityWall.Mixed.preserves_readout",
        "IDT.QMClosure.MixedControlProbabilityWall.law",
        "IDT.QMClosure.MixedControlProbabilityWall.Law.spectator_pair",
        "IDT.QMClosure.MixedControlProbabilityWall.Law.spectator_swap",
        "IDT.QMClosure.MixedControlProbabilityWall.witnessWithSwap_port_one",
        "IDT.QMClosure.MixedControlProbabilityWall.witnessWithSwap_probability_eq_ratio_iff",
        "IDT.QMClosure.MixedControlProbabilityWall.mixed_probability_nonunique",
        "IDT.QMClosure.MixedControlProbabilityWall.alternative_readouts_strictly_positive"] }]
  plannedArtifacts := []
  dependencies := ["original_gate_probability_wall"]
  limits := [
    "This is an enriched grammar and locality contract, not the unchanged normalized-only Law.",
    "The result excludes these named controls as a sufficient selection principle, not every conceivable additional control.",
    "The explicit finite-dimensional quadratic readouts are positive definite; no null-weight loophole is required."] }

def rawDiagonalDecomposition : ResearchTask := {
  id := "raw_diagonal_decomposition"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The existing raw operational data and its reconstructed group, phase, half and positive quadratic weight.",
    "No assumption that the original diagonal fixes the chosen zero; its offset may be a null raw direction."]
  conclusions := [
    "The original diagonal is D*x+t, where D is an additive involution commuting with phase and half, W(t)=0 and D(t)=-t.",
    "The null center half(t) is fixed by the diagonal; literal translation by this center conjugates the original operation to an additive one.",
    "Complementary projectors half(id+D) and half(id-D) give an additive equivalence with the product of the two sign subgroups.",
    "Opposite sign subgroups are orthogonal for the supplied weight, Hermitian kernel and constructed feature inner product.",
    "The original positive projection is normalized mixing; the negative projection is negative normalized mixing plus the retained offset in both outputs."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawDiagonalDecomposition.lean"
      declarations := [
        "IDT.QMClosure.RawDiagonalDecomposition.linearDiagonal_apply",
        "IDT.QMClosure.RawDiagonalDecomposition.linearDiagonal_involutive",
        "IDT.QMClosure.RawDiagonalDecomposition.linearDiagonal_phase",
        "IDT.QMClosure.RawDiagonalDecomposition.fixedCenter_null",
        "IDT.QMClosure.RawDiagonalDecomposition.diagonal_fixedCenter",
        "IDT.QMClosure.RawDiagonalDecomposition.centeredOperation_conjugacy",
        "IDT.QMClosure.RawDiagonalDecomposition.splitEquiv",
        "IDT.QMClosure.RawDiagonalDecomposition.weight_split",
        "IDT.QMClosure.RawDiagonalDecomposition.plus_minus_kernel",
        "IDT.QMClosure.RawDiagonalDecomposition.plus_minus_inner",
        "IDT.QMClosure.RawDiagonalDecomposition.original_sector_decomposition"] }]
  plannedArtifacts := []
  dependencies := ["raw_operational_hilbert_facade", "diagonal_normalization", "original_gate_probability_wall"]
  limits := [
    "This structure theorem does not classify all probability laws or prove arbitrary circuit synthesis.",
    "Null translation is retained for exact raw statements; no feature injectivity or whole-carrier torsion-freeness is supplied.",
    "The mathematical decomposition supplies no physical sector exchange, preparation procedure, irreducibility or calibration."] }

def nativeProbabilityPremiseIndependence : ResearchTask := {
  id := "native_probability_premise_independence"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The scalar native circuit grammar and the exact six-field real all-width Law contract, considered one omitted field at a time."]
  conclusions := [
    "The six standalone requirement predicates jointly hold exactly when an existing Law has the same probability field.",
    "For each requirement there is a field satisfying the other five and violating the selected one.",
    "The witnesses are real amplitude, zero, syntax-based pair averaging, fixed source delta, renormalized squared structural weights and uniform output distribution.",
    "The averaging interpreter has a literal all-width construction and padding proof; its four-gate witness has the same scalar preparation as identity but different probabilities."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeProbabilityPremiseIndependence.lean"
      declarations := [
        "IDT.QMClosure.NativeProbabilityPremiseIndependence.all_holds_iff_law",
        "IDT.QMClosure.NativeProbabilityPremiseIndependence.realPart_holdsExcept",
        "IDT.QMClosure.NativeProbabilityPremiseIndependence.zero_holdsExcept",
        "IDT.QMClosure.NativeProbabilityPremiseIndependence.averaging_holdsExcept",
        "IDT.QMClosure.NativeProbabilityPremiseIndependence.fixedSource_holdsExcept",
        "IDT.QMClosure.NativeProbabilityPremiseIndependence.contextual_holdsExcept",
        "IDT.QMClosure.NativeProbabilityPremiseIndependence.uniform_holdsExcept",
        "IDT.QMClosure.NativeProbabilityPremiseIndependence.six_conditions_irredundant"] }]
  plannedArtifacts := []
  dependencies := ["native_gaussian_probability_selection", "native_contextual_probability_control"]
  limits := [
    "Logical irredundance is not a claim of globally minimal or physically inevitable axioms.",
    "The scalar-law theorem is not automatically an independence theorem for every arbitrary raw carrier and reference.",
    "The signed real-amplitude field is a mathematical omission control, not a physical probability proposal."] }

def rawNetworkMedialWall : ResearchTask := {
  id := "raw_network_medial_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For the general equivalence, a complete raw operation with square-swap; row and column actions on a two-by-two array overlap on every wire.",
    "For the countermodel, a fixed four-state table with weights (0,1,1,2), transparent diagonal and reference 3 of weight 2."]
  conclusions := [
    "Full row/column commutation is equivalent to first-channel mediality under square-swap; the top-left implication itself needs no square law.",
    "The fixed table satisfies square-swap, diagonal transparency and weight conservation. Its declared reference splits into probabilities (1/2,1/2).",
    "A generic raw evaluator conservation theorem constructs all six probability fields from a nonnegative conserved normalized readout without raw additive structure or mediality.",
    "The four-state law exists at every finite width, but the two-gate word gives (1/2,1/2,0) against standard native norms (1/4,1/2,1/4).",
    "An actual five-wire reference preparation supplies the noncommuting network inputs while retaining a spectator branch; the network orders give selected probabilities 1/2 and 0."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawNetworkMedialWall.lean"
      declarations := [
        "IDT.QMClosure.RawNetworkMedialWall.rowColumnCommutes_iff_medial",
        "IDT.QMClosure.RawNetworkMedialWall.evalRaw_preserves_readout",
        "IDT.QMClosure.RawNetworkMedialWall.readoutLaw",
        "IDT.QMClosure.RawNetworkMedialWall.gate_square",
        "IDT.QMClosure.RawNetworkMedialWall.gate_transparent",
        "IDT.QMClosure.RawNetworkMedialWall.weight_conserved",
        "IDT.QMClosure.RawNetworkMedialWall.gate_not_medial",
        "IDT.QMClosure.RawNetworkMedialWall.declared_reference_balanced",
        "IDT.QMClosure.RawNetworkMedialWall.other_vacuum_inputs_unbalanced",
        "IDT.QMClosure.RawNetworkMedialWall.finiteModelLaw",
        "IDT.QMClosure.RawNetworkMedialWall.balanced_reference_does_not_select_native_normSq",
        "IDT.QMClosure.RawNetworkMedialWall.prepared_network_readout_difference"] }]
  plannedArtifacts := []
  dependencies := ["weight_free_raw_probability", "raw_medial_addition"]
  limits := [
    "Balance holds for the declared reference, not every nonzero vacuum input; the artifact explicitly exhibits the other unbalanced inputs.",
    "These are raw-model probability fields, not an inhabitant of the scalar native Law or the medial RawLaw.",
    "Commutation of disjoint local gates does not supply the overlapping-network interchange law.",
    "The result does not select a physical primitive or refute norm-squared readout for arbitrary quantum dynamics."] }

def continuousBalancedNonmedialWall : ResearchTask := {
  id := "continuous_balanced_nonmedial_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "An explicit nonlinear operation on complex pairs with supplied norm-squared readout, used only as a mathematical countermodel.",
    "For s=x+y and d=x-y, let R=normSq(s)+normSq(d), k=1+normSq(s)/R, A=(k+1/k)/2, B=(1/k-k)/2 and q=s/conj(s).",
    "The frozen-coefficient real-linear turn is M=i*(A*d+B*q*conj(d)); normalize it to the radius of d and recover the two outputs from their sum s and normalized difference."]
  conclusions := [
    "The frozen turn squares to minus identity, while radius normalization preserves k at the next step; the complete gate therefore squares to swap.",
    "The gate is diagonal-transparent, conserves coherent sum and the sum of squared norms, and agrees exactly with the standard native gate on every vacuum input.",
    "The full gate is continuous and jointly complex-homogeneous, including its zero cases.",
    "For medial inputs (1,1,i,1), the sides are (1+i)/2 and 1+i/2-(52+17i)/(2*sqrt(2993)), which differ. The same exact witness also rejects flexibility and the quadratical identity.",
    "With unit reference at source wire 0, the actual three-gate word 01;02;12 gives selected squared norm and raw probability 3/8+121/(8*sqrt(2993)) at wire 1, instead of standard native 5/8.",
    "The supplied norm-squared readout constructs all six raw-semantic probability fields at every finite width."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/BalancedNonmedialMixerCore.lean"
      declarations := [
        "IDT.QMClosure.BalancedNonmedialMixerCore.k_one_le",
        "IDT.QMClosure.BalancedNonmedialMixerCore.k_le_two",
        "IDT.QMClosure.BalancedNonmedialMixerCore.frozenTurn_square_actual",
        "IDT.QMClosure.BalancedNonmedialMixerCore.rotated_normSq",
        "IDT.QMClosure.BalancedNonmedialMixerCore.rotated_square",
        "IDT.QMClosure.BalancedNonmedialMixerCore.gate_square",
        "IDT.QMClosure.BalancedNonmedialMixerCore.gate_transparent",
        "IDT.QMClosure.BalancedNonmedialMixerCore.gate_sum",
        "IDT.QMClosure.BalancedNonmedialMixerCore.gate_conserves",
        "IDT.QMClosure.BalancedNonmedialMixerCore.native_vacuum_right",
        "IDT.QMClosure.BalancedNonmedialMixerCore.native_vacuum_left"] },
    { sourcePath := "Proofs/QMClosure/BalancedNonmedialMixerRegularity.lean"
      declarations := [
        "IDT.QMClosure.BalancedNonmedialMixerRegularity.turn_regular_form",
        "IDT.QMClosure.BalancedNonmedialMixerRegularity.continuous_rotated",
        "IDT.QMClosure.BalancedNonmedialMixerRegularity.continuous_gate",
        "IDT.QMClosure.BalancedNonmedialMixerRegularity.gate_joint_complex_homogeneity"] },
    { sourcePath := "Proofs/QMClosure/BalancedNonmedialMixerWitness.lean"
      declarations := [
        "IDT.QMClosure.BalancedNonmedialMixerWitness.gate_not_medial",
        "IDT.QMClosure.BalancedNonmedialMixerWitness.gate_not_flexible",
        "IDT.QMClosure.BalancedNonmedialMixerWitness.gate_not_quadratical",
        "IDT.QMClosure.BalancedNonmedialMixerWitness.gate_not_rowColumnCommutes",
        "IDT.QMClosure.BalancedNonmedialMixerWitness.rawLaw",
        "IDT.QMClosure.BalancedNonmedialMixerWitness.raw_probability_eq_own_normSq",
        "IDT.QMClosure.BalancedNonmedialMixerWitness.word_selected",
        "IDT.QMClosure.BalancedNonmedialMixerWitness.word_probability",
        "IDT.QMClosure.BalancedNonmedialMixerWitness.native_word_normSq",
        "IDT.QMClosure.BalancedNonmedialMixerWitness.raw_word_differs_from_native"] }]
  plannedArtifacts := []
  dependencies := ["raw_network_medial_wall"]
  limits := [
    "These checked statements concern one explicit mathematical countermodel, not a classification or physical realization of nonlinear dynamics.",
    "Only the frozen-coefficient turn squares to minus identity. Recomputing k after the unnormalized turn does not have that property.",
    "Homogeneity is joint scalar homogeneity, not additivity. Differentiability is not claimed.",
    "This is a nonlinear process/mediality wall, not a violation of norm-squared readout for the operation's own outputs.",
    "A separate four-wire marginal discrepancy has numerical evidence only. Any independent-party interpretation, causal conclusion or implication from no-signalling to mediality remains open."] }

def rawObservableMedialWall : ResearchTask := {
  id := "raw_observable_medial_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "An explicit product of the native complex mixer and the checked nonmedial four-state gate, with zero (0,0) and reference (1,3).",
    "The declared readout sees only the complex coordinate; observations use the existing arbitrary-reference one-hole context grammar."]
  conclusions := [
    "Checked construction: square-swap, transparency, all-input vacuum balance for the declared readout, conservation and a six-field literal-raw probability law coexist with failure of literal mediality.",
    "Projection to the complex coordinate commutes with every named circuit. Existing observational equivalence is exactly equality of that coordinate.",
    "The product inhabits the existing ObservedData contract; its observed quotient remains native and medial.",
    "The checked finite gate's five-wire single-source words lift to unequal raw arrays with common visible readouts (1/8,1/8,1/8,1/8,1/2), indistinguishable by subsequent declared readouts.",
    "A second conserved readout of the finite coordinate gives another six-field raw law, with probabilities 1/2 and zero on those observed-equivalent preparations. Literal prepared equality alone therefore does not imply observational probability descent.",
    "Immediate row-readout invariance follows from conservation; invariance after the other layer's analyzer is a separate equation."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawObservableMedialWall.lean"
      declarations := [
        "IDT.QMClosure.RawObservableMedialWall.gate_square",
        "IDT.QMClosure.RawObservableMedialWall.gate_transparent",
        "IDT.QMClosure.RawObservableMedialWall.all_vacuum_readouts_balanced",
        "IDT.QMClosure.RawObservableMedialWall.rawLaw",
        "IDT.QMClosure.RawObservableMedialWall.hiddenLaw",
        "IDT.QMClosure.RawObservableMedialWall.gate_not_medial",
        "IDT.QMClosure.RawObservableMedialWall.observationalEq_iff_visible_eq",
        "IDT.QMClosure.RawObservableMedialWall.observedData",
        "IDT.QMClosure.RawObservableMedialWall.prepared_raw_ne",
        "IDT.QMClosure.RawObservableMedialWall.prepared_readouts",
        "IDT.QMClosure.RawObservableMedialWall.padded_downstream_observationalEq",
        "IDT.QMClosure.RawObservableMedialWall.hiddenLaw_not_observationally_extensional",
        "IDT.QMClosure.RawObservableMedialWall.rowReadout_rows",
        "IDT.QMClosure.RawObservableMedialWall.row_order_eq_iff_after_analyzer"] }]
  plannedArtifacts := []
  dependencies := ["raw_network_medial_wall"]
  limits := [
    "The quotient is characterized by equivalence and projection theorems; no separate quotient-isomorphism object is packaged.",
    "Readout indistinguishability is relative to the supplied readout and named contexts, not all physical observations or all probability assignments.",
    "The result does not reject quotient mediality or assert topology or scalar homogeneity of the product carrier.",
    "Interpreting the overlapping row and column layers as independent physical subsystems remains a separate bridge."] }

def observedRawProbabilitySelection : ResearchTask := {
  id := "observed_raw_probability_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Existing ObservedData: supplied nonnegative conserved readout, zero-weight vacuum, observational square-swap and observational mediality in the declared context grammar.",
    "Observed first-output diagonal transparency for selection and uniqueness; quotient square-swap supplies the other diagonal output. The checked existence criterion does not need this transparency premise.",
    "A six-field all-width probability law whose prepared-equality field respects pointwise observational equivalence of actual raw prepared arrays."]
  conclusions := [
    "Checked conditional route: the quotient is diagonally transparent and its normalized circuit semantics equals the quotient of literal raw circuit semantics.",
    "Transport retains the supplied probability field exactly and allows existing native selection, absolute weight agreement and uniqueness without a positive-reference premise.",
    "The checked existence criterion is exactly positive reference weight even without transparency: normalized readout gives a separate witness, while observational equivalence of the reference to vacuum contradicts observational prepared consistency, singleton/two-wire normalization, permutation covariance and vacuum padding."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ObservedRawProbabilitySelection.lean"
      declarations := [
        "IDT.QMClosure.ObservedRawProbabilitySelection.quotient_transparent",
        "IDT.QMClosure.ObservedRawProbabilitySelection.rawPrepared_eq_class",
        "IDT.QMClosure.ObservedRawProbabilitySelection.Law.toQuotientLaw_probability",
        "IDT.QMClosure.ObservedRawProbabilitySelection.probability_eq_normSq",
        "IDT.QMClosure.ObservedRawProbabilitySelection.probability_weight_identity",
        "IDT.QMClosure.ObservedRawProbabilitySelection.probability_eq_weight_ratio",
        "IDT.QMClosure.ObservedRawProbabilitySelection.probability_fields_equal",
        "IDT.QMClosure.ObservedRawProbabilitySelection.normalizedReadoutLaw",
        "IDT.QMClosure.ObservedRawProbabilitySelection.no_law_of_reference_observational_zero",
        "IDT.QMClosure.ObservedRawProbabilitySelection.reference_positive",
        "IDT.QMClosure.ObservedRawProbabilitySelection.law_nonempty_iff_positive_weight"] }]
  plannedArtifacts := []
  dependencies := ["raw_observable_medial_wall", "weight_free_raw_probability"]
  limits := [
    "The null-reference contradiction uses only selected Law fields, but theorem signatures retain the bundled ObservedData contract; no separately generalized minimal-package theorem is asserted.",
    "Observational prepared equality is an explicit additional probability premise, not a consequence of literal prepared equality.",
    "Existence witnesses must remain downstream of conditional selection. Ratio formulas still require positive reference weight.",
    "Positive-weight necessity concerns this observational law, not arbitrary unquotiented RawLaw, whose reference condition is infinite additive order.",
    "No physical availability, exhaustive observation grammar, actual outcome generator, Born actualization or full QM closure follows."] }

def responseContextProbability : ResearchTask := {
  id := "response_context_probability"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A raw zero and two-output operation with a supplied response/signature map into an arbitrary type; contexts are the existing finite one-hole grammar with arbitrary raw references.",
    "Square-swap, first-channel mediality and first-output diagonal transparency hold modulo equality of signatures in every stated context.",
    "A real-valued six-field all-width probability law respects pointwise contextual equivalence of actual original-gate prepared arrays."]
  conclusions := [
    "Context plugging supplies congruence without a numerical weight, positivity, conservation or a supplied Hilbert feature map.",
    "The quotient supplies WeightFreeRawProbability.RawOperationalData. Transparency identifies original and normalized quotient semantics; both law adapters retain the identical probability field and form an equivalence of contracts.",
    "Conditional native selection and field uniqueness use the supplied law without an existence witness or reference-order premise. Under the same transparency premise, law existence is exactly infinite additive order of the quotient reference.",
    "A finite total contextual quotient forbids the law. A finite response alphabet alone does not: the native complex model with Boolean exact-zero signature has contextual equivalence exactly literal equality and an infinite quotient.",
    "The Boolean model transports any supplied native scalar law with its field unchanged; the canonical scalar law supplies a separate consistency witness at reference one.",
    "Constant signatures yield a singleton quotient and no law for any raw operation. An identity signature separates raw values already in the hole context; no separate identity-signature law-equivalence wrapper is packaged."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ResponseContextQuotient.lean"
      declarations := [
        "IDT.QMClosure.ResponseContextQuotient.output_congr",
        "IDT.QMClosure.ResponseContextQuotient.relation_le_responseEq",
        "IDT.QMClosure.ResponseContextQuotient.Data.quotientData",
        "IDT.QMClosure.ResponseContextQuotient.quotient_transparent",
        "IDT.QMClosure.ResponseContextQuotient.evalRaw_class",
        "IDT.QMClosure.ResponseContextQuotient.normalized_evalRaw_class"] },
    { sourcePath := "Proofs/QMClosure/ResponseNativeProbabilitySelection.lean"
      declarations := [
        "IDT.QMClosure.ResponseNativeProbabilitySelection.prepared_eq_class",
        "IDT.QMClosure.ResponseNativeProbabilitySelection.quotientLawEquiv",
        "IDT.QMClosure.ResponseNativeProbabilitySelection.Law.toQuotientLaw_probability",
        "IDT.QMClosure.ResponseNativeProbabilitySelection.fromQuotientLaw_probability",
        "IDT.QMClosure.ResponseNativeProbabilitySelection.probability_eq_normSq",
        "IDT.QMClosure.ResponseNativeProbabilitySelection.probability_fields_equal",
        "IDT.QMClosure.ResponseNativeProbabilitySelection.law_nonempty_iff_reference_infiniteOrder"] },
    { sourcePath := "Proofs/QMClosure/ResponseSignatureControls.lean"
      declarations := [
        "IDT.QMClosure.ResponseSignatureControls.finite_quotient_no_law",
        "IDT.QMClosure.ResponseSignatureControls.law_implies_infinite_quotient",
        "IDT.QMClosure.ResponseSignatureControls.identity_responseEq_iff_eq",
        "IDT.QMClosure.ResponseSignatureControls.constant_no_law",
        "IDT.QMClosure.ResponseSignatureControls.native_first_cancel_reference",
        "IDT.QMClosure.ResponseSignatureControls.native_responseEq_iff_eq",
        "IDT.QMClosure.ResponseSignatureControls.native_quotient_infinite",
        "IDT.QMClosure.ResponseSignatureControls.nativeLawOfScalar_probability",
        "IDT.QMClosure.ResponseSignatureControls.native_law_nonempty"] }]
  plannedArtifacts := []
  dependencies := ["weight_free_raw_probability", "observed_raw_probability_selection"]
  limits := [
    "Signature provenance independent of the desired conclusion is a scientific requirement, not a property enforced by Data. Encoding the target probability or representation into it is not a derivation.",
    "The signature is not automatically an individual deterministic measurement outcome; structural or statistical response data do not assign actual outcomes to every incompatible measurement.",
    "Observed mediality, transparency, probability consistency, real Archimedean values and the all-width contract remain premises; physical availability and detector dynamics remain open.",
    "Native words describe coherent preparations from one reference and raw vacua, not arbitrary physical states, transformations or independently unknown rays.",
    "The Boolean control supplies complex coordinates and the native gate as a mathematical model. Exact zero tests and arbitrary references do not establish finite-precision physical controls.",
    "Finite contextual quotient means finitely many response-equivalence classes of raw coherent preparations; it is not finite Hilbert dimension, finite output alphabet or a no-go theorem for arbitrary finite-state stochastic models.",
    "A finite battery yields a finite full contextual quotient only with finite responses and a proof that its equality is the full contextual congruence; bounded depth alone is neither finite nor automatically congruent.",
    "This transparent route does not subsume the weighted existence theorem without transparency.",
    "Outcome actualization and every standing matter-regime obligation remain open."] }

def responseSourceLocalProbability : ResearchTask := {
  id := "response_source_local_probability"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Retain d:ResponseContextQuotient.Data V Omega, a chosen source v, globally observed square-swap and first-channel mediality modulo full ResponseEq over the existing finite contexts with arbitrary fixed raw references. A response signature takes values in an arbitrary type; no weight or probability meaning is supplied.",
    "The initial response-law/original-quotient-law equivalence requires no diagonal transparency. The later source-local transfer assumes ResponseEq d.operation d.signature (d.operation (z,z)).1 z for z=d.chosenZero, and the same condition at v.",
    "Use the checked SourceLocalOriginalSemantics.GenericOriginalLaw on d.quotientData and d.classOf v, preserving its same six supplied fields and source-local boundary."]
  conclusions := [
    "Parent-accepted kernel-checked source-local response contract: originalPrepared d.quotientData (d.classOf v) s c is exactly the array fun i => d.classOf (ResponseNativeProbabilitySelection.prepared d v s c i), using evalRaw_class and the basis-input array. No local or global diagonal transparency is needed for this original-quotient evaluation identity.",
    "Pointwise full ResponseEq of two response-prepared arrays is equivalent to equality of their original-quotient prepared arrays through classOf_eq_iff_responseEq. ResponseNativeProbabilitySelection.Law d v and GenericOriginalLaw d.quotientData (d.classOf v) therefore form an equivalence preserving the entire identical probability field; the other five supplied law fields copy unchanged.",
    "The two source-local full ResponseEq premises imply that the reconstructed quotient diagonal fixes the quotient chosen zero and quotient source. SourceLocalOriginalSemantics then transports the original-quotient law to the normalized weight-free law without any global ObservedTransparent premise.",
    "Under both source-local premises, transfer conditional native normSq selection and extensional probability-field uniqueness. Separately, Nonempty (ResponseNativeProbabilitySelection.Law d v) is equivalent to ReferenceInfiniteOrder d.quotientData (d.classOf v). The fixed-class premises alone do not construct a law, and a zero-class source can preclude a law.",
    "Global ObservedTransparent implies both local premises, providing compatibility with the existing transparent theorem. Literal raw fixedness is not required. The theorem retains full contextual equality at both points; no replacement by bare signature equality is asserted.",
    "Strictness control: use an identity signature on the existing two-component original-gate operation, chosen zero (0,0), source (1,0). Full ResponseEq is literal equality already by the hole context; globally observed square-swap and mediality hold, both selected classes are diagonal-fixed, but global ObservedTransparent fails at (0,1). This separates the strength of sufficient hypotheses, not a necessary condition for probability-law uniqueness."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ResponseSourceLocalProbability.lean"
      declarations := [
        "IDT.QMClosure.ResponseSourceLocalProbability.originalPrepared_eq_class",
        "IDT.QMClosure.ResponseSourceLocalProbability.responseEq_iff_originalPrepared_eq",
        "IDT.QMClosure.ResponseSourceLocalProbability.OriginalLaw",
        "IDT.QMClosure.ResponseSourceLocalProbability.toOriginalLaw",
        "IDT.QMClosure.ResponseSourceLocalProbability.fromOriginalLaw",
        "IDT.QMClosure.ResponseSourceLocalProbability.originalLawEquiv",
        "IDT.QMClosure.ResponseSourceLocalProbability.toOriginalLaw_probability",
        "IDT.QMClosure.ResponseSourceLocalProbability.fromOriginalLaw_probability",
        "IDT.QMClosure.ResponseSourceLocalProbability.DiagonalFixed",
        "IDT.QMClosure.ResponseSourceLocalProbability.diagonalFixed_iff_quotient_fixed",
        "IDT.QMClosure.ResponseSourceLocalProbability.observedTransparent_diagonalFixed",
        "IDT.QMClosure.ResponseSourceLocalProbability.observedTransparent_source_local",
        "IDT.QMClosure.ResponseSourceLocalProbability.normalizedLawEquiv",
        "IDT.QMClosure.ResponseSourceLocalProbability.normalizedLawEquiv_probability",
        "IDT.QMClosure.ResponseSourceLocalProbability.normalizedLawEquiv_symm_probability",
        "IDT.QMClosure.ResponseSourceLocalProbability.probability_eq_normSq",
        "IDT.QMClosure.ResponseSourceLocalProbability.probability_fields_equal",
        "IDT.QMClosure.ResponseSourceLocalProbability.law_nonempty_iff_reference_infiniteOrder",
        "IDT.QMClosure.ResponseSourceLocalProbability.Controls.PairCarrier",
        "IDT.QMClosure.ResponseSourceLocalProbability.Controls.identity_responseEq_iff",
        "IDT.QMClosure.ResponseSourceLocalProbability.Controls.data",
        "IDT.QMClosure.ResponseSourceLocalProbability.Controls.fixedSource",
        "IDT.QMClosure.ResponseSourceLocalProbability.Controls.zero_fixed",
        "IDT.QMClosure.ResponseSourceLocalProbability.Controls.source_fixed",
        "IDT.QMClosure.ResponseSourceLocalProbability.Controls.not_globally_transparent",
        "IDT.QMClosure.ResponseSourceLocalProbability.Controls.source_local_without_global"] }]
  plannedArtifacts := []
  dependencies := ["response_context_probability", "source_local_original_semantics",
    "weight_free_raw_probability"]
  limits := [
    "Full contextual ResponseEq over arbitrary fixed raw references remains supplied. Recipe-only reference tests are not substituted, and arbitrary signatures need not reflect attenuation.",
    "This task weakens global observed transparency to two source-sector quotient conditions while retaining globally observed square-swap and first-channel mediality. The unconditional law equivalence still refers to original quotient semantics.",
    "The source-local fixed-class premises are sufficient for the stated transfer; they are not claimed necessary for response-law uniqueness or existence. Conditional selection and a separate law-existence criterion are distinct results.",
    "The signature is not supplied as a numerical weight or probability readout. A term such as T(v,v) supplies no physical test control or availability of two copies of v.",
    "Quotient semantics, source-sector algebra and structural probability consistency establish no physical reference availability, unknown-token processing, outcome actualization, detector dynamics, Hilbert premise or full QM closure."] }

def responseDiagonalSignatureWall : ResearchTask := {
  id := "response_diagonal_signature_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use exactly OriginalGateProbabilityWall.operation T on V=Complex x Complex, chosen zero (0,0), mixed reference v=(1,1), and signature W=OriginalGateProbabilityWall.weight=normSq(x.1)+normSq(x.2). The term-defined diagonal is g(x.1,x.2)=(x.1,-x.2).",
    "Use the existing full finite one-hole context grammar with arbitrary fixed raw references. W is a supplied mathematical signature, not asserted to be a probability readout or a physically available measurement.",
    "Retain the existing Native syntax and unchanged six-field OriginalGateProbabilityWall.OriginalLaw; no source availability, physical context implementation or free-copy premise is added."]
  conclusions := [
    "Checked countermodel: W((T(x,x)).1)=W(x) globally, while this bare signature invariance does not imply full contextual diagonal fixedness at the mixed reference.",
    "A checked cancellation-reference theorem uses a fixed raw reference tailored to x and shows full ResponseEq T W x y if and only if x=y. These arbitrary raw references are mathematical context parameters, not physically certified preparations.",
    "The checked explicit context C(x)=(T(x,(0,I))).1 separates v=(1,1) and g(v)=(1,-1): both initial signatures are 2, while W(C(v))=5/2 and W(C(g(v)))=1/2. Hence the mixed source is not contextually diagonal-fixed despite global bare W diagonal invariance.",
    "A checked structural Native-to-Original circuit adapter preserves full original prepared arrays and padding and transports the existing six-field OriginalLaw to the response-law contract without altering its probability field.",
    "Checked transport of quarterLaw and threeQuarterLaw supplies response laws. On source 0, the Native word pair 0 1; pair 0 2; pair 1 2 over Fin 3 gives port-1 probabilities 1/4 and 1/2, respectively.",
    "This checked wall refutes replacement of full contextual fixedness by bare signature invariance in the stated transfer route. It does not claim that source-local full contextual fixedness is necessary for general probability-law uniqueness or existence."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ResponseDiagonalSignatureWall.lean"
      declarations := [
        "IDT.QMClosure.ResponseDiagonalSignatureWall.responseData",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.diagonal_signature",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.responseEq_iff_eq",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.witness_context_diagonal",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.witness_context_source",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.source_not_responseEq_diagonal",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.toOriginal_eval",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.toOriginal_padCircuit",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.transportLaw",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.transportLaw_probability",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.quarter_probability",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.three_quarter_probability",
        "IDT.QMClosure.ResponseDiagonalSignatureWall.bare_diagonal_invariance_does_not_select"] }]
  plannedArtifacts := []
  dependencies := ["response_context_probability", "source_local_original_semantics",
    "original_gate_probability_wall"]
  limits := [
    "The signature W is not asserted to equal a probability law. Its diagonal invariance is a bare response identity, distinct from full contextual equivalence.",
    "The mathematical model supplies complex coordinates, T, W and arbitrary fixed raw references. No independent physical provenance, available cancellation reference, finite-resolution detector or physical gate implementation follows.",
    "This is a countermodel to a weakened sufficient-premise route, not a general necessity theorem for uniqueness, existence or every response model. No outcome actualization, unknown-token processing or full QM closure is established."] }

def responseRecipeContextReflection : ResearchTask := {
  id := "response_recipe_context_reflection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use d:ResponseContextQuotient.Data V Omega with arbitrary signature and globally observed square-swap and first-channel mediality modulo full ResponseEq. Assume full contextual diagonal fixedness at d.chosenZero and the chosen source v, as in ResponseSourceLocalProbability.DiagonalFixed.",
    "Use actual same-source Native Event recipes, a single recipe-reference context C, and scalar realizations E and F of that same C on recipes e and f. Define originalEvent using the actual original raw operation and all retained circuit outputs; define idealOriginalContext using that original T and the recipe-defined raw references.",
    "No probability Law, weight, infinite-order reference, global observed transparency, or bare-signature completeness is supplied. The fixed-class hypotheses concern full contextual equivalence, not only the hole signature."]
  conclusions := [
    "Checked quotient-class bridge: classOf of each original recipe event equals the normalized quotient rawEvent. The quotient zero and source are g-fixed, every retained source-generated intermediate quotient term stays g-fixed, and original and normalized evaluations agree as full quotient arrays.",
    "The checked quotient-class identity identifies classOf of idealOriginalContext with the existing normalized quotient rawIdealContext. Reference recipes and intermediates are all in the same fixed source sector; arbitrary raw source availability is not inferred.",
    "For the same recipe context C and its two scalar realizations E and F, the checked theorem equates full ResponseEq of their actual original recipe outputs U(E) and U(F) with full ResponseEq of I_C(e) and I_C(f). The equivalence transfers through quotient classes and the existing injective quotient halfPower at the common context attenuation order.",
    "This is reflection of equality of selected contextual classes at a common attenuation scale, not equality of complete unattenuated arrays, equality of circuit histories, a response-signature separation theorem, or an amplification operation."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ResponseRecipeContextReflection.lean"
      declarations := [
        "IDT.QMClosure.ResponseRecipeContextReflection.context_eval_class",
        "IDT.QMClosure.ResponseRecipeContextReflection.originalEvent_class",
        "IDT.QMClosure.ResponseRecipeContextReflection.rawEvent_fixed",
        "IDT.QMClosure.ResponseRecipeContextReflection.context_eval_eq_normalized",
        "IDT.QMClosure.ResponseRecipeContextReflection.idealOriginalContext_class",
        "IDT.QMClosure.ResponseRecipeContextReflection.original_realization_class",
        "IDT.QMClosure.ResponseRecipeContextReflection.realization_responseEq_iff",
        "IDT.QMClosure.ResponseRecipeContextReflection.realize_responseEq_iff"] }]
  plannedArtifacts := []
  dependencies := ["response_context_probability", "response_source_local_probability",
    "source_local_original_semantics", "native_recipe_context_realization"]
  limits := [
    "The checked reflection remains conditional on both full contextual source-sector fixedness premises and the existing scalar realization relation; it supplies no probability Law, weight, or infinite-order reference.",
    "The outer full ResponseEq still quantifies over arbitrary fixed raw references at every finite context nesting. Recipe-reference compilation does not replace that supplied contextual relation by a reachable-only or bare-signature relation.",
    "Only selected output classes are compared after retaining all circuits and ancillary outputs. No unknown-token copying, physical reference availability, apparatus implementation, detector robustness, actualization, or full QM closure follows."] }

def nativeRecipeObservationBoundary : ResearchTask := {
  id := "native_recipe_observation_boundary"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the concrete complex scalar native mixer, chosen zero 0, source 1 and the exact Boolean signature pointTest q z=decide(z=q), for arbitrary q. Full response contexts retain arbitrary fixed complex references.",
    "For the reachable-observation wall assume normSq(q)>1. Every native output at every finite width is from the same unit source and raw vacua; all recipe, compiler and ancillary outputs obey the existing output_normSq_le_one bound.",
    "For the positive companion, use known actual Event recipes e and t and the actual PairedSetting.differenceEvent circuit with selected amplitude I*(z-t)/2. The comparator retains its entire native circuit and all other outputs."]
  conclusions := [
    "Checked full-context control: Rq(x)=(1+I)*q-I*x gives mixer.first(y,Rq(x))=q+((1+I)/2)*(y-x). Therefore full ResponseEq for pointTest q is literal scalar equality for every q; the exact square-swap, mediality and transparency laws hold, and the full contextual quotient is infinite despite a Boolean signature alphabet.",
    "Checked transport preserves the entire probability field of any supplied scalar native Law in the response-law contract; canonicalLaw supplies only a separate consistency witness. This does not derive a law from the point-test signature.",
    "When normSq(q)>1, the signature is false on every native output at every width, including every reachable recipe-context compiler output and every ancillary output. Thus the complete family of these reachable observations does not separate even the distinct actual half/quarter recipe amplitudes, although their full ResponseEq classes differ.",
    "This concrete model refutes replacing arbitrary-reference full contextual equivalence by equality of the complete reachable-recipe observation family in general. It supplies a countermodel, not a claim that every Boolean signature or every recipe family fails separation.",
    "Checked positive companion: exact zeroTest on the actual recipe-dependent difference comparator is true if and only if the two recipe amplitudes are equal. Equality of all such reference-recipe tests is equivalent to amplitude equality, choosing an actual comparison recipe from the same known source sector when needed.",
    "The positive companion uses a family of actual recipe-dependent circuits with full retained outputs. It does not claim that one fixed finite Boolean battery gives tomography, nor does it identify a bare zero signature with every contextual test."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeRecipeObservationBoundary.lean"
      declarations := [
        "IDT.QMClosure.NativeRecipeObservationBoundary.first_point_reference",
        "IDT.QMClosure.NativeRecipeObservationBoundary.point_responseEq_iff_eq",
        "IDT.QMClosure.NativeRecipeObservationBoundary.point_observedTransparent",
        "IDT.QMClosure.NativeRecipeObservationBoundary.point_quotient_infinite",
        "IDT.QMClosure.NativeRecipeObservationBoundary.pointLawOfScalar_probability",
        "IDT.QMClosure.NativeRecipeObservationBoundary.point_law_nonempty",
        "IDT.QMClosure.NativeRecipeObservationBoundary.native_output_pointTest_false",
        "IDT.QMClosure.NativeRecipeObservationBoundary.pairedSetting_all_outputs_false",
        "IDT.QMClosure.NativeRecipeObservationBoundary.outside_point_all_recipe_observations_equal",
        "IDT.QMClosure.NativeRecipeObservationBoundary.half_quarter_not_responseEq",
        "IDT.QMClosure.NativeRecipeObservationBoundary.arbitrary_signature_recipe_completeness_fails",
        "IDT.QMClosure.NativeRecipeObservationBoundary.point_two_unit_reference_not_reachable",
        "IDT.QMClosure.NativeRecipeObservationBoundary.zeroComparison_true_iff",
        "IDT.QMClosure.NativeRecipeObservationBoundary.all_zeroComparisons_eq_iff",
        "IDT.QMClosure.NativeRecipeObservationBoundary.zeroComparison_retained_circuit"] }]
  plannedArtifacts := []
  dependencies := ["response_context_probability", "native_single_source_reference_wall",
    "native_reference_separation", "native_recipe_context_realization",
    "native_vacuum_probability_family"]
  limits := [
    "The model explicitly supplies complex coordinates, the native mixer, exact point tests and mathematical arbitrary references; the checked countermodel is conditional on this mathematical setup.",
    "The full-context cancellation reference Rq(x) need not be reachable from the one-unit-source recipe sector; the failure to observe q in that sector supplies no physical availability of Rq(x).",
    "The negative point-test signature and positive zero-test comparator family are distinct supplied response choices. No universal response separation, signature provenance, independent measurement realization, or finite detector robustness is inferred.",
    "All compared inputs are known recipe preparations, with complete circuits and ancillary outputs retained. No unknown-token cloning, unattenuated copying, physical reference or controller availability, actual outcomes, actualization, or full QM closure is established."] }

def responseRecipeComparison : ResearchTask := {
  id := "response_recipe_comparison"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use d:ResponseContextQuotient.Data V Omega with arbitrary signature, globally observed square-swap and first-channel mediality, and full contextual diagonal fixedness at d.chosenZero and the chosen source v. Full ResponseEq continues to quantify over arbitrary fixed raw references.",
    "Use actual same-source Native Event recipes and the actual PairedSetting difference comparisonEvent, with its complete retained circuit and ancillary outputs. The actual vacuumEvent is the identity circuit at tower level 1 with the unused vacuum port, whose original raw value is d.chosenZero.",
    "The algebraic comparison core supplies no probability Law, weight, infinite-order reference, scalar recovery, global observed transparency, or detector soundness. ComparatorVacuumSound is a separate optional premise restricted to actual comparison outputs: signature(Ucomparison)=signature(chosenZero) implies full ResponseEq of that comparison output and chosenZero."]
  conclusions := [
    "Checked quotient algebra: the class of an actual original comparison output equals J(H([U(e)]-[U(f)])), with J and H the existing reconstructed quotient operations. Hence full ResponseEq of Ucomparison and chosenZero is equivalent to full ResponseEq of U(e) and U(f), without any Law, weight, infinite-order reference or scalar recovery premise.",
    "Under the additional ComparatorVacuumSound premise, each individual comparison signature agrees with the vacuum signature if and only if the two input recipe outputs are fully response-equivalent. The reverse implication uses the checked algebra and the hole context; the premise is not inferred from the raw operational laws.",
    "Under the same additional premise, equality of the entire responseProfile over all actual reference recipes is equivalent to full ResponseEq of the compared recipe outputs. These are known recipe-indexed comparison circuits, not a fixed universal finite observation battery.",
    "After establishing the algebraic comparison equivalence, ComparatorVacuumSound is equivalent to correctness of every individual vacuum-baseline test. This is not a minimality theorem and does not claim ComparatorVacuumSound is necessary for completeness of the whole profile."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ResponseRecipeComparison.lean"
      declarations := [
        "IDT.QMClosure.ResponseRecipeComparison.rawEvent_comparison",
        "IDT.QMClosure.ResponseRecipeComparison.comparisonEvent_class",
        "IDT.QMClosure.ResponseRecipeComparison.vacuumEvent_original",
        "IDT.QMClosure.ResponseRecipeComparison.comparison_responseEq_zero_iff",
        "IDT.QMClosure.ResponseRecipeComparison.comparison_signature_eq_zero_iff",
        "IDT.QMClosure.ResponseRecipeComparison.comparatorVacuumSound_iff_comparison_correct",
        "IDT.QMClosure.ResponseRecipeComparison.responseProfile_eq_of_responseEq",
        "IDT.QMClosure.ResponseRecipeComparison.responseProfile_eq_iff"] }]
  plannedArtifacts := []
  dependencies := ["response_recipe_context_reflection", "native_reference_separation",
    "raw_native_dyadic_semantics"]
  limits := [
    "The quotient difference identity, actual vacuum recipe and comparison equivalence use the supplied global observed laws and local fixed-zero/source premises. The signature-baseline and profile theorems additionally retain ComparatorVacuumSound; the algebraic comparison equivalence does not require it.",
    "ComparatorVacuumSound is an explicit additional response assumption on comparison outputs only. Its physical provenance remains open; it is neither an inevitable new primitive nor a consequence of contextual fixedness or a supplied probability law.",
    "The entire raw contextual relation remains supplied over arbitrary fixed references. A conditional recipe profile theorem does not replace it universally by reachable observations, a bare signature, scalar amplitudes or an unattenuated transformation.",
    "Every comparator concerns known preparations and retains its full native circuit. No unknown-token processing, free copying, physical reference or detector availability, finite-precision robustness, actualization, or full QM closure is established."] }

def nativeTwoPointObservationControl : ResearchTask := {
  id := "native_two_point_observation_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the concrete complex native scalar mixer, chosen zero 0, source 1, nonzero t, and exact Boolean signature sigma_t(z)=decide(z=0 or z=t). Full response contexts allow arbitrary fixed complex references; all compared recipe preparations and comparator circuits are actual same-source Native events.",
    "Use the existing pointReference q x from NativeRecipeObservationBoundary and the actual comparisonEvent of response_recipe_comparison. The scalar model supplies global square-swap, mediality and transparency, while physical response provenance and context availability are not supplied."]
  conclusions := [
    "Checked literal-equality control: full arbitrary-reference ResponseEq for sigma_t equals scalar equality. For x different from y, pointReference first with q=0 distinguishes unless the resulting nonzero difference equals t; then q=t gives t versus 2*t, which sigma_t distinguishes because t is nonzero.",
    "The checked equality of entire actual recipe-indexed comparison responseProfiles is equivalent to equality of recipe amplitudes, and hence full contextual classes. Evaluating the two profiles at reference e and reference f forces both signs of the comparator-scaled difference delta=I*(amplitude(e)-amplitude(f))/2 to lie in {0,t}; nonzero delta would force t=-t, contrary to t nonzero.",
    "At t=I/8, the actual half/quarter comparison output is t. Its signature equals the vacuum signature although its full contextual class differs from vacuum, so ComparatorVacuumSound fails while the entire recipe comparison profile remains complete.",
    "This is a nonminimality countercontrol: soundness of each individual vacuum-baseline test is sufficient in the preceding task but is not necessary for completeness of the whole actual recipe-indexed profile. It does not assert that all signatures have complete profiles or select a universal detector principle.",
    "The packaged probability-law adapter transports any supplied scalar native Law with its entire probability field and all six structural fields preserved. A canonicalLaw supplies only a separate consistency witness; neither profile completeness nor ComparatorVacuumSound follows from that witness."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeTwoPointObservationControl.lean"
      declarations := [
        "IDT.QMClosure.NativeTwoPointObservationControl.twoPoint_responseEq_iff_eq",
        "IDT.QMClosure.NativeTwoPointObservationControl.observedTransparent",
        "IDT.QMClosure.NativeTwoPointObservationControl.lawOfScalar_probability",
        "IDT.QMClosure.NativeTwoPointObservationControl.law_nonempty",
        "IDT.QMClosure.NativeTwoPointObservationControl.profile_value",
        "IDT.QMClosure.NativeTwoPointObservationControl.signed_membership_forces_zero",
        "IDT.QMClosure.NativeTwoPointObservationControl.profile_eq_iff_amplitude_eq",
        "IDT.QMClosure.NativeTwoPointObservationControl.profile_eq_iff_responseEq",
        "IDT.QMClosure.NativeTwoPointObservationControl.half_quarter_comparison_amplitude",
        "IDT.QMClosure.NativeTwoPointObservationControl.controlPoint_not_responseEq_vacuum",
        "IDT.QMClosure.NativeTwoPointObservationControl.not_comparatorVacuumSound",
        "IDT.QMClosure.NativeTwoPointObservationControl.separating_profiles_without_comparatorSoundness"] }]
  plannedArtifacts := []
  dependencies := ["response_recipe_comparison", "native_recipe_observation_boundary",
    "native_reference_separation"]
  limits := [
    "The checked model explicitly supplies complex coordinates, the native mixer, exact two-point tests and mathematical arbitrary references. The nonzero t premise remains explicit in the stated full-equivalence and profile theorems; this is a conditional mathematical control.",
    "The profile ranges over all actual reference recipes and known preparation-dependent comparison circuits; this is no fixed universal finite test-count, capacity or efficiency claim. The full arbitrary-reference quotient and the reachable recipe family remain distinct constructions.",
    "Failure of individual baseline soundness together with full-profile completeness is a mathematical control, not a proof of physical detector behavior, physical availability of arbitrary references, unknown-token cloning, free copying, finite-precision or noise robustness, actual outcomes, actualization or full QM closure."] }

def allocatedPreparationContexts : ResearchTask := {
  id := "allocated_preparation_contexts"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Fix an arbitrary two-output raw operation T and the existing finite one-hole context syntax. At every reference occurrence supply a separate allocated known preparation with its input block, circuit, selected reference output and charged resources; repeated descriptions of one known preparation still require separate allocations.",
    "The complete joint initial array, disjoint wire allocations, common frame and legal simultaneous placement of the hole input and preparation resources are externally supplied. No scalar linearity, chosen-zero behavior, zero-preservation law, tensor product or independence premise is inferred."]
  conclusions := [
    "Checked arbitrary-T compiler: eval_realize equates the selected output of an allocated context program with exact ideal raw context evaluation using the separately prepared reference at each occurrence. evalRaw_blocks and eval_pair retain disjoint preparation blocks and the selected two-output gate semantics without scalar or zero-preservation laws.",
    "All preparation wires remain in the complete final array, including companion-output and ancillary wires. Later gates may change earlier cursor values; no separate record of past cursor values or histories is asserted. Exactness concerns the designated final context output, not identification of the complete final array with a one-hole expression.",
    "Checked budget accounting is additive for pair programs; repeating a known preparation charges its budget twice. budget_realize is the hole-program budget plus the sum of all reference-occurrence budgets. The Event adapter preserves actual raw evaluation and has budget one; compiling an Event-reference context with an Event hole therefore charges referenceCount(C)+1. These are allocation counts, not physical source certificates or optimality claims."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/AllocatedPreparation.lean"
      declarations := [
        "IDT.QMClosure.AllocatedPreparation.evalRaw_blocks",
        "IDT.QMClosure.AllocatedPreparation.eval_pair",
        "IDT.QMClosure.AllocatedPreparation.budget_pair",
        "IDT.QMClosure.AllocatedPreparation.budget_repeated",
        "IDT.QMClosure.AllocatedPreparation.eval_ofEvent",
        "IDT.QMClosure.AllocatedPreparation.budget_ofEvent",
        "IDT.QMClosure.AllocatedPreparation.eval_realize",
        "IDT.QMClosure.AllocatedPreparation.budget_realize",
        "IDT.QMClosure.AllocatedPreparation.budget_realize_ofEvent"] }]
  plannedArtifacts := []
  dependencies := ["reference_occurrence_compilation", "native_recipe_context_realization"]
  limits := [
    "Joint initial arrays, common-frame alignment and preparation resources remain supplied conditions, not an implementation of physical simultaneous availability.",
    "Separate allocations of known preparation descriptions are not cloning or reuse of an independently unknown input. No tensor or independence interpretation, uncharged reference availability or physical history-composition law is established.",
    "No multi-source probability-law extension, physical detector or controller availability, outcome actualization, or full QM closure is established."] }

def nativeAllocatedSourceArithmetic : ResearchTask := {
  id := "native_allocated_source_arithmetic"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the concrete native complex scalar mixer and finitely allocated unit-source inputs with explicitly supplied zero inputs, joint initial arrays and a common frame. Every macro records its finite source budget and retains all outputs.",
    "Allocate separate known preparations whenever a construction needs two occurrences of a prepared value. These charged mathematical inputs do not certify physical simultaneous availability, tensor structure, independence or unknown-token cloning."]
  conclusions := [
    "Checked constructive arithmetic supplies actual source-budgeted native macros for multiplication by I and -I, halving, negation and addition, with exact selected-output identities, explicit additive source counts, and the complete final arrays retained.",
    "The existing arbitrary-array closure proves that the selected output of every allocated native program with its arbitrary finite 0/1 input array lies in the Gaussian-dyadic carrier. The checked exclusion shows the scalar 1/3 is not reachable in this generated sector.",
    "Explicit Gaussian-integer and dyadic constructors give every Gaussian-dyadic scalar with a finite charged source budget. Combined with arbitrary-array closure, reachable_iff_gaussian_dyadic proves exact reachability if and only if Gaussian-dyadic over all finite allocated budgets; value_dyadicProgram and budget_dyadicProgram record exact value and source count.",
    "The concrete targetTwo program has selected output 2 and charged source count 10. This is a source-budget witness, not a gate count, wire count, minimum source count, optimal circuit, efficiency, bounded-capacity or general optimality assertion."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAllocatedSourceArithmetic.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.value_phasePlus",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.value_phaseMinus",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.budget_phasePlus",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.budget_phaseMinus",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.value_half",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.budget_half",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.value_negate",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.budget_negate",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.value_add",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.budget_add",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.value_dyadicProgram",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.budget_dyadicProgram",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.value_gaussian_dyadic",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.reachable_iff_gaussian_dyadic",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.third_not_reachable",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.targetTwo_value",
        "IDT.QMClosure.NativeAllocatedSourceArithmetic.targetTwo_budget"] }]
  plannedArtifacts := []
  dependencies := ["allocated_preparation_contexts", "native_single_source_reference_wall",
    "raw_native_dyadic_semantics"]
  limits := [
    "Explicitly increasing a finite source budget changes the supplied preparation resources; it is not amplification or free copying from a single unknown token.",
    "Gaussian-dyadic closure, constructive reachability and the finite 2 witness concern concrete scalar native semantics, not arbitrary raw carriers or arbitrary physical state preparation.",
    "All joint-input availability and common-frame requirements remain supplied. No tensor or independence claim, physical availability, multi-source probability-law extension, detector robustness, outcome actualization or full QM closure is established."] }

def allocatedGeneratedContexts : ResearchTask := {
  id := "allocated_generated_contexts"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For arbitrary raw V, two-output operation T, chosen zero and admitted stock S to V, define G={x | there exists p:Program S with eval(p)=x}. Restrict operations and reference contexts to this generated carrier, retaining program witnesses and charging every allocated reference occurrence. The concrete scalar unit-stock model is a separate specialization.",
    "Use the allocated-preparation compiler with externally supplied joint initial arrays and common frame. Any proposed Gaussian-dyadic characterization in the scalar unit-stock specialization must cite the completed constructive arithmetic proof rather than serve as an unproved identification.",
    "Response signatures are supplied independently on the generated carrier. Any six-field probability law from the earlier ambient complex route remains an additional contract whose consistency with a new generated-context quotient must be checked, not presumed."]
  conclusions := [
    "Checked generic generated-context adequacy: value is surjective onto G, every finite G-reference context lifts to a context of allocated program witnesses, and eval_coe identifies its evaluation with ambient raw evaluation under inclusion. The compiled circuit has exact selected-output semantics and retains the complete final array, with every reference occurrence charged.",
    "compiled_tests_iff_responseEq equates equality of every allocated program-reference test with full contextual equivalence on G and its own G-reference grammar. Ambient ResponseEq restricts to this relation by ambient_responseEq_restrict; the converse is not asserted in general. compiled_budget is the hole-program budget plus referenceBudget(C).",
    "The checked scalar point-signature classification determines exactly when the unchanged single-basis six-field Law exists on the generated carrier: Nonempty pointGeneratedLaw(q) if and only if q is Gaussian-dyadic, equivalently reachable. It supplies a field-preserving adapter for each reachable q, and excludes a response Law for each unreachable q; no law field is relaxed.",
    "Checked scalar point-signature classification: define response Data on the scalar generated carrier G for every ambient complex q, using pointTest q restricted to G. If q lies in G, full G-reference response equivalence is literal equality and any supplied scalar Law transports with its probability field unchanged. If q lies outside G, the signature is constantly false on G and its G-reference contexts, and no response Law exists.",
    "The classification Law retains the existing single-basis six-field contract over G; it does not assign probabilities to joint allocated multi-source inputs. The supplied-law adapter preserves the entire probability field; canonical scalar consistency is a separate witness. The checked pointTest(1/3) boundary has literal ambient response equivalence and an ambient Law, but universal generated-context equivalence and no generated response Law. The point centers 2 and 0 separately admit generated response Laws."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/AllocatedGeneratedContexts.lean"
      declarations := [
        "IDT.QMClosure.AllocatedGeneratedContexts.value_surjective",
        "IDT.QMClosure.AllocatedGeneratedContexts.context_lift",
        "IDT.QMClosure.AllocatedGeneratedContexts.eval_coe",
        "IDT.QMClosure.AllocatedGeneratedContexts.compiled_tests_iff_responseEq",
        "IDT.QMClosure.AllocatedGeneratedContexts.ambient_responseEq_restrict",
        "IDT.QMClosure.AllocatedGeneratedContexts.compiled_budget"] },
    { sourcePath := "Proofs/QMClosure/NativeAllocatedObservationBoundary.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedObservationBoundary.pointGeneratedData",
        "IDT.QMClosure.NativeAllocatedObservationBoundary.value_pointReferenceProgram",
        "IDT.QMClosure.NativeAllocatedObservationBoundary.budget_pointReferenceProgram",
        "IDT.QMClosure.NativeAllocatedObservationBoundary.pointGenerated_responseEq_classification",
        "IDT.QMClosure.NativeAllocatedObservationBoundary.pointGenerated_prepared_coe",
        "IDT.QMClosure.NativeAllocatedObservationBoundary.pointGeneratedLawOfScalar",
        "IDT.QMClosure.NativeAllocatedObservationBoundary.pointGeneratedLawOfScalar_probability",
        "IDT.QMClosure.NativeAllocatedObservationBoundary.pointGenerated_law_nonempty_iff_gaussian_dyadic",
        "IDT.QMClosure.NativeAllocatedObservationBoundary.third_ambient_generated_boundary",
        "IDT.QMClosure.NativeAllocatedObservationBoundary.pointGenerated_law_two",
        "IDT.QMClosure.NativeAllocatedObservationBoundary.pointGenerated_law_zero"] }]
  plannedArtifacts := []
  dependencies := ["allocated_preparation_contexts", "native_allocated_source_arithmetic",
    "response_context_probability", "native_recipe_observation_boundary"]
  limits := [
    "The generic generated-carrier and scalar point-signature components are checked under their supplied mathematical assumptions. Generated-context adequacy does not establish adequacy for arbitrary ambient complex references or transfer every ambient probability law.",
    "A generated-context quotient is a new mathematical scope. Existing ambient probability laws, class distinctions and representation conclusions are not transferred without a separate proof that their exact contracts survive.",
    "Joint-input and common-frame availability remain externally supplied. No physical reference availability, tensor or independence structure, unknown-token cloning, multi-source probability-law extension, physical detector implementation, outcome actualization or full QM closure is established."] }

def denseReferenceContextEquivalence : ResearchTask := {
  id := "dense_reference_context_equivalence"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply a topological raw carrier V, a map A to V with dense range, a two-output operation T whose selected outputs are separately continuous in each input slot, and a continuous signature from V to a Hausdorff response space Omega. No closure of the image of A under T is assumed.",
    "Use the existing finite one-hole context grammar. Restricted contexts have reference values from the supplied dense map; the hole inputs x and y remain arbitrary ambient elements of V, not necessarily generated or in the image.",
    "Density and the stated topology and continuity properties are independent premises. The core concerns an arbitrary dense map; any eventual application to an allocated generated carrier needs a separate density proof and does not add a generated-closure premise to the core."]
  conclusions := [
    "Checked dense-reference equivalence: equality of signatures in every finite dense-reference context is equivalent to ambient full ResponseEq for arbitrary ambient x and y. Transfer reference occurrences one at a time using separate continuity and the Hausdorff equality condition; no simultaneous-net convergence assertion is used.",
    "Whenever an ambient finite context separates x and y, some finite context using references from the dense map also separates them. This is an existence statement, not exact replacement of any individual ambient reference or preservation of a particular numerical response value.",
    "The theorem needs no closure of the dense reference image under T, numerical weight, probability meaning or probability Law. The generated-carrier task is an eventual application boundary, not a hypothesis that identifies all ambient references with generated values.",
    "Analytic scope note: the standard topology observation that every continuous Boolean signature on the connected complex carrier is constant for a Hausdorff Boolean response space is not separately formalized in this module. This observation excludes zeroTest and all nonconstant pointTest signatures from the continuity route; it is not a universal repair for arbitrary coarse or discontinuous response maps."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/DenseReferenceContextEquivalence.lean"
      declarations := [
        "IDT.QMClosure.DenseReferenceContextEquivalence.continuous_eval_mapRefs",
        "IDT.QMClosure.DenseReferenceContextEquivalence.left_stable",
        "IDT.QMClosure.DenseReferenceContextEquivalence.right_stable",
        "IDT.QMClosure.DenseReferenceContextEquivalence.restrictedEq_iff_responseEq",
        "IDT.QMClosure.DenseReferenceContextEquivalence.exists_restricted_separator"] }]
  plannedArtifacts := []
  dependencies := ["response_context_probability", "allocated_generated_contexts"]
  limits := [
    "The checked theorem retains separate continuity of both selected T outputs in both input slots, signature continuity, Hausdorff separation and dense reference range as explicit assumptions. No topology on the reference-label type A or closure of its image is required.",
    "The finite separating-context existence statement supplies no source budget, constructive search procedure, efficiency bound, noise tolerance, error modulus or finite-resolution guarantee. It does not replace an arbitrary ambient reference by an exactly equal generated value.",
    "Topology and continuity are supplied mathematical structure, not physical detector dynamics or probability semantics. No physical source/reference availability, outcome actualization or full QM closure is inferred."] }

def responseAllocatedFaithfulness : ResearchTask := {
  id := "response_allocated_faithfulness"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use arbitrary d:ResponseContextQuotient.Data V Omega and chosen reference v, retaining globally observed square-swap and first-channel mediality. Supply full ResponseSourceLocalProbability.DiagonalFixed at d.chosenZero and v, not bare signature equality.",
    "Evaluate allocated Program Unit with stock v and zero d.chosenZero by the original d.operation. Compare its quotient output class with the concrete native scalar value of the same program using unit stock and scalar zero.",
    "The forward scalar-equality implication supplies no probability Law. For the converse only, retain a supplied six-field ResponseNativeProbabilitySelection.Law d v; no multi-source probability normalization or probability law on the joint allocated input array is assumed."]
  conclusions := [
    "Checked allocated-output relation: correlate the quotient class of every original allocated output with the concrete native scalar unit-stock value, using arbitrary-array circuit_related and source-local normalization. Both quotient zero and source fixedness conditions remain explicit.",
    "Without a Law, equality of the scalar values of two allocated programs implies full ResponseEq of their original raw outputs. This concerns quotient classes, not literal equality of the original raw values.",
    "With a supplied six-field response Law, use normalizedLawEquiv, the faithful Gaussian action and related_scalar_unique to obtain the converse. Equality of scalar unit-stock values is then equivalent to full contextual response equivalence of the allocated original outputs.",
    "The proof route requires no global observed transparency, topology, ComparatorVacuumSound, Gaussian-dyadic reachability converse, or multi-source probability-law extension. The supplied Law remains a conditional premise rather than an outcome of allocated-program compilation.",
    "The checked null-reference control takes v=chosenZero: the source and vacuum programs have the same full contextual class although their scalar values differ, and no supplied response Law exists at that reference. It demonstrates why the Law-free forward implication cannot be reversed in general."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ResponseAllocatedFaithfulness.lean"
      declarations := [
        "IDT.QMClosure.ResponseAllocatedFaithfulness.allocated_class_related",
        "IDT.QMClosure.ResponseAllocatedFaithfulness.scalar_eq_implies_responseEq",
        "IDT.QMClosure.ResponseAllocatedFaithfulness.responseEq_iff_scalar_eq",
        "IDT.QMClosure.ResponseAllocatedFaithfulness.null_reference_control"] }]
  plannedArtifacts := []
  dependencies := ["allocated_preparation_contexts", "response_source_local_probability",
    "raw_native_dyadic_semantics", "raw_native_probability_existence"]
  limits := [
    "The checked output comparison is full quotient-class ResponseEq over arbitrary ambient fixed raw references, not literal raw equality or a replacement of contextual equivalence by a bare signature.",
    "The Law used for faithfulness is the existing single-basis six-field response contract; the theorem does not normalize or interpret probabilities of arbitrary joint allocated multi-source preparations.",
    "Joint initial arrays, stock resources and common-frame alignment remain supplied mathematical inputs. No physical resource availability, tensor or independence structure, unknown-token cloning, actualization, or Born/QM closure is established."] }

def nativeAllocatedBallObservation : ResearchTask := {
  id := "native_allocated_ball_observation"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the concrete complex scalar generated carrier G with its actual finite unit-stock allocated preparations. Supply exact closed-ball signatures sigma(q,r,z)=decide(norm(z-q)<=r) for arbitrary ambient complex q and finite real radius r; response Data is intended for every q and r.",
    "For the positive-radius route, use the separately checked density of Gaussian-dyadic G in the standard complex metric. The ball route uses the scalar metric and strict separation margins, not continuity of the Boolean-valued threshold signature.",
    "The radius is a supplied ideal mathematical tolerance, not a physical detector-noise model. Probability laws retain the earlier supplied single-basis six-field contract over G, not joint allocated-input probabilities."]
  conclusions := [
    "Checked ball-signature classification: if r>0, density of G and a strict margin give a finite G-reference context separating any distinct generated values, so full generated-context response equivalence is literal equality. No exact replacement of a particular ambient reference or numerical response value is asserted.",
    "At r=0 the closed-ball signature is the existing point signature: a reachable center q gives literal response equivalence, while an unreachable center gives a constant-false signature. For r<0 the signature is constant false on every input.",
    "The checked law-existence classification is Nonempty(ResponseLaw(q,r)) if and only if 0<r or (r=0 and Reachable(q)), equivalently using GaussianDyadic(q). The law adapter preserves the entire supplied scalar probability field; canonical scalar consistency is a separate witness. Explicit no-law theorems cover negative radius and zero radius with unreachable center.",
    "The checked density component gives floorGaussian_error strictly below 2/2^k, Gaussian-dyadic density and allocated-program approximation at every positive tolerance. The checked positive-radius witness uses an actual allocated reference p with norm(first(x,value(p))-q)<r<norm(first(y,value(p))-q), supplying a strict margin for each pair of distinct generated values. The radius trichotomy and law classification use the checked generic signature-law criterion."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeGaussianDyadicDensity.lean"
      declarations := [
        "IDT.QMClosure.NativeGaussianDyadicDensity.floorGaussian_error",
        "IDT.QMClosure.NativeGaussianDyadicDensity.exists_gaussian_dyadic_approx",
        "IDT.QMClosure.NativeGaussianDyadicDensity.gaussian_dyadic_dense",
        "IDT.QMClosure.NativeGaussianDyadicDensity.generated_coe_denseRange",
        "IDT.QMClosure.NativeGaussianDyadicDensity.exists_program_approx"] },
    { sourcePath := "Proofs/QMClosure/NativeAllocatedBallObservation.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedBallObservation.ballData",
        "IDT.QMClosure.NativeAllocatedBallObservation.ballSignature_negative",
        "IDT.QMClosure.NativeAllocatedBallObservation.ball_responseEq_negative",
        "IDT.QMClosure.NativeAllocatedBallObservation.ballSignature_zero",
        "IDT.QMClosure.NativeAllocatedBallObservation.ball_responseEq_zero",
        "IDT.QMClosure.NativeAllocatedBallObservation.exists_strict_translate_separation",
        "IDT.QMClosure.NativeAllocatedBallObservation.exists_program_strict_ball_separation",
        "IDT.QMClosure.NativeAllocatedBallObservation.ball_responseEq_iff_eq_of_positive",
        "IDT.QMClosure.NativeAllocatedBallObservation.ball_separates_iff",
        "IDT.QMClosure.NativeAllocatedBallObservation.ball_law_nonempty_iff_gaussian_dyadic",
        "IDT.QMClosure.NativeAllocatedBallObservation.ballLawOfScalar_probability",
        "IDT.QMClosure.NativeAllocatedBallObservation.ball_no_law_negative",
        "IDT.QMClosure.NativeAllocatedBallObservation.ball_no_law_zero_unreachable"] }]
  plannedArtifacts := []
  dependencies := ["allocated_generated_contexts", "native_allocated_source_arithmetic",
    "native_allocated_signature_law", "response_context_probability"]
  limits := [
    "The density, strict ball-separation, radius-trichotomy and law-adapter components are checked in the supplied exact scalar metric/signature model. The positive radius is an ideal mathematical tolerance, not a physical detector-noise model.",
    "The checked numerical floor-grid bound is a mathematical approximation estimate. It supplies no uniform allocated-source budget, efficiency guarantee or physical detector-noise or precision guarantee. Exact Boolean threshold signatures remain supplied mathematical choices.",
    "No Boolean-continuity premise, physical topology or detector implementation, reference/source availability, tensor or independence interpretation, unknown-token cloning, multi-source probability-law extension, outcome actualization or full QM closure is inferred."] }

def nativeAllocatedSignatureLaw : ResearchTask := {
  id := "native_allocated_signature_law"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the concrete scalar generated carrier G from finite 0/1 allocated native programs, with its coherent raw preparation domain, supplied joint input arrays and common frame. For arbitrary Omega and supplied signature sigma:G to Omega, the scalar structural laws give ResponseContextQuotient.Data for every sigma.",
    "Supply no topology, numerical interpretation, positivity or decidable equality on Omega. The relevant separation property is that full G-reference contextual equivalence for sigma separates literal G values, not injectivity of sigma on the bare hole context.",
    "For probability-field transport, supply an arbitrary scalar native Law L and retain the unchanged six-field single-basis response-law contract. The general law-existence criterion has no supplied scalar-Law argument; its sufficient direction has a separate canonical scalar consistency witness. No joint multi-source probability normalization is assumed."]
  conclusions := [
    "Checked full-array coercion for arbitrary tagged-input allocated programs and for the single-basis prepared arrays. The checked identity identifies ResponseAllocatedFaithfulness.rawValue for signature sigma, unit reference and program p with ofProgram(p), without a Law premise.",
    "For any supplied scalar Law L, a response Law with the entire identical probability field exists if and only if sigma's full G-reference contextual equivalence separates literal G values. Necessity uses the checked ResponseAllocatedFaithfulness theorem and surjectivity of generated program values; sufficiency transports the same six fields with the probability field unchanged.",
    "The separate checked law_nonempty_iff_separates states Nonempty(ResponseLaw(sigma)) if and only if full G-contextual separation, without a supplied scalar-Law argument. A canonical scalar Law supplies only the independent consistency witness for the sufficient direction; it does not infer a response signature, probability meaning or physical response provenance.",
    "The full-array coercion and raw-value identity are algebraic facts about coherent allocated preparations. The single-basis Law criterion concerns response compatibility, not a probability-law extension to arbitrary joint multi-source preparations or isolated physical rays."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAllocatedSignatureLaw.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedSignatureLaw.signatureData",
        "IDT.QMClosure.NativeAllocatedSignatureLaw.signatureData_observedTransparent",
        "IDT.QMClosure.NativeAllocatedSignatureLaw.rawValue_eq_ofProgram",
        "IDT.QMClosure.NativeAllocatedSignatureLaw.signature_prepared_coe",
        "IDT.QMClosure.NativeAllocatedSignatureLaw.lawOfScalar",
        "IDT.QMClosure.NativeAllocatedSignatureLaw.lawOfScalar_probability",
        "IDT.QMClosure.NativeAllocatedSignatureLaw.responseEq_eq_of_law",
        "IDT.QMClosure.NativeAllocatedSignatureLaw.law_nonempty_iff_separates",
        "IDT.QMClosure.NativeAllocatedSignatureLaw.same_probability_law_exists_iff_separates"] }]
  plannedArtifacts := []
  dependencies := ["response_allocated_faithfulness", "allocated_generated_contexts",
    "native_allocated_source_arithmetic"]
  limits := [
    "The arbitrary-signature Data, coercion identities, identical-field adapters and both directions of the law criterion are checked in the supplied concrete scalar G model. For an arbitrary scalar Law L, same_probability_law_exists_iff_separates explicitly characterizes existence of a response Law with the entire identical probability field.",
    "The criterion is full contextual separation on G, not bare signature injectivity and not equality with the older ambient complex ResponseEq. Its supplied-Law compatibility result supplies no probability or measurement provenance.",
    "All inputs describe raw coherent preparation programs under supplied common-frame and joint-input conditions. No topology, physical source/reference availability, tensor or independence interpretation, unknown-token cloning, multi-source probability-law extension, actualization or full QM closure is inferred."] }

def nativeAllocatedStableObservation : ResearchTask := {
  id := "native_allocated_stable_observation"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the concrete complex scalar generated carrier G of exact finite 0/1 allocated native programs and the existing native mixer. Supply the usual complex topology and its subspace topology on G. A signature sigma:G to Omega is arbitrary; no topology or numerical meaning on Omega is assumed.",
    "Full response equivalence uses the existing finite one-hole contexts with arbitrary generated reference values, represented by known allocated preparations. Common-frame and joint-input resource conditions remain supplied, and no unknown-input duplication or physical availability is inferred.",
    "For the positive local-stability result, supply a nonempty relatively open subset of G on which sigma is constant. This is an exact mathematical response-region assumption, not a detector derivation or a finite-precision noise model."]
  conclusions := [
    "Checked dense-fiber theorem: if two distinct generated values are fully contextually response-equivalent, every nonempty sigma-fiber is dense in G under the supplied subspace topology. Empty fibers are outside this density statement.",
    "Under the supplied nonempty relatively open constant-region assumption, full G-contextual separation is equivalent to sigma being nonconstant, and hence to Nonempty of the existing single-basis six-field response Law. The generic signature-law theorem supplies the unchanged entire probability-field adapter for any supplied scalar Law; a canonical scalar law remains a separate consistency witness.",
    "The canonical scalar pseudometric is supplied by generatedPseudoMetricSpace. The checked constant_of_patch_and_distinct_responseEq theorem turns an open constant patch and a distinct contextually equivalent pair into global signature constancy, with no topology on response labels. The conditional patch law adapter transports the unchanged six-field contract and preserves the entire supplied probability field.",
    "The checked countermodel defines a unique Gaussian-dyadic residue modulo 5 sending I to 3. The two native outputs have residues (2*u+4*v,4*u+2*v). Full G-contextual response equivalence is exactly residue equality, with distinct responses at 0 and 1 but distinct equivalent values 0 and 5, so no response Law exists despite nonconstancy.",
    "The checked residue countermodel has dense nonempty fibers and no nonempty relatively open constant region, separating nonconstancy alone from the supplied local-stability hypothesis. Explicit no-law and no-same-probability-law theorems preserve the full single-basis six-field contract rather than weakening it."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAllocatedStableObservation.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedStableObservation.generatedPseudoMetricSpace",
        "IDT.QMClosure.NativeAllocatedStableObservation.dense_fiber_of_distinct_responseEq",
        "IDT.QMClosure.NativeAllocatedStableObservation.HasOpenConstantPatch",
        "IDT.QMClosure.NativeAllocatedStableObservation.constant_of_patch_and_distinct_responseEq",
        "IDT.QMClosure.NativeAllocatedStableObservation.separates_iff_nonconstant_of_open_constant_patch",
        "IDT.QMClosure.NativeAllocatedStableObservation.law_nonempty_iff_nonconstant_of_open_constant_patch",
        "IDT.QMClosure.NativeAllocatedStableObservation.lawOfScalarOfPatchNonconstant",
        "IDT.QMClosure.NativeAllocatedStableObservation.lawOfScalarOfPatchNonconstant_probability"] },
    { sourcePath := "Proofs/QMClosure/NativeAllocatedResidueObservation.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedResidueObservation.related_unique",
        "IDT.QMClosure.NativeAllocatedResidueObservation.gaussian_dyadic_existsUnique_related",
        "IDT.QMClosure.NativeAllocatedResidueObservation.residue_operationG",
        "IDT.QMClosure.NativeAllocatedResidueObservation.responseEq_iff_residue_eq",
        "IDT.QMClosure.NativeAllocatedResidueObservation.zeroG_ne_fiveG",
        "IDT.QMClosure.NativeAllocatedResidueObservation.residue_nonconstant",
        "IDT.QMClosure.NativeAllocatedResidueObservation.zeroG_responseEq_fiveG",
        "IDT.QMClosure.NativeAllocatedResidueObservation.residue_not_separates",
        "IDT.QMClosure.NativeAllocatedResidueObservation.residue_dense_fiber",
        "IDT.QMClosure.NativeAllocatedResidueObservation.residue_no_open_constant_patch",
        "IDT.QMClosure.NativeAllocatedResidueObservation.residue_no_law",
        "IDT.QMClosure.NativeAllocatedResidueObservation.residue_no_same_probability_law"] }]
  plannedArtifacts := []
  dependencies := ["native_allocated_signature_law", "native_allocated_ball_observation",
    "native_allocated_source_arithmetic", "allocated_generated_contexts"]
  limits := [
    "The dense-fiber/open-patch route and finite-residue countermodel are checked under the supplied concrete scalar G and topology assumptions. Separate contextual-ideal, native-settling and raw stable-bridge tasks carry their own evidence and assumptions; this entry does not establish their conclusions.",
    "Ordinary scalar topology and a relatively open constant response region are supplied mathematical structure. They supply no physical detector construction, topology on response labels, probability provenance, robustness or precision guarantee.",
    "All references are generated known preparation values in one-hole tests. No physical source/reference availability or common-frame condition is inferred, and no unknown-token cloning, tensor or independence interpretation, multi-source probability-law extension, actualization or full QM closure is established."] }

def nativeAllocatedContextIdeals : ResearchTask := {
  id := "native_allocated_context_ideals"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Use the concrete Gaussian-dyadic scalar generated ring G and the existing native mixer with full G-reference one-hole contexts. Supply arbitrary signature sigma:G to Omega and let R be its full contextual response equivalence. No topology or numerical structure on Omega, nor topology on G, is required for the algebraic route.",
    "Define contextual periods P={d | for every z in G, R z (z+d)}. Distinguish P from the ordinary signature-period subgroup {d | for every z in G, sigma(z+d)=sigma(z)}, which need not be an ideal.",
    "Only the density consequence additionally uses the supplied usual complex/subspace topology. Compatible laws retain the checked generic signature-law theorem's existing single-basis six-field contract and supplied scalar probability field, without joint multi-source normalization."]
  conclusions := [
    "Parent-accepted analytic contract awaiting formalization: R is a difference congruence, with R x y if and only if y-x belongs to P. Prove P is an ideal of the Gaussian-dyadic ring, and characterize it as the largest ideal contained in the ordinary signature-period subgroup, equivalently the largest ideal on every coset of which sigma is constant.",
    "Explicit algebraic proof obligations are the additive subgroup laws, stability under a=(1+I)/2 and b=(1-I)/2 using generated fixed references, recovery of d from a*d using 2*a*b=1, and closure under I=2*a-1 and 1/2=a*b. The ordinary signature-period subgroup is not silently promoted to an ideal.",
    "Under the separately supplied usual topology, a nonzero contextual ideal forces every contextual class and every nonempty signature fiber to be dense. This is a further topological consequence, not an assumption of the ideal characterization.",
    "Topology-free finite-quotient route: a nonzero ideal contains the positive integer norm of a nonzero Gaussian numerator; removal of factors of 2 gives an odd integer N0>0 in the ideal. Prove the quotient has a finite representative family of at most N0 squared residue pairs, so sigma has finite range whenever full contextual separation fails.",
    "Consequently infinite signature range implies full G-contextual separation and hence existence of a compatible single-basis response Law via the checked generic criterion. Infinite range is sufficient, not necessary: generated point tests can have finite response range and still separate full contextual classes.",
    "Odd quotient cardinality does not force odd signature-range cardinality. The quotient-to-response map can identify classes; record no parity claim about the number of supplied response labels."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/NativeAllocatedContextIdeals.lean"]
  dependencies := ["native_allocated_stable_observation", "native_allocated_signature_law",
    "native_allocated_source_arithmetic"]
  limits := [
    "This task records an independently reviewed analytic contract only. No source author is assigned, kernel artifact or checked evidence is registered, and every ideal, finite-quotient and range implication remains a proof obligation before promotion.",
    "The algebraic and finite-range criteria are topology-free; the dense-class and dense-fiber conclusion uses ordinary topology as an explicit separate mathematical premise. Neither supplies a physical topology, readout interpretation or probability provenance.",
    "All references are known generated values in one-hole tests under supplied preparation resources and common-frame conditions. No physical source/reference availability, unknown-token cloning, tensor or independence structure, multi-source probability-law extension, actualization or full QM closure is inferred."] }

def nativeReferenceSettling : ResearchTask := {
  id := "native_reference_settling"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use concrete generated scalar G, arbitrary signature sigma:G to Omega, a fixed generated reference z, and F_z(x)=(operationG(x,z)).1. The core assumes no topology on G or Omega.",
    "Supply the exact all-input settling contract: for every x in G there exists N such that for every n>=N, sigma((F_z iterated n)(x))=sigma(z). Nonconstancy of sigma is an additional premise for the separation and Law conclusions.",
    "Repeated use of the same known reference value requires a fresh charged allocated preparation at every occurrence. No unknown-token duplication or uniform preparation budget is supplied."]
  conclusions := [
    "Checked topology-free ReferenceSettles contract: under exact eventual settling toward one generated reference, full G-contextual separation, signature nonconstancy and existence of the existing single-basis six-field response Law are equivalent. Transport of any supplied scalar Law preserves its entire probability field; canonical scalar consistency remains separate.",
    "The checked common contextual-return theorem gives one positive native iteration length returning every input toward every reference modulo full response equivalence when a distinct equivalent pair exists. Combining that return with exact eventual settling forces global signature constancy. The proof uses positive integer periods, powers-of-16 collisions and a^8=1/16 without a finite quotient, odd-part extraction or new Ring instance.",
    "The identity signature on G is a checked arbitrary-codomain nonnecessity control: it separates full contextual classes and admits a Law while ReferenceSettles fails. Settling is sufficient, not necessary; no finite-alphabet necessity classification is asserted.",
    "The all-input eventual-tail contract is not replaced by finite probes. The optional open-patch-to-settling contraction theorem and universal finite-probe countercontrol are preserved as unchecked obligations in native_reference_settling_scope_extensions."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAllocatedStableObservation.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedStableObservation.ReferenceSettles",
        "IDT.QMClosure.NativeAllocatedStableObservation.referenceStep_iterate_coe",
        "IDT.QMClosure.NativeAllocatedStableObservation.common_contextual_return_of_distinct_responseEq",
        "IDT.QMClosure.NativeAllocatedStableObservation.constant_of_settling_and_distinct_responseEq",
        "IDT.QMClosure.NativeAllocatedStableObservation.separates_iff_nonconstant_of_reference_settles",
        "IDT.QMClosure.NativeAllocatedStableObservation.law_nonempty_iff_nonconstant_of_reference_settles",
        "IDT.QMClosure.NativeAllocatedStableObservation.lawOfScalarOfReferenceSettles",
        "IDT.QMClosure.NativeAllocatedStableObservation.lawOfScalarOfReferenceSettles_probability"] },
    { sourcePath := "Proofs/QMClosure/NativeAllocatedResidueObservation.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedResidueObservation.identity_signature_separates",
        "IDT.QMClosure.NativeAllocatedResidueObservation.identity_signature_not_referenceSettles",
        "IDT.QMClosure.NativeAllocatedResidueObservation.identity_signature_law_without_settling"] }]
  plannedArtifacts := []
  dependencies := ["native_allocated_stable_observation", "native_allocated_signature_law",
    "native_allocated_source_arithmetic"]
  limits := [
    "The topology-free eventual-settling core, same-field Law adapter and identity-signature nonnecessity control are checked. The separate analytic scope-extension task retains optional contraction and finite-probe gaps with no checked evidence.",
    "Settling is an exact supplied response contract, not physical damping, a detector-noise model, a finite validation rule, probability provenance or outcome actualization. The Law retains the existing single-basis contract rather than extending probabilities to joint allocated inputs.",
    "Known reference occurrences remain separately charged under supplied preparation and common-frame conditions. No uniform source budget, physical resource availability, unknown-token cloning, tensor or independence interpretation, actualization or full QM closure is inferred."] }

def responseAllocatedStableBridge : ResearchTask := {
  id := "response_allocated_stable_bridge"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use existing d:ResponseContextQuotient.Data V Omega and source v, retaining the observed square-swap and mediality assumptions and full contextual DiagonalFixed at d.chosenZero and v. These are supplied premises, not bare signature equalities.",
    "For every generated scalar value choose an actual Program Unit witness and define its induced signature by the signature of that program evaluated under the original raw d.operation with stock v and chosen zero. Law-free well-definedness uses scalar_eq_implies_responseEq, not an assumed response Law.",
    "For the core sufficient existence result supply Separates for the induced signature. The open-patch corollary uses induced-signature nonconstancy and a nonempty relatively open constant region under the supplied scalar-coordinate topology. The native-settling corollary uses two actual programs witnessing raw signature nonconstancy and a reference program r with exact raw settling: for every input program p there exists N such that for all n>=N, the signature of n original first-output iterations toward rawValue(r), starting at rawValue(p), equals the signature of rawValue(r). No topology on raw V or on response labels is supplied by this bridge."]
  conclusions := [
    "Checked law-free domain bridge: scalar equality implies full ambient raw ResponseEq, which implies raw equivalence restricted to actual generated program references. Compiled tests identify the restricted raw relation exactly with induced scalar contextual equivalence; under Separates these relations close back to scalar equality. The statement concerns selected raw classes, not literal raw equality.",
    "preparedProgram uses complete native wire arrays and gives exact original raw and scalar selected-output identities. These adapters supply the original ambient single-basis response Law under Separates, and the open-patch corollary supplies that premise from induced-signature nonconstancy and an open constant region. Every adapter transports the unchanged six-field contract and preserves the entire supplied scalar probability field; canonical scalar consistency is separate.",
    "The checked q=1/3 countercontrol has an ambient Law but constantly false induced signature on G. The sufficient bridge result is not an ambient Law-existence if-and-only-if; any restricted generated Law criterion has its own domain and artifacts.",
    "Explicit compiled one-hole contexts give signature correspondence for every reference program r, input program p and iteration n, yielding RawReferenceSettles if and only if induced ReferenceSettles and raw program nonconstancy if and only if induced nonconstancy. Raw settling and raw nonconstancy then suffice for an ambient Law and arbitrary supplied scalar-field transport, without an assumed ambient Law or literal raw convergence/fixedness.",
    "The exact allocated referenceContext source count is Bp+n*Br. This counts tagged source occurrences, not gates, wires, a uniform budget or a physical resource bound; repeated known reference preparations remain separately charged.",
    "The observational premises use original raw evaluation and discrete allocated programs; the existing Native-indexed syntax and scalar proof backend are retained. No scalar coordinates or topology are added as observation data."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ResponseAllocatedStableBridge.lean"
      declarations := [
        "IDT.QMClosure.ResponseAllocatedStableBridge.inducedSignature_ofProgram",
        "IDT.QMClosure.ResponseAllocatedStableBridge.compiled_tests_iff_scalar_responseEq",
        "IDT.QMClosure.ResponseAllocatedStableBridge.generated_responseEq_iff_scalar_responseEq",
        "IDT.QMClosure.ResponseAllocatedStableBridge.ambient_responseEq_iff_scalar_eq_of_separates",
        "IDT.QMClosure.ResponseAllocatedStableBridge.rawValue_preparedProgram",
        "IDT.QMClosure.ResponseAllocatedStableBridge.scalarValue_preparedProgram",
        "IDT.QMClosure.ResponseAllocatedStableBridge.lawOfScalarOfSeparates",
        "IDT.QMClosure.ResponseAllocatedStableBridge.lawOfScalarOfSeparates_probability",
        "IDT.QMClosure.ResponseAllocatedStableBridge.lawOfScalarOfPatchNonconstant",
        "IDT.QMClosure.ResponseAllocatedStableBridge.lawOfScalarOfPatchNonconstant_probability",
        "IDT.QMClosure.ResponseAllocatedStableBridge.third_ambient_law_generated_signature_control",
        "IDT.QMClosure.ResponseAllocatedStableBridge.RawReferenceSettles",
        "IDT.QMClosure.ResponseAllocatedStableBridge.RawProgramNonconstant",
        "IDT.QMClosure.ResponseAllocatedStableBridge.rawValue_referenceContext",
        "IDT.QMClosure.ResponseAllocatedStableBridge.referenceContext_budget",
        "IDT.QMClosure.ResponseAllocatedStableBridge.signature_reference_iterate",
        "IDT.QMClosure.ResponseAllocatedStableBridge.rawReferenceSettles_iff_induced_referenceSettles",
        "IDT.QMClosure.ResponseAllocatedStableBridge.rawProgramNonconstant_iff_induced_nonconstant",
        "IDT.QMClosure.ResponseAllocatedStableBridge.lawOfScalarOfRawReferenceSettles",
        "IDT.QMClosure.ResponseAllocatedStableBridge.lawOfScalarOfRawReferenceSettles_probability",
        "IDT.QMClosure.ResponseAllocatedStableBridge.law_nonempty_of_rawReferenceSettles"] }]
  plannedArtifacts := []
  dependencies := ["response_allocated_faithfulness", "allocated_generated_contexts",
    "native_allocated_stable_observation", "native_reference_settling"]
  limits := [
    "The checked core, open-patch and raw-settling corollaries retain their explicit supplied premises and generated-versus-ambient domains. The existing scalar proof backend is not claimed to be Complex-free. The ambient Law conclusion remains sufficient only, never an ambient law-existence if-and-only-if.",
    "Full observed raw laws and both contextual fixedness premises remain supplied. Scalar-coordinate topology is used only by the open-region route; the alternative exact settling condition is not a physical relaxation or readout principle.",
    "Joint-input resources, source/frame alignment and raw coherent preparation scope remain supplied. No physical source/reference availability, detector or probability provenance, unknown-token cloning, tensor or independence interpretation, multi-source probability-law extension, actualization or full QM closure is inferred."] }

def nativeReferenceRecurrenceWall : ResearchTask := {
  id := "native_reference_recurrence_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use concrete scalar generated G, the checked modulo-5 residue, and the native referenceStep toward zeroG. Define the supplied Boolean hitSignature(x)=decide(residue(x)=0 or residue(x)=1); no topology on G or response labels is required for these added predicates.",
    "References are actual known generated values, with fresh charged preparations for repeated occurrences. Use the checked residue uniqueness and operation laws to transport finite residue calculations to arbitrary generated inputs."]
  conclusions := [
    "The checked Boolean hit signature is nonconstant at generated values 0 and 2. The residue of native referenceStep toward zeroG propagates by multiplication by 2, and the iteration theorem transports that finite residue law to every generated input.",
    "Distinct generated values 0 and 5 are fully response-equivalent after Boolean postcomposition of the residue signature. Full contextual separation therefore fails, no unchanged single-basis six-field Law exists, and no ReferenceSettles witness exists at any reference.",
    "The checked universal hit theorem gives, for every generated x, an iterate n<=3 with the same response as zeroG. The recurrence theorem gives, for every threshold N, an n with N<=n<=N+3 with that response. These are all-input transported theorems, not finite-input experiments.",
    "The residue-level five-state decision calculation is explicitly transported through native iteration. This entry asserts the actual universal bounds, not an extra exact-cycle theorem, minimal hitting times or optimality of the bound 3.",
    "The countercontrol excludes weakening an eventual constant tail to one hit or arbitrarily late recurrent hits. It does not claim that finite-input testing validates universal settling or that recurrence implements physical relaxation."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAllocatedResidueObservation.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedResidueObservation.hitSignature",
        "IDT.QMClosure.NativeAllocatedResidueObservation.hitSignature_nonconstant",
        "IDT.QMClosure.NativeAllocatedResidueObservation.residue_referenceStep_zeroG",
        "IDT.QMClosure.NativeAllocatedResidueObservation.residue_referenceStep_zeroG_iterate",
        "IDT.QMClosure.NativeAllocatedResidueObservation.hitSignature_zero_reference_hit_within_three",
        "IDT.QMClosure.NativeAllocatedResidueObservation.hitSignature_zero_reference_recurrence",
        "IDT.QMClosure.NativeAllocatedResidueObservation.zeroG_hitSignature_responseEq_fiveG",
        "IDT.QMClosure.NativeAllocatedResidueObservation.hitSignature_not_separates",
        "IDT.QMClosure.NativeAllocatedResidueObservation.hitSignature_no_reference_settles",
        "IDT.QMClosure.NativeAllocatedResidueObservation.hitSignature_no_settling_reference",
        "IDT.QMClosure.NativeAllocatedResidueObservation.hitSignature_no_law",
        "IDT.QMClosure.NativeAllocatedResidueObservation.hitSignature_no_same_probability_law"] }]
  plannedArtifacts := []
  dependencies := ["native_allocated_stable_observation", "native_reference_settling",
    "native_allocated_signature_law"]
  limits := [
    "The generated-input hit and recurrence bounds, Boolean contextual countercontrols, no-law statements and no-settling statements are checked under the supplied concrete residue/signature model. No separate exact-cycle or minimality claim is registered.",
    "Exact Boolean recurrence is a supplied mathematical response control, not a detector readout, relaxation mechanism, noise model or probability provenance. Its universal transport obligation remains distinct from a finite probe experiment.",
    "No physical source/reference availability, common-frame condition, unknown-token cloning, tensor or independence interpretation, multi-source probability-law extension, actual outcomes, actualization or full QM closure is inferred."] }

def nativeReferenceSettlingScopeExtensions : ResearchTask := {
  id := "native_reference_settling_scope_extensions"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Use concrete generated scalar G, the native mixer, arbitrary signature sigma:G to Omega and separately charged known reference preparations. No author is assigned to the remaining equal-label finite-probe tail control.",
    "The open-patch contraction route is separately checked under the canonical scalar/subspace topology in native_open_patch_single_trace. The remaining equal-label finite-probe control is an algebraic residue construction and adds no topology premise."]
  conclusions := [
    "The open-patch-to-settling contraction implication is checked in the separate native_open_patch_single_trace task, with canonical topology and arbitrary response labels. This entry points to that evidence without adding evidence or promoting its remaining equal-label finite-probe obligation.",
    "Pending universal finite-input-probe countercontrol: for any finite probe family, choose an odd M>max(1,4*probeCount) and use a union of native a-orbits in the residue model. Each selected probe initially has the reference label and retains that label along its whole selected orbit. This equal-label control does not refute changed-response tails or eventual avoidance of the initial label. The identity a^4=-1/4 gives the intended orbit-size bound at most 4*M versus M squared residue classes; every universal control and transport step requires an explicit artifact.",
    "The finite F9 axes control applies to halving only and must not be asserted as a native F_z control, whose a-orbit has order 8 in that example. This distinction remains part of the pending algebraic countercontrol.",
    "Finite probes do not replace the all-input eventual-tail predicate. The remaining equal-label finite-probe countercontrol is analytic and is not a checked conclusion or a necessity theorem for every response codomain; the contraction implication has separate checked evidence."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/NativeAllocatedStableObservation.lean",
    "Proofs/QMClosure/NativeAllocatedResidueObservation.lean"]
  dependencies := ["native_reference_settling", "native_allocated_source_arithmetic"]
  limits := [
    "This task retains the equal-label finite-probe tail control with analytic status, no checked evidence and no assigned source author. Existing checked declarations in the prospective extension files do not discharge that remaining obligation.",
    "Known reference occurrences stay separately charged. No uniform source budget, physical damping, detector-noise model, reference availability, unknown-token cloning, probability provenance, multi-source Law extension, actualization or QM closure is inferred."] }

def nativeBinaryValuationNonsettling : ResearchTask := {
  id := "native_binary_valuation_nonsettling"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use concrete Gaussian-dyadic generated G and the existing native mixer. Supply the Boolean readout that is true exactly when the rational 2-adic valuation of Re(x) is odd, with valuation(0)=0. The readout depends on the exact rational coordinate value, independently of its chosen Gaussian-dyadic numerator/exponent representation.",
    "The valuation is supplied arithmetic, not a new 2-adic topology. The existing Native-indexed complex scalar backend is retained; no scalar-coordinate-free backend or physical detector interpretation is asserted.",
    "Probability compatibility uses the existing single-basis six-field Law and generic signature criterion, not probabilities on joint allocated input arrays."]
  conclusions := [
    "Checked separation route: a distinct contextually equivalent pair gives a common return length L>0 by the checked common_contextual_return theorem. Repeating that return eight times at x=2 and z=1 compares 2 with 1+16^(-L); their rational valuations are 1 and -4*L, respectively, so their Boolean readouts differ. This forces full G-contextual separation without an additional separation hypothesis.",
    "Checked universal nonsettling proof: for each generated reference z take q=realCoord(z) and x=z+1. For nonzero q choose arbitrarily late k with -(4*k)<padicValRat 2 q; the checked valuation-dominance lemma handles q=0 separately and gives valuations -(4*k) and -(4*k+1) after 8*k and 8*k+1 native iterations, hence opposite labels. The plusUnit input has no eventual constant tail at all, so ReferenceSettles fails at every generated reference.",
    "The checked contextual separation and generic signature-law criterion give existence of the unchanged six-field single-basis Law and an adapter preserving the entire probability field of any supplied scalar Law. A canonical scalar Law remains a separate consistency witness, not probability provenance.",
    "No fiber-density theorem is established by this checked core entry. The optional usual-topology density construction and exact generated witnesses remain a separate unchecked analytic task, native_binary_valuation_density."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAllocatedValuationObservation.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedValuationObservation.realCoord",
        "IDT.QMClosure.NativeAllocatedValuationObservation.realCoord_cast",
        "IDT.QMClosure.NativeAllocatedValuationObservation.realCoord_eq_of_cast",
        "IDT.QMClosure.NativeAllocatedValuationObservation.valuationSignature",
        "IDT.QMClosure.NativeAllocatedValuationObservation.val_plusUnit",
        "IDT.QMClosure.NativeAllocatedValuationObservation.realCoord_reference_eighth",
        "IDT.QMClosure.NativeAllocatedValuationObservation.realCoord_reference_eighth_next",
        "IDT.QMClosure.NativeAllocatedValuationObservation.late_adjacent_opposite_signatures",
        "IDT.QMClosure.NativeAllocatedValuationObservation.plusUnit_no_eventual_constant",
        "IDT.QMClosure.NativeAllocatedValuationObservation.valuationSignature_no_reference_settles",
        "IDT.QMClosure.NativeAllocatedValuationObservation.valuationSignature_no_settling_reference",
        "IDT.QMClosure.NativeAllocatedValuationObservation.valuationSignature_nonconstant",
        "IDT.QMClosure.NativeAllocatedValuationObservation.valuationSignature_separates",
        "IDT.QMClosure.NativeAllocatedValuationObservation.valuationSignature_law_without_settling",
        "IDT.QMClosure.NativeAllocatedValuationObservation.lawOfScalar",
        "IDT.QMClosure.NativeAllocatedValuationObservation.lawOfScalar_probability"] }]
  plannedArtifacts := []
  dependencies := ["native_reference_settling", "native_allocated_signature_law",
    "native_allocated_source_arithmetic"]
  limits := [
    "Representation-independent coordinates, rational-valuation identities, unconditional contextual separation and all-reference nonsettling are checked in the supplied concrete G model. The adapter preserves the entire probability field of any supplied scalar Law. Optional fiber density is not part of this checked result.",
    "This is a supplied exact arithmetic negative control; no continuity or topology premise is used by the core theorem. Neither the rational valuation nor its Boolean readout supplies a physical detector, topology derivation, reference availability or probability provenance.",
    "Known references remain actual allocated preparations under supplied source/frame conditions. No unknown-token cloning, tensor or independence interpretation, multi-input probability-law extension, actualization or full QM closure is inferred."] }

def nativeBinaryValuationDensity : ResearchTask := {
  id := "native_binary_valuation_density"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Use the checked binary rational-valuation signature on generated Gaussian-dyadic G, and separately supply the usual complex/subspace topology. Rational real coordinates are representation-independent; valuation(0)=0 remains the fixed convention.",
    "Generated perturbations are actual finite allocated programs under supplied source/frame conditions. The numerical perturbation is ordinary 2^(-n), not a new 2-adic topology or a physical detector tolerance."]
  conclusions := [
    "Accepted analytic density obligation, not yet formalized: both Boolean signature fibers are dense in G. For an arbitrary z with Re(z)=m/2^h, use z+2^(-n) for arbitrarily large n>h of the desired parity; the rational valuation of its real coordinate is -n.",
    "Prove exact generated witnesses for the perturbations and ordinary convergence to z, then obtain membership in every prescribed nonempty relative open neighborhood. The existing checked valuation-core artifact does not establish this density statement."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/NativeAllocatedValuationObservation.lean"]
  dependencies := ["native_binary_valuation_nonsettling", "native_allocated_source_arithmetic"]
  limits := [
    "This optional topology consequence is analytic only with empty checked evidence. Its perturbation, parity and dense-fiber assertions remain proof obligations even though the prospective extension file already contains checked core declarations.",
    "Usual scalar topology is supplied, not a physical topology or robustness derivation. No uniform source budget, detector interpretation, physical references, probability provenance, unknown-token cloning, multi-source Law extension, actualization or QM closure is inferred."] }

def nativeFiniteObservationUnderdetermination : ResearchTask := {
  id := "native_finite_observation_underdetermination"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use concrete generated Gaussian-dyadic G, any finite set S of generated values and any Boolean labeling f on S. The exact checked top statement is: for every S:Finset G and f:G to Bool, Nonempty(ExtensionPair S f), with no additional premises.",
    "Supply the checked native mixer and generated arithmetic. Ordinary scalar topology is used only to exhibit a nonempty false open patch for the finite-support positive extension; no physical readout model or probability provenance is supplied."]
  conclusions := [
    "Checked finite-observation boundary: for every finite S and Boolean labeling f, ExtensionPair supplies two signatures agreeing with f on S, both nonconstant. The positive signature separates full contextual classes and admits the existing single-basis six-field Law; the negative signature fails separation, admits no such Law and has no ReferenceSettles witness.",
    "The construction adds two fresh generated points with opposite labels. The residue helper gives a common Gaussian-dyadic denominator and an odd M>1 whose full pair residue is injective on any prescribed finite set; the implementation chooses M=2*B+3 from a coordinate-difference bound B.",
    "For arbitrary odd M, the representation-independent Related relation gives a unique residue in ZMod(M) x ZMod(M). Invertibility of 2 gives native compatibility and contextual preservation without a prime-modulus premise or a chosen square root of -1. The zero and natural-modulus controls yield distinct generated values with identical residues.",
    "The positive finite-support indicator has a false open patch and is nonconstant; no positive exact-settling assertion is packaged. The negative residue-image indicator matches the same finite labels while identifying 0 and M contextually, so its no-law and no-settling conclusions retain the unchanged six-field contract.",
    "Finitely many generated context-output observations can be collected into S. The artifact contains no separate adaptive-executor syntax or checked adaptive-execution theorem, and makes no claim about a finite input family supplied with all its infinite response tails. Finite symbolic proofs and inference in separately restricted model classes are outside the underdetermination statement."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAllocatedGaussianResidue.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedGaussianResidue.Related",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.related_unique",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.related_of_presentation",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.generated_exists_related",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.residue",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.residue_presentation",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.two_isUnit",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.residue_operationG",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.responseEq_of_residue_eq",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.naturalG_injective",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.residue_zeroG",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.residue_natural_modulus",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.common_denominator",
        "IDT.QMClosure.NativeAllocatedGaussianResidue.exists_finite_injective_residue"] },
    { sourcePath := "Proofs/QMClosure/NativeAllocatedFiniteObservationBoundary.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedFiniteObservationBoundary.ExtensionPair",
        "IDT.QMClosure.NativeAllocatedFiniteObservationBoundary.finite_observation_boundary"] }]
  plannedArtifacts := []
  dependencies := ["native_allocated_stable_observation", "native_reference_settling",
    "native_allocated_signature_law", "native_allocated_source_arithmetic"]
  limits := [
    "The two checked modules establish representation-independent odd-modulus residue compatibility, finite-set injectivity and the unconditional ExtensionPair theorem. Its positive branch has no exact-settling field, and adaptive transcript interpretation is not a separate formal executor result.",
    "The claim is finite observational underdetermination within the stated unrestricted mathematical signature class, not a rejection of finite machine-checked proofs or of inference under an explicitly restricted model class.",
    "Known generated references remain separately allocated under supplied source/frame conditions. No uniform source budget, physical availability, detector interpretation, probability provenance, unknown-token cloning, multi-source Law extension, actualization or QM closure is inferred."] }

def nativeReferenceSettlingRegularityScope : ResearchTask := {
  id := "native_reference_settling_regularity_scope"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Supply the usual inherited topology on concrete generated G and its native referenceStep F_z. For arbitrary sigma:G to Omega, local uniform settling at z means an open U containing z and one N such that for all x in U and all n>=N, sigma((F_z iterated n)(x))=sigma(z). No topology on Omega is needed for this equality-only definition.",
    "Boolean descriptive-regularity controls additionally use the usual discrete topology on Bool. Distinguish regularity on countable G from extensions to ambient complex space, and distinguish ambient real-valued from ambient Boolean-valued Baire-class-one extensions."]
  conclusions := [
    "Accepted analytic local-uniform criterion awaiting artifacts: local uniform settling at z is equivalent to sigma being constant on a neighborhood of z. Forward, F_z iterated N is a homeomorphism because a=(1+I)/2 is a unit; reverse, choose an invariant sufficiently small ball and take N=0.",
    "Pointwise all-input ReferenceSettles does not imply any constant open patch. Construct a dense partial transversal T in G excluding 0, with at most one representative of each two-sided a-orbit. Its Boolean indicator settles toward 0 because each forward orbit visits T at most once, while both fibers are dense.",
    "The transversal proof is to enumerate a countable base and choose fresh orbits, using that finite unions of two-sided orbit closures are nowhere dense. The complement is dense because a nonempty open U contained in T would make a*U open and disjoint from dense T.",
    "Countability of G makes every Boolean signature Borel and Baire-property, and the intended clopen-box interpolation on the first n enumerated points makes every such signature Bool-valued Baire class one on G. An ambient complex Borel/Baire-property extension also imposes no restriction: extend the countable true fiber by its indicator.",
    "An ambient real-valued Baire-class-one extension on complex space is a substantive different assumption: a continuity point forces a nonempty constant patch on dense binary G, and the separately checked native_open_patch_single_trace bridge then gives settling. A Bool-valued Baire-class-one extension on connected complex space would instead be constant; it is not the same assumption.",
    "Global all-input uniform finite-time settling forces sigma constant by surjectivity of the native iterate. Local uniform response stability is therefore distinct from both that global condition and pointwise eventual settling.",
    "Optional equality-only cofinite relaxation: for every input, eventual exclusion of each wrong label separately should suffice, with nonconstancy, for separation by common contextual return. Finite response range makes this equivalent to exact settling; the identity signature exhibits its infinite-range weakness. Nonunique equality-only limits supply no outcome selection."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/NativeAllocatedSettlingRegularity.lean"]
  dependencies := ["native_allocated_stable_observation", "native_reference_settling"]
  limits := [
    "Every assertion in this entry is analytic only, with no checked evidence. The local-uniform equivalence, dense-transversal construction, regularity and extension distinctions, global-uniform collapse and optional cofinite criterion all require separate exact artifacts.",
    "Ordinary topology and regularity are supplied mathematical structure. Local response stability is not physical robustness, detector dynamics, a noise model, probability provenance or outcome actualization.",
    "Known references remain separately charged under supplied preparation and common-frame conditions. No physical reference availability, unknown-token cloning, tensor or independence interpretation, multi-source probability-law extension or QM closure is inferred."] }

def nativeContextAttenuationRecordBoundary : ResearchTask := {
  id := "native_context_attenuation_record_boundary"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the existing one-hole Context grammar over concrete generated G and the native scalar mixer. All reference values are fixed independently of the unknown hole input; each constructor selects one output with slope a=(1+I)/2 or b=(1-I)/2.",
    "Supply the existing complex scalar backend and usual complex metric. Context depth counts constructors on the selected one-hole path, not the total depth of a retained-wire circuit whose companion outputs may later re-enter.",
    "For a sequence C_n, use the same input-independent context sequence for all compared inputs; known reference values may vary with n. A premise that one selected-output sequence converges is separate from depth tending to infinity."]
  conclusions := [
    "Checked affine-context contract: each finite C evaluates as C(x)=c_C*x+d_C, with normSq(c_C)=(1/2)^depth(C). The exact exported distance law is normSq(C(x)-C(y))=(1/2)^depth(C)*normSq(x-y), and every finite one-hole context remains injective. No separate literal 1/sqrt(2) norm theorem is registered.",
    "For any one common input-independent sequence C_n with selected-path depth tending to infinity, the output differences for each fixed pair of inputs tend to zero, even when the known references vary. If outputs converge for one input, they converge for every input to that same scalar limit. No existence of convergence is asserted from attenuation alone.",
    "Broader affine-sequence boundary: if c_n*x+d_n converges at inputs 0 and 1 to l0 and l1, respectively, it converges pointwise on G to (l1-l0)*x+l0. The literal limiting affine function has finite image on infinite G if and only if its slope l1-l0 is zero, in which case it is constant.",
    "These results concern literal scalar limiting values on the selected one-hole path. Selected-wire attenuation alone supplies neither distinct limiting records nor discrete readout or outcome actualization."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAllocatedContextAttenuation.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedContextAttenuation.depth",
        "IDT.QMClosure.NativeAllocatedContextAttenuation.eval_affine",
        "IDT.QMClosure.NativeAllocatedContextAttenuation.slope_normSq",
        "IDT.QMClosure.NativeAllocatedContextAttenuation.eval_sub",
        "IDT.QMClosure.NativeAllocatedContextAttenuation.eval_sub_normSq",
        "IDT.QMClosure.NativeAllocatedContextAttenuation.slope_ne_zero",
        "IDT.QMClosure.NativeAllocatedContextAttenuation.eval_injective",
        "IDT.QMClosure.NativeAllocatedContextAttenuation.eval_sub_tendsto_zero",
        "IDT.QMClosure.NativeAllocatedContextAttenuation.eval_tendsto_of_one",
        "IDT.QMClosure.NativeAllocatedContextAttenuation.affine_tendsto_of_zero_unit",
        "IDT.QMClosure.NativeAllocatedContextAttenuation.affine_finite_range_iff",
        "IDT.QMClosure.NativeAllocatedContextAttenuation.affine_limit_finite_range_iff"] }]
  plannedArtifacts := []
  dependencies := ["native_reference_settling", "native_allocated_source_arithmetic",
    "allocated_preparation_contexts"]
  limits := [
    "Affine semantics, exact squared-norm attenuation, finite injectivity, shared-sequence conditional convergence, two-point affine convergence and the finite literal-image criterion are checked. Attenuation alone supplies no existence of a limit, and the registered exact metric formula is squared norm.",
    "All companion and ancillary wires remain retained. Square-swap already permits recoverability when companion outputs re-enter, so the selected-path theorem is no claim of global information erasure, thermodynamic irreversibility or a no-go theorem for detectors.",
    "Input-dependent feedback, stopping, decoding and richer retained-wire observables are outside this proof scope. The same-context-sequence condition cannot be dropped or replaced by a total-circuit-depth statement.",
    "The usual metric and scalar backend are supplied mathematical structure. No probabilities, physical detector implementation, source/reference availability, probability provenance, actualization or full QM closure are inferred."] }

def nativeSingleTraceProbabilityCriterion : ResearchTask := {
  id := "native_single_trace_probability_criterion"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use concrete generated G, native referenceStep F_z and arbitrary signature sigma:G to Omega. No topology or finite response-range assumption is supplied. Witnesses use one generated input x and one generated reference z.",
    "HasNonperiodicReferenceTrace is absence of a positive period from time zero: there exist z and x such that for every L>0 there exists n>=0 with sigma(F_z iterated (n+L) at x) different from sigma(F_z iterated n at x). This includes indispensable quantification over infinitely many times, not a finite transcript."]
  conclusions := [
    "Checked single-trace criterion: failure of contextual separation supplies one common positive contextual return L for every reference and input. Apply that return at F_z iterated n at x to force exact period L at every n, contradicting the witness. Hence the witness implies full G-contextual separation.",
    "HasEventuallyAvoidingReferenceTrace is the simpler sufficient witness of eventual avoidance of the initial label: there exist z,x,N such that every n>=N has sigma(F_z iterated n at x) different from sigma(x). HasChangedConstantReferenceTail is the changed constant-tail special case with label c different from sigma(x); c need not equal sigma(z). These witnesses imply the time-zero nonperiodicity criterion and make nonconstancy automatic.",
    "For each of the three predicates, the checked artifact supplies a separation theorem, automatic nonconstancy, a Law constructor, an entire-probability-field equality for every supplied scalar Law and a separate nonempty wrapper. The changed-tail-to-avoidance-to-time-zero-nonperiodicity chain is checked. Canonical scalar consistency remains separate, and no necessity claim is asserted.",
    "The checked arbitrarily_late_change_without_law and one_change_without_law controls use the modulo-5 hitSignature to give arbitrarily late changes or a single change while a compatible Law still fails. They reject those weaker criteria, not the exact eventual-avoidance or time-zero-nonperiodicity witnesses.",
    "The one-input/reference witness is compatible with finite-transcript underdetermination because its infinite time quantifiers are essential. A finite observation or finite input family without the required full-time contract does not establish it."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAllocatedSingleTraceLaw.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.HasNonperiodicReferenceTrace",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.HasEventuallyAvoidingReferenceTrace",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.HasChangedConstantReferenceTail",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.eventuallyAvoiding_of_changedConstantTail",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.nonperiodic_of_eventuallyAvoiding",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.separates_of_nonperiodicReferenceTrace",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.separates_of_eventuallyAvoidingReferenceTrace",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.separates_of_changedConstantTail",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.nonconstant_of_nonperiodicReferenceTrace",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.nonconstant_of_eventuallyAvoidingReferenceTrace",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.nonconstant_of_changedConstantTail",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.lawOfScalarOfNonperiodicTrace",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.lawOfScalarOfNonperiodicTrace_probability",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.law_nonempty_of_nonperiodicTrace",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.lawOfScalarOfEventuallyAvoidingTrace",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.lawOfScalarOfEventuallyAvoidingTrace_probability",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.law_nonempty_of_eventuallyAvoidingTrace",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.lawOfScalarOfChangedConstantTail",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.lawOfScalarOfChangedConstantTail_probability",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.law_nonempty_of_changedConstantTail",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.arbitrarily_late_change_without_law",
        "IDT.QMClosure.NativeAllocatedSingleTraceLaw.one_change_without_law"] }]
  plannedArtifacts := []
  dependencies := ["native_reference_settling", "native_allocated_signature_law",
    "native_reference_recurrence_wall"]
  limits := [
    "All three exact infinite-time sufficient predicates, their implication chain, automatic nonconstancy, field-preserving Law adapters and both sharp weaker-criterion controls are checked. This is neither a necessity theorem nor a finite observational verification rule.",
    "Known references are separately charged at each occurrence. No topology, finite alphabet, uniform source budget, physical detector/probability provenance, unknown-token cloning, multi-source Law extension, outcome selection, actualization or QM closure is inferred."] }

def rawSingleTraceProbabilityBridge : ResearchTask := {
  id := "raw_single_trace_probability_bridge"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the existing Data d and source v with observed square-swap and mediality and full contextual DiagonalFixed at chosenZero and v, as in the checked raw stable bridge. All trace witnesses use original rawReferenceStep toward rawValue of an actual reference program r, starting from rawValue of an actual input program p.",
    "Use RawEventuallyAvoidingReferenceTrace, RawChangedConstantReferenceTail or RawNonperiodicReferenceTrace with the same exact infinite time quantifiers as the scalar criterion. No scalar coordinates or topology are added as observation data; the Native-indexed complex scalar proof backend is retained."]
  conclusions := [
    "Checked raw-trace bridge: signature_reference_iterate and inducedSignature_ofProgram transport every trace time exactly to the induced scalar signature. Preserve actual compiled context witnesses; do not induct on bare signature equality.",
    "Each raw predicate has a checked induced scalar predicate transport and separation theorem targeting inducedSignature on G, not ambient literal-state separation. Each then supplies an original ambient single-basis Law constructor, equality of the entire probability field for any supplied scalar Law, and a nonempty wrapper. The unchanged six-field contract is transported, and canonical scalar consistency is a separate witness.",
    "This is sufficient only, not an ambient Law-existence if-and-only-if. The checked ambient point-signature countercontrol remains compatible with failure of a proposed induced trace witness.",
    "The existing exact reference allocation is Bp+n*Br at time n. It counts separate known reference preparations, not a uniform physical resource bound, gate/wire count, physical cloning operation or detector implementation."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ResponseAllocatedSingleTraceBridge.lean"
      declarations := [
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.RawNonperiodicReferenceTrace",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.RawEventuallyAvoidingReferenceTrace",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.RawChangedConstantReferenceTail",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.induced_nonperiodic_of_rawNonperiodic",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.induced_eventuallyAvoiding_of_rawEventuallyAvoiding",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.induced_changedConstantTail_of_rawChangedConstantTail",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.separates_of_rawNonperiodicTrace",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.separates_of_rawEventuallyAvoidingTrace",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.separates_of_rawChangedConstantTail",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.lawOfScalarOfRawNonperiodicTrace",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.lawOfScalarOfRawNonperiodicTrace_probability",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.law_nonempty_of_rawNonperiodicTrace",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.lawOfScalarOfRawEventuallyAvoidingTrace",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.lawOfScalarOfRawEventuallyAvoidingTrace_probability",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.law_nonempty_of_rawEventuallyAvoidingTrace",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.lawOfScalarOfRawChangedConstantTail",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.lawOfScalarOfRawChangedConstantTail_probability",
        "IDT.QMClosure.ResponseAllocatedSingleTraceBridge.law_nonempty_of_rawChangedConstantTail"] }]
  plannedArtifacts := []
  dependencies := ["response_allocated_stable_bridge", "native_single_trace_probability_criterion"]
  limits := [
    "The raw predicates, all-time induced-signature transports, sufficient ambient Law constructors and identical-field equalities are checked with Data and both full contextual DiagonalFixed premises retained. The separation target is inducedSignature only; no ambient literal-state or necessity theorem is asserted.",
    "Observed raw laws, contextual fixedness, actual program resources and common-frame conditions remain supplied. No Complex-free backend, scalar/topological observation datum, physical detector or probability provenance, multi-source Law extension, outcome actualization or QM closure is inferred."] }

def nativeOpenPatchSingleTrace : ResearchTask := {
  id := "native_open_patch_single_trace"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply the canonical inherited topology on generated G and the existing ordinary complex scalar backend. The signature sigma:G to Omega is arbitrary; no topology on Omega or global continuity of sigma is assumed.",
    "Use actual repeated left-first one-hole contexts of depth n with a fixed generated reference z, separately allocating every repeated known reference occurrence. The native iterate fixes z as a selected scalar output; no physical availability or unknown-input copying is supplied."]
  conclusions := [
    "Checked contraction result: for every generated z and x, native fixed-reference iterates converge to z, first in literal complex coordinates and then in the canonical G topology. The proof uses the committed shared-context attenuation theorem on the actual depth-n repeated contexts, with the reference output fixed.",
    "HasOpenConstantPatch sigma supplies a generated z inside the relatively open constant region. Convergence gives an input-dependent eventual time N(x) at which all later iterates have response sigma(z), hence ReferenceSettles sigma. No nonconstancy premise is required for patch-to-settling.",
    "With nonconstancy additionally supplied, choose an input whose label differs from sigma(z). Its settled tail has the changed constant label sigma(z), giving HasChangedConstantReferenceTail sigma. This checked witness composes with the existing single-trace Law adapter and its entire-field equality; no Law constructor was duplicated in this artifact.",
    "Patch-to-settling, nonconstant settling-to-changed-tail and nonconstant patch-to-changed-tail are checked in this isolated artifact. Local-uniform equivalence, dense-transversal/Baire results and universal finite-input infinite-tail countercontrols remain separate analytic tasks and are not discharged by this entry."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAllocatedSettlingRegularity.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedSettlingRegularity.referenceStep_iterate_coe_tendsto",
        "IDT.QMClosure.NativeAllocatedSettlingRegularity.referenceStep_iterate_tendsto",
        "IDT.QMClosure.NativeAllocatedSettlingRegularity.referenceSettles_of_openConstantPatch",
        "IDT.QMClosure.NativeAllocatedSettlingRegularity.changedConstantTail_of_referenceSettles_nonconstant",
        "IDT.QMClosure.NativeAllocatedSettlingRegularity.changedConstantTail_of_openConstantPatch_nonconstant"] }]
  plannedArtifacts := []
  dependencies := ["native_context_attenuation_record_boundary", "native_reference_settling",
    "native_single_trace_probability_criterion"]
  limits := [
    "The five registered theorems establish literal and canonical G-topological convergence, patch-to-settling and both nonconstant changed-tail corollaries. No new Law adapter is defined here, and the shared file does not establish the separate local-uniform, Baire or dense-transversal obligations.",
    "Eventual time may depend on the input; no global uniform time or source budget is asserted. Ordinary scalar topology is supplied, not a topology or continuity principle on response labels.",
    "Known references remain separately allocated under supplied source/frame conditions. No physical detector, topology or robustness derivation, reference availability, probability provenance, unknown-token cloning, multi-source Law extension, outcome actualization or QM closure is inferred."] }

def nativePointwisePeriodicSeparatingReadout : ResearchTask := {
  id := "native_pointwise_periodic_separating_readout"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Use countable Gaussian-dyadic generated G and native unit a=(1+I)/2. The nontrivial two-sided orbit O(z,x) consists of z+a^n*(x-z) for integer n and x different from z. Ordinary complex/subspace topology is used as an existence proof device, not as a regularity premise on the Boolean readout.",
    "Enumerate all nontrivial reference orbits and all distinct generated pairs. References are known generated values with actual allocated preparations; no computability or practical context-selection procedure is assumed."]
  conclusions := [
    "Accepted analytic nonnecessity construction awaiting artifacts: same-center nontrivial orbits coincide or are disjoint, while different-center intersections are finite. A bounded infinite intersection would force equal centers; for an unbounded intersection exponent differences are bounded and a repeated difference forces equal centers. Each orbit closure is its orbit plus center and is nowhere dense.",
    "Interleave orbit and pair stages. At each finite stage the colored domain is a finite union of processed full orbits plus finite witness points. A fresh orbit has finitely many constrained exponent positions; choose a positive period greater than all absolute differences of constrained positions, and extend periodically without overwriting. Skip duplicate orbits; singleton fixed orbits have period 1.",
    "At a pair stage for distinct x,y choose u and u+a*(y-x) outside the colored domain by avoiding finitely many translated nowhere-dense closures, and assign opposite Boolean values. The actual generated reference r=(1+I)*(u-a*x) realizes these two values as selected first outputs, proving the intended contextual separation.",
    "Every point is eventually covered and every installed orbit period persists. The final signature is intended to separate, yet for every z,x there is an orbit-dependent P>0 such that every n has equal responses at times n+P and n. The existing single-basis Law then exists, while ReferenceSettles fails by nonconstancy and periodicity.",
    "This would show the single-orbit time-zero nonperiodicity witness is not necessary even for Bool. Orbit-dependent periods do not provide a uniform common period; no necessity or finite verification claim for the single-trace criterion follows."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/NativeAllocatedPointwisePeriodicObservation.lean"]
  dependencies := ["native_single_trace_probability_criterion", "native_context_attenuation_record_boundary",
    "native_allocated_signature_law"]
  limits := [
    "This task is analytic only with no checked evidence. Orbit intersection/closure facts, consistent periodic extensions, fresh pair witnesses, coverage and all separation/periodicity/no-settling conclusions remain proof obligations.",
    "The construction is an exact mathematical existence argument, not a computable or practical detector, context-selection method, physical reference availability or probability provenance. Known references remain separately allocated.",
    "No unknown-token cloning, tensor or independence interpretation, multi-source probability-law extension, outcome actualization or QM closure is inferred."] }

def nativeUniformPeriodProbabilityCriterion : ResearchTask := {
  id := "native_uniform_period_probability_criterion"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use concrete generated G, arbitrary signature sigma:G to Omega, native referenceStep F_z and the existing complex scalar arithmetic backend. No topology on response labels or finite-codomain assumption is supplied.",
    "Define UniversalPeriod(sigma,L) by: for every z,x in G, sigma(F_z iterated L at x)=sigma(x). Absence of a common positive period means every L>0 has some generated z,x where this equality fails; it is not absence of all individually periodic traces."]
  conclusions := [
    "Checked equivalence: full G-contextual separation is equivalent to absence of a common positive UniversalPeriod, that is, for every L>0 there exist z,x with different responses at time L and time zero. The checked common contextual-return theorem gives a common positive period whenever a distinct pair collapses.",
    "For the converse, one-hole affine semantics gives selected scalar equality C(F_z iterated L at x)=F_(C(z)) iterated L at C(x). A global bare-signature period therefore lifts to full ResponseEq between x and F_z iterated L at x for every context C.",
    "Choose x=0,z=1. The Lth output is 1-a^L, which differs from 0 for L>0 because normSq(a^L)=(1/2)^L<1. Thus a global positive period gives a distinct collapsed pair, completing the checked equivalence without a topology premise.",
    "The checked generic signature criterion then gives the same if-and-only-if for existence of the existing generated single-basis six-field Law, and an adapter preserving the entire probability field of any supplied scalar Law under the no-common-period condition. Canonical scalar consistency remains separate."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeAllocatedUniversalPeriodLaw.lean"
      declarations := [
        "IDT.QMClosure.NativeAllocatedUniversalPeriodLaw.UniversalPeriod",
        "IDT.QMClosure.NativeAllocatedUniversalPeriodLaw.NoCommonPositivePeriod",
        "IDT.QMClosure.NativeAllocatedUniversalPeriodLaw.universalPeriod_zero",
        "IDT.QMClosure.NativeAllocatedUniversalPeriodLaw.context_reference_iterate",
        "IDT.QMClosure.NativeAllocatedUniversalPeriodLaw.responseEq_reference_iterate_of_universalPeriod",
        "IDT.QMClosure.NativeAllocatedUniversalPeriodLaw.reference_iterate_unit_zero_ne_zero",
        "IDT.QMClosure.NativeAllocatedUniversalPeriodLaw.separates_iff_noCommonPositivePeriod",
        "IDT.QMClosure.NativeAllocatedUniversalPeriodLaw.nonconstant_of_noCommonPositivePeriod",
        "IDT.QMClosure.NativeAllocatedUniversalPeriodLaw.law_nonempty_iff_noCommonPositivePeriod",
        "IDT.QMClosure.NativeAllocatedUniversalPeriodLaw.lawOfScalarOfNoCommonPositivePeriod",
        "IDT.QMClosure.NativeAllocatedUniversalPeriodLaw.lawOfScalarOfNoCommonPositivePeriod_probability"] }]
  plannedArtifacts := []
  dependencies := ["native_reference_settling", "native_context_attenuation_record_boundary",
    "native_allocated_signature_law"]
  limits := [
    "The universal-period predicate, affine context intertwining, distinct collapsed witness, separation and existing generated single-basis Law-existence equivalences, and identical-field Law adapter are kernel checked under the supplied complex scalar backend. Individual traces may be periodic with different periods; no individually nonperiodic-trace necessity is asserted.",
    "C(z) is a generated known reference that must be separately prepared. The intertwining equality is equality of selected scalar values, not equality of full retained arrays, histories or resource costs. The existing complex arithmetic backend is retained.",
    "Infinite reference/input/time quantification supplies no finite empirical certificate, physical detector or probability provenance, source availability, multi-source Law extension, actualization or QM closure."] }

def rawUniformPeriodProbabilityBridge : ResearchTask := {
  id := "raw_uniform_period_probability_bridge"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the existing original raw Data d, source v, structural laws and both full contextual DiagonalFixed premises at chosenZero and v from the checked raw stable bridge.",
    "Supply the original observation predicate: for every L>0 there exist actual reference and input programs r,p whose rawReferenceStep_r iterated L from rawValue(p) has signature different from signature(rawValue(p)). Program references are separately charged; no scalar coordinates or topology are observation data."]
  conclusions := [
    "Checked raw no-common-period bridge: per-index compiled signature correspondence and initial-signature equality transport the raw predicate to the native no-common-period condition for inducedSignature on G. The proof preserves actual program/context witnesses rather than inducting on bare signature equality.",
    "The native criterion gives induced contextual separation and hence a sufficient original ambient single-basis Law, with the entire probability field of any supplied scalar Law preserved and the unchanged six-field contract transported. Canonical scalar consistency remains separate.",
    "No ambient Law-existence if-and-only-if or full raw-carrier literal-state separation is asserted. The checked q=1/3 ambient-law/constant-induced-signature countercontrol remains compatible with this sufficient criterion.",
    "The infinite time/family predicate is not a finite empirical certificate. The exact time-L allocation Bp+L*Br counts tagged-source occurrences, not general resources, gates or wires; each occurrence remains charged and supplies no uniform physical resource bound."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ResponseAllocatedUniversalPeriodBridge.lean"
      declarations := [
        "IDT.QMClosure.ResponseAllocatedUniversalPeriodBridge.RawNoCommonPositivePeriod",
        "IDT.QMClosure.ResponseAllocatedUniversalPeriodBridge.induced_noCommonPositivePeriod_of_raw",
        "IDT.QMClosure.ResponseAllocatedUniversalPeriodBridge.separates_of_rawNoCommonPositivePeriod",
        "IDT.QMClosure.ResponseAllocatedUniversalPeriodBridge.lawOfScalarOfRawNoCommonPositivePeriod",
        "IDT.QMClosure.ResponseAllocatedUniversalPeriodBridge.lawOfScalarOfRawNoCommonPositivePeriod_probability",
        "IDT.QMClosure.ResponseAllocatedUniversalPeriodBridge.law_nonempty_of_rawNoCommonPositivePeriod"] }]
  plannedArtifacts := []
  dependencies := ["response_allocated_stable_bridge", "native_uniform_period_probability_criterion"]
  limits := [
    "Raw predicate definition, all-index transport, induced separation and sufficient ambient Law/whole-field adapters are kernel checked with both full contextual DiagonalFixed premises retained at chosenZero and v. Only the induced signature is separated; no ambient Law-existence equivalence or literal-state separation is asserted.",
    "Original raw evaluations and signatures of actual allocated programs are the observational premises. The Native-indexed complex backend is retained; it is not claimed Complex-free, and no scalar/topological observation datum is added.",
    "No physical source/frame availability, detector or probability provenance, unknown-token cloning, tensor or independence interpretation, multi-source probability-law extension, actualization or QM closure is inferred."] }

def fixedThreeWireFiniteMemoryFrequencyWall : ResearchTask := {
  id := "fixed_three_wire_finite_memory_frequency_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the existing native fixed-three-wire word K=A*B^3 and the first selected output x_n=(K^n e0)_0. The target readout is the existing selected squared-norm probability; no Born provenance is assumed.",
    "The detector class is a finite closed deterministic time-homogeneous complete-state system S, under repeated identical preparation, with a Boolean record and the exact limiting empirical frequency along one trajectory. The update rule and initial state may depend on the preparation."]
  conclusions := [
    "Checked native recurrence and denominator result: the scaled output w_n=2^n*x_n has integer real and imaginary components satisfying w_(n+2)=w_(n+1)-4*w_n+2^(n+1), with w_0=1 and w_1=1+i. Both components are odd for n>0, so the selected squared norm has reduced denominator 2^(2*n-1).",
    "For this finite complete-state deterministic detector class, every trajectory is eventually periodic with a positive period ell at most card S. Its exact limiting Boolean empirical frequency is k/ell for the number k of true records in one eventual period.",
    "If that exact limiting frequency equals the selected squared-norm target at n>0, the target's reduced denominator divides ell and card S is at least 2^(2*n-1). The three ports stay fixed while this conditional state-count lower bound grows. With binary encoding, at least 2*n-1 memory bits are required; the exponential lower bound counts states, not memory bits.",
    "The universal recurrence/parity/denominator theorem, finite deterministic eventual-period/frequency theorem and state-count integration are kernel checked. No fixed finite state carrier can fit all positive n, even when its rule, record and initial state depend on n. The original raw Law bridge retains both contextual DiagonalFixed premises and gives the same state-count bound. The earlier exact rational probe for n=1 through 12 remains finite evidence only."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeThreeWireProbabilityDenominator.lean"
      declarations := [
        "IDT.QMClosure.NativeThreeWireProbabilityDenominator.orbit_eq_matrix_power",
        "IDT.QMClosure.NativeThreeWireProbabilityDenominator.selectedAmplitude_recurrence",
        "IDT.QMClosure.NativeThreeWireProbabilityDenominator.realNumerator_odd",
        "IDT.QMClosure.NativeThreeWireProbabilityDenominator.imagNumerator_odd",
        "IDT.QMClosure.NativeThreeWireProbabilityDenominator.selectedAmplitude_gaussian",
        "IDT.QMClosure.NativeThreeWireProbabilityDenominator.selectedWeight_reduced",
        "IDT.QMClosure.NativeThreeWireProbabilityDenominator.selectedWeight_positive_odd_fraction",
        "IDT.QMClosure.NativeThreeWireProbabilityDenominator.denominator_dvd",
        "IDT.QMClosure.NativeThreeWireProbabilityDenominator.repeatedWord_selectedWeight"] },
    { sourcePath := "Proofs/QMClosure/FiniteDeterministicRecordFrequency.lean"
      declarations := [
        "IDT.QMClosure.FiniteDeterministicRecordFrequency.exists_periodic_tail",
        "IDT.QMClosure.FiniteDeterministicRecordFrequency.exists_eventually_periodic_orbit",
        "IDT.QMClosure.FiniteDeterministicRecordFrequency.exists_recordFrequency_limit",
        "IDT.QMClosure.FiniteDeterministicRecordFrequency.fraction_of_recordFrequency_tendsto"] },
    { sourcePath := "Proofs/QMClosure/NativeFiniteMemoryReadoutWall.lean"
      declarations := [
        "IDT.QMClosure.NativeFiniteMemoryReadoutWall.selectedWeight_requires_states",
        "IDT.QMClosure.NativeFiniteMemoryReadoutWall.no_fixed_finite_carrier_matches_all",
        "IDT.QMClosure.NativeFiniteMemoryReadoutWall.rawLaw_repeatedWord_probability",
        "IDT.QMClosure.NativeFiniteMemoryReadoutWall.rawLaw_probability_requires_states"] }]
  plannedArtifacts := []
  dependencies := ["native_mixer_infinite_order", "native_vacuum_probability_family"]
  limits := [
    "The cited universal native, finite deterministic frequency and integrated state-count results are kernel checked under their supplied contracts. The raw Law result retains the existing six-field Law and both full contextual DiagonalFixed premises at chosenZero and v; the state-count theorem supplies no detector or probability Law.",
    "The conclusion concerns only the exact limiting single-history frequency in the stated finite closed deterministic time-homogeneous complete-state detector class. It does not exclude stochastic detectors, external streams, ensembles, continuous or unbounded memory, or approximate empirical matching.",
    "No uniform detector across all preparations is required: the rule and initial state may depend on preparation, but any matching detector in this class must meet the corresponding state-count bound.",
    "Fixed three ports do not imply physically finite complete-state memory. No physical finite-memory assumption, detector realization, probability provenance, Born derivation, outcome actualization or QM closure is inferred."] }

def nativeFiniteStochasticPreparationWall : ResearchTask := {
  id := "native_finite_stochastic_preparation_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the existing native fixed-three-wire preparation word K=A*B^3, source e0 and selected squared-norm readout p_n=selectedWeight n under the supplied complex backend. Preparation depth n counts repetitions of the word, not repeated detector trials.",
    "Supply one uniform compositional hidden-preparation model across all depths: one finite state carrier S, one fixed real row-stochastic matrix P and fixed complex vectors mu and r, with prediction sum_i mu_i*((complexify P)^n*r)_i. Arbitrary fixed complex endpoints include real probability initial distributions and event readouts as a special case.",
    "The original raw Law corollary additionally supplies Data d, source v, its six-field probability Law and both full contextual DiagonalFixed premises at chosenZero and v. The existence and physical applicability of these premises are not conclusions of this wall."]
  conclusions := [
    "Checked native nondecay: the actual selectedWeight sequence satisfies 8*p_(n+4)+10*p_(n+3)+9*p_(n+2)+10*p_(n+1)+8*p_n=21. The factored homogeneous recurrence and positive second-order energy invariants, together with the checked denominator result, show that p_(n+q)-p_n does not tend to zero for any positive q.",
    "Checked algebraic spectral coefficient: lambda=(1+i*sqrt(15))/4 has normSq 1 and infinite order, with the latter established through the odd trace sequence. The actual native readout satisfies p_n=7/15+(2/9)*(lambda^n+conj(lambda)^n)+(2/45)*(lambda^(2*n)+conj(lambda)^(2*n)) in complex coordinates. Its lambda-twisted Cesaro mean tends to 2/9.",
    "Checked finite stochastic peripheral theorem: every unit-modulus eigenvalue with a nonzero eigenvector for complexify P has a positive root-of-unity exponent q at most card S. Alignment along positive edges follows from row stochasticity and the eigenvector equation; no irreducibility or rational-entry premise is required.",
    "Checked finite stochastic twisted-readout theorem: for any unit-modulus infinite-order phase, every fixed complex readout of a finite row-stochastic orbit has twisted Cesaro mean tending to zero. The proof uses the resolvent, a telescoping identity and a checked orbit bound. A standalone general Markov asymptotic-periodicity theorem is neither established nor required by this route.",
    "Checked integration: no such fixed finite model represents p_n at all depths or has prediction error tending to zero. The quantitative corollary is exactly: if every n satisfies norm(prediction_n-p_n) <= epsilon, then 2/9 <= epsilon. This is a nonsharp uniform-all-depth bound, with no pointwise-strict, eventual-bound or 4/9-optimum claim. The original raw Law no-vanishing-error bridge retains both DiagonalFixed premises and the supplied six-field Law.",
    "Checked finite-prefix control: for every supplied finite probability table g through horizon N, an explicit Fin(N+1) absorbing clock has a row-stochastic matrix, a normalized nonnegative point initial distribution and readout g at each clock state. The same prediction equals g(min n N) at every n, hence equals g(n) for n <= N and is constant after N.",
    "The native finite-prefix specialization has checked readout bounds using an explicit canonical Law as a mathematical consistency witness. The supplied table is encoded into the readout, not obtained as an independent prediction or probability origin; the model depends on N. Therefore finite-prefix agreement alone does not exclude the class of finite models with no common state-count bound."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeThreeWireNondecay.lean"
      declarations := [
        "IDT.QMClosure.NativeThreeWireNondecay.recurrenceEnergy_constant",
        "IDT.QMClosure.NativeThreeWireNondecay.recurrence_tendsto_zero",
        "IDT.QMClosure.NativeThreeWireNondecay.selectedWeight_recurrence",
        "IDT.QMClosure.NativeThreeWireNondecay.fourth_recurrence_tendsto_zero",
        "IDT.QMClosure.NativeThreeWireNondecay.selectedWeight_no_asymptotic_period"] },
    { sourcePath := "Proofs/QMClosure/FiniteStochasticPeripheral.lean"
      declarations := [
        "IDT.QMClosure.FiniteStochasticPeripheral.aligned_of_positive_edge",
        "IDT.QMClosure.FiniteStochasticPeripheral.exists_bounded_pow_eq_one"] },
    { sourcePath := "Proofs/QMClosure/NativeThreeWireSpectralCoefficient.lean"
      declarations := [
        "IDT.QMClosure.NativeThreeWireSpectralCoefficient.traceSequence_spectral",
        "IDT.QMClosure.NativeThreeWireSpectralCoefficient.lambda_normSq",
        "IDT.QMClosure.NativeThreeWireSpectralCoefficient.lambda_pow_ne_one",
        "IDT.QMClosure.NativeThreeWireSpectralCoefficient.selectedWeight_spectral",
        "IDT.QMClosure.NativeThreeWireSpectralCoefficient.selectedWeight_twistedCesaro_limit"] },
    { sourcePath := "Proofs/QMClosure/FiniteStochasticTwistedReadout.lean"
      declarations := [
        "IDT.QMClosure.FiniteStochasticTwistedReadout.shifted_det_ne_zero",
        "IDT.QMClosure.FiniteStochasticTwistedReadout.tendsto_coordinateMean_zero",
        "IDT.QMClosure.FiniteStochasticTwistedReadout.tendsto_twistedCesaroMean_zero"] },
    { sourcePath := "Proofs/QMClosure/NativeFiniteStochasticReadoutWall.lean"
      declarations := [
        "IDT.QMClosure.NativeFiniteStochasticReadoutWall.twisted_error_tendsto",
        "IDT.QMClosure.NativeFiniteStochasticReadoutWall.no_vanishing_error",
        "IDT.QMClosure.NativeFiniteStochasticReadoutWall.no_exact_representation",
        "IDT.QMClosure.NativeFiniteStochasticReadoutWall.uniform_error_lower_bound",
        "IDT.QMClosure.NativeFiniteStochasticReadoutWall.rawLaw_no_vanishing_error"] },
    { sourcePath := "Proofs/QMClosure/FiniteStochasticPrefix.lean"
      declarations := [
        "IDT.QMClosure.FiniteStochasticPrefix.clock_card",
        "IDT.QMClosure.FiniteStochasticPrefix.clockMatrix_rowStochastic",
        "IDT.QMClosure.FiniteStochasticPrefix.initial_nonnegative",
        "IDT.QMClosure.FiniteStochasticPrefix.initial_normalized",
        "IDT.QMClosure.FiniteStochasticPrefix.readout_bounds",
        "IDT.QMClosure.FiniteStochasticPrefix.prediction_eq_terminal_extension",
        "IDT.QMClosure.FiniteStochasticPrefix.prediction_eq_prefix",
        "IDT.QMClosure.FiniteStochasticPrefix.native_selectedWeight_bounds",
        "IDT.QMClosure.FiniteStochasticPrefix.native_readout_bounds",
        "IDT.QMClosure.FiniteStochasticPrefix.native_prediction_eq_prefix"] }]
  plannedArtifacts := []
  dependencies := ["native_mixer_infinite_order", "fixed_three_wire_finite_memory_frequency_wall"]
  limits := [
    "The finite-memory and uniform compositional hidden-preparation assumptions remain supplied mathematical contracts, without a physical justification. Preparation depth and detector trial count remain distinct.",
    "The exclusion concerns one fixed finite model across all preparation depths. It does not exclude n-dependent kernels, initial distributions or readouts, external drive, or unbounded or continuous memory. Finite-prefix models are explicitly possible and may depend on the chosen horizon.",
    "Within the stated fixed-model class, uniform error below 2/9 across every preparation depth is excluded. The bound is not asserted sharp and supplies no pointwise-strict or eventual-bound result.",
    "The native backend, original Law and both contextual fixedness premises retain their existing scope. No empirical confirmation, probability origin or actualization, physical detector construction, Born derivation or full QM closure is inferred. Manifest kernel-proof statuses remain unchanged."] }

def nativeFixedStateFiniteWindow : ResearchTask := {
  id := "native_fixed_state_finite_window"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the same native fixed-three-wire selectedWeight sequence p_n and supplied complex backend. Fix any finite carrier S, a real row-stochastic matrix P and arbitrary fixed complex endpoint vectors mu and r across preparation depths n. Empty S is allowed; n counts preparation-word repetitions, not detector trials.",
    "Use the checked native forced fourth-order recurrence and all-depth no_exact_representation obstruction under their existing mathematical contracts. A state-count upper bound card S <= M, when used, is externally supplied."]
  conclusions := [
    "Checked sequence-level Cayley-Hamilton: the characteristic polynomial of complexify P annihilates every fixed complex matrix readout. Checked monic initial-value uniqueness extends zero errors on the first d terms of an order-d monic recurrence to zero errors at every depth.",
    "For nonempty S, row stochasticity gives chi_Pc(1)=0. The checked monic product chi_Pc*Q4 of degree card S+4 annihilates both prediction and native target, hence their error. The empty-carrier case is checked separately at n=0, where prediction is zero and p_0=1.",
    "For every finite S, including empty S, every fixed real row-stochastic P and arbitrary fixed complex mu/r have a mismatch at some preparation depth n<card S+4. If card S<=M, a mismatch occurs at some n<M+4.",
    "If one such fixed model matches all N initial depths n<N exactly, then N<=card S+3, equivalently the natural-number lower bound N-3<=card S. Subtraction is truncated for short prefixes. Both corollaries allow arbitrary fixed complex endpoints and empty S.",
    "These are exact finite-window exclusions under supplied fixed-model and state-count contracts; no positive numerical error margin is inferred from this task alone."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FiniteReadoutRecurrence.lean"
      declarations := [
        "IDT.QMClosure.FiniteReadoutRecurrence.applyPolynomial_mul",
        "IDT.QMClosure.FiniteReadoutRecurrence.eq_zero_of_initial",
        "IDT.QMClosure.FiniteReadoutRecurrence.applyPolynomial_matrix_powers",
        "IDT.QMClosure.FiniteReadoutRecurrence.charpoly_annihilates"] },
    { sourcePath := "Proofs/QMClosure/NativeFixedStateFiniteWindow.lean"
      declarations := [
        "IDT.QMClosure.NativeFixedStateFiniteWindow.charpoly_prediction",
        "IDT.QMClosure.NativeFixedStateFiniteWindow.charpoly_eval_one",
        "IDT.QMClosure.NativeFixedStateFiniteWindow.nativePolynomial_monic",
        "IDT.QMClosure.NativeFixedStateFiniteWindow.nativePolynomial_natDegree",
        "IDT.QMClosure.NativeFixedStateFiniteWindow.nativePolynomial_forcing",
        "IDT.QMClosure.NativeFixedStateFiniteWindow.common_annihilator",
        "IDT.QMClosure.NativeFixedStateFiniteWindow.exists_mismatch_before_card_add_four",
        "IDT.QMClosure.NativeFixedStateFiniteWindow.exists_mismatch_before_bound_add_four",
        "IDT.QMClosure.NativeFixedStateFiniteWindow.match_prefix_requires_states",
        "IDT.QMClosure.NativeFixedStateFiniteWindow.prefix_state_lower_bound"] }]
  plannedArtifacts := []
  dependencies := ["native_finite_stochastic_preparation_wall"]
  limits := [
    "The model uses one fixed finite carrier, P, mu and r across preparation depths. No physical finite-memory or state-count bound, finite-precision error margin, statistical confidence or parameter-estimation protocol is supplied.",
    "Without a common state-count bound, the checked absorbing-clock construction still matches any supplied finite probability prefix. The exact witness does not contradict that finite-prefix control.",
    "No physical justification of the uniform preparation contract, experimental confirmation, probability origin or actualization, Born derivation or full QM closure is inferred. Manifest and public QM statuses remain unchanged."] }

def nativeFixedStateRobustWindow : ResearchTask := {
  id := "native_fixed_state_robust_window"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Fix a finite state carrier S and the same native target p_n. The supplied parameterFamily consists of one fixed real row-stochastic P, a fixed nonnegative real initial distribution mu summing to one, and a fixed real readout r with every entry in [0,1], across all preparation depths.",
    "The bounded endpoint contract is a hypothesis of this parameter-compactness proof. The checked exact finite-window exclusion and uniform-all-depth error lower bound retain their existing mathematical contracts."]
  conclusions := [
    "Checked compactness and continuity: row-stochastic kernels and the honest probability parameter family are compact; model predictions and finite prediction vectors depend continuously on those parameters.",
    "There exists an unspecified delta>0, uniform over this fixed-S family, such that every model has some preparation depth n<card S+4 with norm(prediction_n-p_n)>=delta.",
    "Separately, for every epsilon<2/9 there exists some finite N, uniform over the same family, such that every model has some n<N with norm(prediction_n-p_n)>epsilon. No effective N or identification of the exact-window delta with 2/9 is supplied.",
    "Both statements allow empty S; in that case the normalized initial-distribution family is empty and their model quantification is vacuous."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FiniteStochasticCompact.lean"
      declarations := [
        "IDT.QMClosure.FiniteStochasticCompact.isCompact_rowStochastic",
        "IDT.QMClosure.FiniteStochasticCompact.isCompact_parameterFamily",
        "IDT.QMClosure.FiniteStochasticCompact.continuous_modelPrediction",
        "IDT.QMClosure.FiniteStochasticCompact.continuous_finitePredictions",
        "IDT.QMClosure.FiniteStochasticCompact.exists_positive_window_gap",
        "IDT.QMClosure.FiniteStochasticCompact.exists_finite_threshold_window"] },
    { sourcePath := "Proofs/QMClosure/NativeFixedStateRobustWindow.lean"
      declarations := [
        "IDT.QMClosure.NativeFixedStateRobustWindow.exists_positive_gap_before_card_add_four",
        "IDT.QMClosure.NativeFixedStateRobustWindow.exists_finite_window_above_threshold"] }]
  plannedArtifacts := []
  dependencies := ["native_fixed_state_finite_window", "native_finite_stochastic_preparation_wall"]
  limits := [
    "Bounded honest endpoints are the scope of this parameter-compactness proof. The separate native_unbounded_endpoint_robust_window task removes endpoint bounds for an existential positive gap; the finite unspecified threshold window for each epsilon<2/9 is established here only for the bounded probability family.",
    "Neither a numerical delta nor an effective threshold-window length is computed. No finite-precision calibration, statistical confidence or parameter-estimation protocol is supplied.",
    "State count remains fixed. With no common state-count bound, checked prefix-clock controls still match any supplied finite probability window exactly. Preparation depth is not detector trial count.",
    "No physical finite-memory bound or justification of the uniform preparation contract, experimental confirmation, probability origin or actualization, Born derivation or full QM closure is inferred. Manifest and public QM statuses remain unchanged."] }

def nativeUnboundedEndpointRobustWindow : ResearchTask := {
  id := "native_unbounded_endpoint_robust_window"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Fix any finite carrier S, the same native target p_n and supplied complex backend. Use one fixed real row-stochastic P and arbitrary fixed complex endpoint vectors mu/r across preparation depths. No endpoint bound, normalization, probability interpretation or nonempty-carrier premise is required.",
    "Use the checked exact five-mode spectral decomposition, infinite order of lambda and finite stochastic peripheral eigenvalue obstruction under their existing mathematical contracts. The polynomial filter requires no new Cesaro limit or general Markov asymptotics."]
  conclusions := [
    "Checked finite polynomial filter: applying a polynomial to the actual native sequence multiplies each geometric mode by its polynomial value. For the stochastic characteristic-polynomial filter, vanishing of its first four residual terms extends to all depths through the native fourth-order recurrence and would force the polynomial value at lambda to vanish. A row-stochastic characteristic polynomial cannot vanish at lambda, so some residual (chi_Pc(E)*p)_k is nonzero for k<4, including for empty S.",
    "Checked continuity and normalization: characteristic-polynomial coefficients and the residual maximum depend continuously on P; the sum of coefficient norms is at least one, and the residual maximum is positive for row-stochastic P. The normalized residual is continuous and bounded above by the maximum prediction error on the first card S+4 depths via Cayley-Hamilton and the triangle inequality, independently of endpoint size.",
    "For each finite S there exists an unspecified delta_S>0 such that, for every real row-stochastic P and arbitrary fixed complex mu/r, some preparation depth n<card S+4 has norm(prediction_n-p_n)>=delta_S. Compactness is used only for stochastic P; endpoints need not lie in a compact or bounded set.",
    "The existential gap is not identified with 2/9 and no value is computed. The separate finite unspecified threshold-window theorem for each epsilon<2/9 remains established only for the bounded probability parameter family."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeReadoutPolynomialObstruction.lean"
      declarations := [
        "IDT.QMClosure.NativeReadoutPolynomialObstruction.applyPolynomial_geometric",
        "IDT.QMClosure.NativeReadoutPolynomialObstruction.applyPolynomial_selectedWeight",
        "IDT.QMClosure.NativeReadoutPolynomialObstruction.annihilator_eval_lambda_zero",
        "IDT.QMClosure.NativeReadoutPolynomialObstruction.charpoly_eval_lambda_ne_zero",
        "IDT.QMClosure.NativeReadoutPolynomialObstruction.exists_charpoly_residual_before_four"] },
    { sourcePath := "Proofs/QMClosure/NativeUnboundedEndpointRobustWindow.lean"
      declarations := [
        "IDT.QMClosure.NativeUnboundedEndpointRobustWindow.continuous_charpoly_coeff",
        "IDT.QMClosure.NativeUnboundedEndpointRobustWindow.continuous_complexify_charpoly_coeff",
        "IDT.QMClosure.NativeUnboundedEndpointRobustWindow.one_le_coefficientNormSum",
        "IDT.QMClosure.NativeUnboundedEndpointRobustWindow.residualMax_pos",
        "IDT.QMClosure.NativeUnboundedEndpointRobustWindow.continuous_normalizedResidual",
        "IDT.QMClosure.NativeUnboundedEndpointRobustWindow.normalizedResidual_le_windowError",
        "IDT.QMClosure.NativeUnboundedEndpointRobustWindow.exists_positive_gap_before_card_add_four"] }]
  plannedArtifacts := []
  dependencies := ["native_fixed_state_finite_window", "native_finite_stochastic_preparation_wall",
    "native_fixed_state_robust_window"]
  limits := [
    "Delta is existential and unspecified; no numerical gap, physical state-count bound, finite-precision guarantee or statistical protocol is supplied. With no common state-count bound, finite-prefix clock controls still apply.",
    "Preparation depth is not trial count; P and endpoints are fixed across depths. No physical memory bound, probability origin or actualization, Born derivation or full QM closure is inferred. Manifest and public QM statuses remain unchanged.",
    "The uncoded original-source route retains its raw operation/signature contract and both contextual DiagonalFixed premises. The separate raw_fixed_reference_preparation task constructs fixed changed references; their noncollapse and physical availability remain separate obligations. An already-selected p_n does not establish these premises noncircularly."] }

def rawFixedReferencePreparation : ResearchTask := {
  id := "raw_fixed_reference_preparation"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For the abstract core supply a raw operation f satisfying DiagonalNormalization.Laws: mediality and bookend. Define g(x)=f(x,x) and P(x)=f(x,f(x,f(x,x))). The core fixedness proof has no axioms beyond its explicit hypotheses.",
    "For the raw resource compiler supply arbitrary T and three known copies of each input source tag or vacuum port. No square/medial law on T or DecidableEq on source labels is required for this compiler.",
    "For observed fixedness supply response Data d and its quotient contracts. Probability conclusions additionally supply the complete six-field Law on rebased data and processed source, or the stated scalar-field and rebased RawNoCommonPositivePeriod premises."]
  conclusions := [
    "Checked minimal medial/bookend core: g(P(x))=P(x); if g(x)=x then P(x)=x; hence P(P(x))=P(x). The original square-swap three-copy word uses three gates and retains all three outputs, selecting port two. Known-source budget is three; all-vacuum tagged-source budget is zero while three vacuum ports and three gates remain.",
    "Checked negative control: the explicit nonzero pure-minus source (0,1) is sent to (0,0) by the raw retraction. This checked source collapse suffices to exclude a general noncollapse or source-preservation guarantee.",
    "Checked generic compilation: expand wires to iota+(iota+iota), triple source tags and vacuum inputs, prepare each original port with the three-gate word, then pad the original circuit on active wires. The actual selected preparation value defines the transformed zero and stock. compile_eval and full active-array equality hold for arbitrary T, and final garbage is exactly the retained preparation-midpoint garbage.",
    "Checked resources: width and each source-occurrence budget are exactly tripled; preparation uses three paired gates per original wire and total paired-gate count is three times original width plus the original paired-gate count. No unknown-input cloning or optimality is asserted.",
    "Checked observed adapter: actual original-circuit preparedReference is identified with the abstract retraction only through quotient-class equality and ResponseEq under observed laws. Actual prepared zero and processed source are fully contextually DiagonalFixed after rebasing; literal equality to the abstract raw term is not required.",
    "Checked response/compiler integration identifies the actual preparedValue with preparedReference and gives literal raw-value and reference-step equalities, plus CompiledNoCommonPositivePeriod equivalence, on the compiler image. These equalities do not quantify over every original program.",
    "Checked conditional probability adapters preserve all six fields on the rebased data and processed source: normSq representation, equality of probability fields and Law existence iff the processed quotient reference has infinite order. A supplied scalar-field adapter with rebased RawNoCommonPositivePeriod constructs a Law; neither an old Law nor an old noncollapse observation transfers automatically."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawFixedReferencePreparation.lean"
      declarations := [
        "IDT.QMClosure.RawFixedReferencePreparation.diagonal_retract_fixed",
        "IDT.QMClosure.RawFixedReferencePreparation.retract_eq_self_of_fixed",
        "IDT.QMClosure.RawFixedReferencePreparation.retract_idempotent",
        "IDT.QMClosure.RawFixedReferencePreparation.evalRaw_fixedReferenceWord",
        "IDT.QMClosure.RawFixedReferencePreparation.evalRaw_fixedReferenceWord_selected",
        "IDT.QMClosure.RawFixedReferencePreparation.eval_knownSourceProgram",
        "IDT.QMClosure.RawFixedReferencePreparation.budget_knownSourceProgram",
        "IDT.QMClosure.RawFixedReferencePreparation.eval_vacuumProgram",
        "IDT.QMClosure.RawFixedReferencePreparation.budget_vacuumProgram",
        "IDT.QMClosure.RawFixedReferencePreparation.Controls.collapsingSource_ne_zero",
        "IDT.QMClosure.RawFixedReferencePreparation.Controls.rawRetract_collapses"] },
    { sourcePath := "Proofs/QMClosure/FixedReferenceProgramCompilation.lean"
      declarations := [
        "IDT.QMClosure.FixedReferenceProgramCompilation.compile_eval",
        "IDT.QMClosure.FixedReferenceProgramCompilation.compile_active",
        "IDT.QMClosure.FixedReferenceProgramCompilation.compile_outputs",
        "IDT.QMClosure.FixedReferenceProgramCompilation.compile_garbage",
        "IDT.QMClosure.FixedReferenceProgramCompilation.compile_width",
        "IDT.QMClosure.FixedReferenceProgramCompilation.compile_budget",
        "IDT.QMClosure.FixedReferenceProgramCompilation.pairedGateCount_preparationWord",
        "IDT.QMClosure.FixedReferenceProgramCompilation.compile_pairedGateCount"] },
    { sourcePath := "Proofs/QMClosure/ResponseFixedReferencePreparation.lean"
      declarations := [
        "IDT.QMClosure.ResponseFixedReferencePreparation.rawCircuitOutputs_class",
        "IDT.QMClosure.ResponseFixedReferencePreparation.class_preparedReference",
        "IDT.QMClosure.ResponseFixedReferencePreparation.preparedReference_responseEq",
        "IDT.QMClosure.ResponseFixedReferencePreparation.preparedReference_diagonalFixed",
        "IDT.QMClosure.ResponseFixedReferencePreparation.rebased_zero_diagonalFixed",
        "IDT.QMClosure.ResponseFixedReferencePreparation.processedSource_diagonalFixed",
        "IDT.QMClosure.ResponseFixedReferencePreparation.rebased_source_local",
        "IDT.QMClosure.ResponseFixedReferencePreparation.probability_eq_normSq",
        "IDT.QMClosure.ResponseFixedReferencePreparation.probability_fields_equal",
        "IDT.QMClosure.ResponseFixedReferencePreparation.law_nonempty_iff_reference_infiniteOrder",
        "IDT.QMClosure.ResponseFixedReferencePreparation.lawOfScalarOfRawNoCommonPositivePeriod",
        "IDT.QMClosure.ResponseFixedReferencePreparation.lawOfScalarOfRawNoCommonPositivePeriod_probability",
        "IDT.QMClosure.ResponseFixedReferencePreparation.compiler_preparedValue_eq",
        "IDT.QMClosure.ResponseFixedReferencePreparation.compile_eval_rebased",
        "IDT.QMClosure.ResponseFixedReferencePreparation.compile_rawValue",
        "IDT.QMClosure.ResponseFixedReferencePreparation.rawReferenceStep_rebased",
        "IDT.QMClosure.ResponseFixedReferencePreparation.CompiledNoCommonPositivePeriod",
        "IDT.QMClosure.ResponseFixedReferencePreparation.compiledNoCommonPositivePeriod_iff",
        "IDT.QMClosure.ResponseFixedReferencePreparation.lawOfScalarOfCompiledNoCommonPositivePeriod",
        "IDT.QMClosure.ResponseFixedReferencePreparation.lawOfScalarOfCompiledNoCommonPositivePeriod_probability"] }]
  plannedArtifacts := []
  dependencies := ["source_local_original_semantics", "response_source_local_probability",
    "allocated_preparation_contexts"]
  limits := [
    "The raw compiler does not transport probabilities from a rebased single-basis Law to the whole original three-copy experiment: enlarged inputs may be multisource and retained garbage may be nonvacuum. The compiled nonperiodicity adapter preserves scalar probability fields only in the rebased Law. No erasure, conditioning or joint Law is introduced; joint availability of known sources remains supplied.",
    "Fixedness does not transfer old Laws or noncollapse to the prepared source. No useful Law, physical source/reference availability, outcome actualization, Born derivation or full QM closure follows without the stated additional premises. Manifest and public QM statuses remain unchanged."] }

def rawDoubledNormalizationCompiler : ResearchTask := {
  id := "raw_doubled_normalization_compiler"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For the generic compiler supply arbitrary raw T and g with T(z,z)=(g(z),g(z)); define normalizedWith=Prod.map g g composed with T. Supply two known copies of every initial source or vacuum input.",
    "The square-only corollary supplies diagonal synchronization and the existing normalizer, without mediality, fixed references or a chosen zero. The RawData adapter supplies its existing target normalizer; mediality remains a separate premise of the normalized algebra.",
    "The observed adapter supplies response Data and quotient contracts. CompiledLaw is a new six-field logical readout contract, whose probabilities are indexed by logical circuits and outcomes, with prepared_eq tested through coordinatewise full contextual ResponseEq of actual doubled compiled arrays."]
  conclusions := [
    "Checked generic macro: four raw gates on (inl i,inl j), (inr i,inr j), (inl i,inr i), (inl j,inr j) send a duplicated pair to the duplicated normalizedWith output. Homomorphic compilation of identity, sequence and both-rail permutations gives whole-array simulation for every circuit. The encoding is restored after each macro, using the initial copies once rather than supplying fresh copies at each step.",
    "Checked allocated program compiler: source and zero remain unchanged, input tags are duplicated, width and each source-occurrence budget double, and paired-gate count is four times the original. Complete raw output arrays and selected program evaluations simulate the normalized target. No source projection or selected-output nonzero guarantee is asserted.",
    "Checked observed simulation: the actual compiled raw output has the duplicated normalized quotient output as its full quotient array. Actual rails need only satisfy ResponseEq; literal equality of raw arrays under observed-only laws is not claimed. Injectivity of duplication makes coordinatewise full contextual output equivalence exactly equivalent to equality of normalized quotient prepared arrays.",
    "Checked logical Law equivalence: CompiledLaw d v is equivalent to WeightFreeRawProbability.Law on d.quotientData at the original classOf(v). The other five fields transfer and the entire probability field is preserved. Conditional normSq representation, probability-field uniqueness and Law nonemptiness iff the original quotient reference has infinite order require no DiagonalFixed premises, rebasing or source projection."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawDoubledNormalizationCompiler.lean"
      declarations := [
        "IDT.QMClosure.RawDoubledNormalizationCompiler.evalRaw_pairMacro",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.evalRaw_compileWord",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.diagonal_synchronization_of_square",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.evalRaw_compileWord_of_square",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.normalizedWith_rawData",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.evalRaw_compileWord_rawData",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.compileProgram_outputs",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.compileProgram_eval",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.compileProgram_eval_rawData",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.compileProgram_width",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.compileProgram_budget",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.compileWord_pairedGateCount",
        "IDT.QMClosure.RawDoubledNormalizationCompiler.compileProgram_pairedGateCount"] },
    { sourcePath := "Proofs/QMClosure/ResponseDoubledNormalizationCompiler.lean"
      declarations := [
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.evalRaw_compileWord_class",
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.encodedPrepared_class",
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.responseEq_iff_prepared_eq",
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.CompiledLaw",
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.toQuotientLaw",
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.fromQuotientLaw",
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.toQuotientLaw_probability",
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.fromQuotientLaw_probability",
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.quotientLawEquiv",
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.probability_eq_normSq",
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.probability_fields_equal",
        "IDT.QMClosure.ResponseDoubledNormalizationCompiler.law_nonempty_iff_reference_infiniteOrder"] }]
  plannedArtifacts := []
  dependencies := ["diagonal_normalization", "source_local_original_semantics",
    "allocated_preparation_contexts", "weight_free_raw_probability"]
  limits := [
    "The initial known-copy preparations and their physical joint availability remain supplied. The compiler is not an unknown-input cloning operation or a new source-noncollapse theorem. Normalized algebra still requires its own laws, including mediality where stated.",
    "CompiledLaw normalizes over logical iota, not physical rails iota+iota. Its locality field concerns complete four-gate macros, its permutations act on both rails, and each added logical vacuum position supplies two old-zero inputs. The vacuum-layout correspondence is not a raw-padding identity. Coordinatewise full contextual preparedEq is not a joint-detector premise.",
    "The equivalence does not identify the logical probability field with one rail, rail sums, a marginal, conditioning, postselection, a physical joint Law or actual outcomes. It does not transport the existing uncoded original single-basis Law. The checked raw_rail_readout_bridge supplies a conditional rail-contract-to-logical map, while raw_rail_vacuum_extension_wall shows extension is not automatic; physical actualization remains open.",
    "The contract covers complete compiled macros and both-rail permutations only, without intermediate partial-macro readouts, arbitrary single-rail gates or mixed-control grammar. ExistingMixedControlProbabilityWall remains unchanged.",
    "No physical preparation/readout implementation, outcome actualization, Born derivation or full QM closure is inferred. Manifest and public QM statuses remain unchanged."] }

def rawRailVacuumExtensionWall : ResearchTask := {
  id := "raw_rail_vacuum_extension_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply TwoSourceLaw for arbitrary raw T, chosen zero z and source v, indexed by two distinct source positions and all raw Native words. Its four fields are normalization over physical outputs, same-seed literal complete prepared-state consistency, covariance under all physical output permutations and literal raw zero-padding preservation on old rails.",
    "The generic wall uses no nonnegativity, spectator or calibration premise. Source positions, complete raw states and padding layouts are explicit contract data."]
  conclusions := [
    "Checked arbitrary-finite-width obstruction: no such TwoSourceLaw can coexist with a circuit whose complete prepared output is all chosen zero. Output permutations and prepared-state consistency force uniform probabilities; padding by two zeros contradicts normalized values at the two widths.",
    "Checked affine control over complex scalars: R(x,y)=(1-M1(x,y),1-M2(x,y)), zero 0 and source 1, satisfies square swap and mediality, has diagonal g(x)=1-x and normalizes to M. Its source pair maps to (0,0), giving the width-two versus width-four 1/2 versus 1/4 conflict and excluding TwoSourceLaw.",
    "Checked identity-response affine comparison: a canonical scalar Law and normalized evaluator equality give CompiledLaw nonemptiness and original quotient reference infinite order through the existing iff, without identifying the reconstructed group with standard complex addition. The same data has no actual RawRailReadoutBridge.RailLaw; both exclusions and logical Law existence are recorded together."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawRailVacuumExtensionWall.lean"
      declarations := [
        "IDT.QMClosure.RawRailVacuumExtensionWall.TwoSourceLaw",
        "IDT.QMClosure.RawRailVacuumExtensionWall.prepared_pad",
        "IDT.QMClosure.RawRailVacuumExtensionWall.constant_probability",
        "IDT.QMClosure.RawRailVacuumExtensionWall.no_law_of_zero_prepared",
        "IDT.QMClosure.RawRailVacuumExtensionWall.no_law_of_source_pair_zero"] },
    { sourcePath := "Proofs/QMClosure/AffineRawRailExtensionControl.lean"
      declarations := [
        "IDT.QMClosure.AffineRawRailExtensionControl.operation_square",
        "IDT.QMClosure.AffineRawRailExtensionControl.operation_medial",
        "IDT.QMClosure.AffineRawRailExtensionControl.operation_diagonal",
        "IDT.QMClosure.AffineRawRailExtensionControl.normalizedOperation_eq_mixer",
        "IDT.QMClosure.AffineRawRailExtensionControl.source_pair_zero",
        "IDT.QMClosure.AffineRawRailExtensionControl.no_twoSourceLaw",
        "IDT.QMClosure.AffineRawRailExtensionControl.encodedPrepared_eq_duplicate",
        "IDT.QMClosure.AffineRawRailExtensionControl.compiledLaw_nonempty",
        "IDT.QMClosure.AffineRawRailExtensionControl.original_quotient_reference_infiniteOrder",
        "IDT.QMClosure.AffineRawRailExtensionControl.no_railLaw",
        "IDT.QMClosure.AffineRawRailExtensionControl.compiled_law_and_no_railLaw"] }]
  plannedArtifacts := []
  dependencies := ["raw_doubled_normalization_compiler", "source_local_original_semantics",
    "weight_free_raw_probability", "raw_rail_readout_bridge"]
  limits := [
    "No original single-source Law or raw conserved squared norm is asserted. TwoSourceLaw and the relayout-aware RailLaw are distinct contracts; their exclusions here have separate adapters.",
    "A nonfixed zero alone is insufficient for this obstruction; readout-null sectors may exist. The wall concerns the stated complete-state, permutation and vacuum-extension contracts.",
    "The conditional raw_rail_readout_bridge requires supplied source, state and layout naturality. Categorical probability contracts do not supply physical outcome actualization, physical preparation availability, Born derivation or full QM closure. Manifest and public QM statuses remain unchanged."] }

def rawRailReadoutBridge : ResearchTask := {
  id := "raw_rail_readout_bridge"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For each finite logical iota and logical source s, supply RailLaw on every raw Native word over rails iota+iota, initialized from duplicate(originalBasis zero source s). Its fields are nonnegative probabilities normalized over physical output rails, same-seed complete coordinatewise contextual ResponseEq consistency, covariance under every physical output permutation and spectator locality for every raw pair.",
    "Supply the explicit relayout-aware vacuum field: each logical vacuum adds two original-zero rails, with railInl(inl i)=inl(inl i) and railInl(inr i)=inr(inl i). railPad relabels literal padding through ((iota+iota)+(kappa+kappa)) equivalently ((iota+kappa)+(iota+kappa)). This is an additional premise, not a consequence of an older literal-padding field."]
  conclusions := [
    "Checked six-field transfer: pair-summing corresponding rail probabilities on compileWord images gives the existing CompiledLaw, without diagonal fixedness of zero or source.",
    "Checked compiled-boundary readout: physical swap covariance and prepared consistency equate the two encoded rail probabilities, each equal to one half of the selected logical normSq probability. All RailLaws have equal probability fields on compiled words and imply infinite order of the original quotient reference; no converse existence or global raw uniqueness follows.",
    "Checked RailLaw erasure obstruction: at logical Fin 1, an original circuit ending with both rails equal to chosen zero excludes RailLaw using its own relayout-aware width-two to width-four padding. The source-pair-zero corollary applies to arbitrary Data and reference whenever d.operation(v,v) is the zero pair.",
    "Checked fixed positive control: the existing plus/minus-sector construction on complex pairs, zero 0, source (1,1) and identity signature admits RailLaw with Q=quadratic(1/2) and rail probability Q/2, equivalently total normSq/4. Conservation and the total weight of two supplied source copies verify the contract. The source is nonfixed, and CompiledLaw also exists; this is one fixed witness from an existing family."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawRailReadoutBridge.lean"
      declarations := [
        "IDT.QMClosure.RawRailReadoutBridge.RailLaw",
        "IDT.QMClosure.RawRailReadoutBridge.rawPrepared_railPad",
        "IDT.QMClosure.RawRailReadoutBridge.railPad_compileWord",
        "IDT.QMClosure.RawRailReadoutBridge.toCompiledLaw",
        "IDT.QMClosure.RawRailReadoutBridge.compiled_rails_responseEq",
        "IDT.QMClosure.RawRailReadoutBridge.compiled_left_probability",
        "IDT.QMClosure.RawRailReadoutBridge.compiled_right_probability",
        "IDT.QMClosure.RawRailReadoutBridge.compiled_probability_fields_equal",
        "IDT.QMClosure.RawRailReadoutBridge.law_nonempty_implies_reference_infiniteOrder",
        "IDT.QMClosure.RawRailReadoutBridge.no_law_of_zero_prepared",
        "IDT.QMClosure.RawRailReadoutBridge.no_law_of_source_pair_zero"] },
    { sourcePath := "Proofs/QMClosure/RawRailReadoutPositiveControl.lean"
      declarations := [
        "IDT.QMClosure.RawRailReadoutPositiveControl.Q_reference",
        "IDT.QMClosure.RawRailReadoutPositiveControl.Q_nonnegative",
        "IDT.QMClosure.RawRailReadoutPositiveControl.Q_conserved",
        "IDT.QMClosure.RawRailReadoutPositiveControl.duplicated_source_total",
        "IDT.QMClosure.RawRailReadoutPositiveControl.law",
        "IDT.QMClosure.RawRailReadoutPositiveControl.railLaw_nonempty",
        "IDT.QMClosure.RawRailReadoutPositiveControl.source_not_diagonal_fixed",
        "IDT.QMClosure.RawRailReadoutPositiveControl.zero_diagonal_fixed",
        "IDT.QMClosure.RawRailReadoutPositiveControl.compiledLaw_nonempty"] }]
  plannedArtifacts := []
  dependencies := ["raw_doubled_normalization_compiler",
    "original_gate_probability_wall", "weight_free_raw_probability"]
  limits := [
    "The rail law assigns one categorical outcome label from the complete rail set. Two source occurrences specify supplied preparation resources; they do not specify particle number, independent trials, or a joint click-pattern distribution.",
    "Coarse grouping and the complete raw-word contract are supplied categorical readout premises. The positive control is not a general physical existence theorem or a newly identified continuum; no actualization, unknown-input cloning or physical source/readout availability follows.",
    "The affine control has CompiledLaw but no actual RailLaw, so extension is not automatic. The bridge transports no existing original single-source Law, provides no converse for arbitrary data and proves uniqueness only on the compiled boundary.",
    "Relayout-aware vacuum naturality remains an additional premise. The theorem is a conditional rail-contract-to-logical map, without physical outcome actualization, Born derivation or full QM closure. Manifest and public QM statuses remain unchanged."] }

def sourceRichnessVacuumFixed : ResearchTask := {
  id := "source_richness_vacuum_fixed"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply arbitrary raw T with exact square-swap at chosen zero z. The richness implication additionally supplies Nonempty(TwoSourceLaw T z v) separately for every v distinct from z."]
  conclusions := [
    "Checked square-only obstruction: for a=(T(z,z)).1, square-swap yields T(z,z)=(a,a) and T(a,a)=(z,z), excluding TwoSourceLaw T z a through pair erasure.",
    "Checked richness implication: the additional all-v!=z source-Law premise forces a=z and T(z,z)=(z,z). No mediality, positivity or spectator premise is required; no other source fixedness is concluded."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawRailVacuumExtensionWall.lean"
      declarations := [
        "IDT.QMClosure.RawRailVacuumExtensionWall.diagonal_source_pair_zero_of_square",
        "IDT.QMClosure.RawRailVacuumExtensionWall.no_law_at_diagonal_zero_source_of_square",
        "IDT.QMClosure.RawRailVacuumExtensionWall.diagonal_zero_fixed_of_source_richness",
        "IDT.QMClosure.RawRailVacuumExtensionWall.operation_zero_fixed_of_source_richness"] }]
  plannedArtifacts := []
  dependencies := ["raw_rail_vacuum_extension_wall", "raw_doubled_normalization_compiler"]
  limits := [
    "Source richness is independently supplied across every nonzero raw source, not a consequence of a Law at one source, physical availability, faithfulness alone or distinctions invisible to readout. Square-swap alone supplies the excluded diagonal-image source, not chosen-zero fixedness.",
    "The conclusion concerns chosen zero only, without fixedness of other sources, physical preparation availability, outcome actualization, Born derivation or full QM closure. Manifest and public QM statuses remain unchanged."] }

def nativeSignedVariationSelection : ResearchTask := {
  id := "native_signed_variation_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply a real-valued SignedLaw with the five native fields other than nonnegative: normalization, literal prepared-state equality, output permutations, spectator locality and vacuum preservation. Signed values are not interpreted as physical probabilities before positivity is established.",
    "Supply EventwiseBoundedVariation: for EVERY finite native basis event (iota,s,c,i), choose a real bound C after that event and before all k>=1, bounding the selected-leaf absolute variation V_k of the actual tree(c,i,4*k+1). The bound may depend on the event but must control all its refinement depths."]
  conclusions := [
    "Checked exact finite bound: with p the parent signed readout and r the literal vacuum-split left readout, every k>=1 satisfies 2*(4^k-1)*abs(r-p/2)<=V_k. The proof uses actual tree phase counts and signed accounting; zero-padding values vanish through state consistency, permutations and their zero sum, without positivity.",
    "Checked eventwise selection: EventwiseBoundedVariation gives actual split halving at every finite event, hence a SignedHalvingLaw. Its explicitly supplied halving field is an intermediate interface, not a consequence of the five SignedLaw fields alone.",
    "Checked generalized Gaussian route: SignedHalvingLaw gives normSq readout on actual finite native basis events. Applied after bounded variation supplies halving, this proves nonnegativity and only then constructs the old six-field Law. The adapter preserves the ENTIRE polymorphic readout field; no positive Law is instantiated circularly before positivity.",
    "Checked reverse direction: every old six-field Law, mapped to SignedLaw, satisfies EventwiseBoundedVariation. The original Law and premise-irredundance result remain unchanged; old public positive-Law normSq wrappers and the old response_nonnegative specialization are preserved.",
    "Checked sharp realPart control at pair01, source index zero and output index zero: p=1/2, r=0 and halving defect 1/4. For k>=1 the selected variation is V_k=4^k/2, leaf count N_k=2*16^k and 8*V_k^2=N_k. Direct unboundedness shows this signed control does not satisfy EventwiseBoundedVariation. Per-port or fixed-width boundedness does not replace the all-depth premise."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeSignedAccounting.lean"
      declarations := [
        "IDT.QMClosure.NativeSignedAccounting.SignedLaw",
        "IDT.QMClosure.NativeSignedAccounting.SignedHalvingLaw",
        "IDT.QMClosure.NativeSignedAccounting.ofLaw",
        "IDT.QMClosure.NativeSignedAccounting.ofLaw_prob",
        "IDT.QMClosure.NativeSignedAccounting.vacuum_probability_zero",
        "IDT.QMClosure.NativeSignedAccounting.split_probability_sum"] },
    { sourcePath := "Proofs/QMClosure/NativeSignedPhaseVariation.lean"
      declarations := [
        "IDT.QMClosure.NativeSignedPhaseVariation.mass_deviation_mul_bound",
        "IDT.QMClosure.NativeSignedPhaseVariation.phase_count_mass_halving_of_bounded_variation"] },
    { sourcePath := "Proofs/QMClosure/NativeZeroPortSplitting.lean"
      declarations := [
        "IDT.QMClosure.NativeZeroPortSplitting.internal_zero_partner_halves"] },
    { sourcePath := "Proofs/QMClosure/NativeCoherentBranchDilation.lean"
      declarations := [
        "IDT.QMClosure.NativeCoherentBranchDilation.dilation_probability_left",
        "IDT.QMClosure.NativeCoherentBranchDilation.dilation_probability_right"] },
    { sourcePath := "Proofs/QMClosure/NativeScalarAmplitudeSufficiency.lean"
      declarations := [
        "IDT.QMClosure.NativeScalarAmplitudeSufficiency.same_source_amplitude_sufficiency"] },
    { sourcePath := "Proofs/QMClosure/NativeGaussianResponse.lean"
      declarations := [
        "IDT.QMClosure.NativeGaussianResponse.response_parallelogram",
        "IDT.QMClosure.NativeGaussianResponse.response_nonnegative"] },
    { sourcePath := "Proofs/QMClosure/NativeProbabilityUniqueness.lean"
      declarations := [
        "IDT.QMClosure.NativeProbabilityUniqueness.signedHalving_response_eq_gaussian_norm",
        "IDT.QMClosure.NativeProbabilityUniqueness.signedHalving_probability_eq_normSq",
        "IDT.QMClosure.NativeProbabilityUniqueness.native_probability_eq_normSq"] },
    { sourcePath := "Proofs/QMClosure/NativeSignedVariationSelection.lean"
      declarations := [
        "IDT.QMClosure.NativeSignedVariationSelection.EventwiseBoundedVariation",
        "IDT.QMClosure.NativeSignedVariationSelection.native_finite_refinement_variation_bound",
        "IDT.QMClosure.NativeSignedVariationSelection.native_vacuum_split_halves_of_bounded_variation",
        "IDT.QMClosure.NativeSignedVariationSelection.boundedVariation_toSignedHalvingLaw",
        "IDT.QMClosure.NativeSignedVariationSelection.probability_eq_normSq_of_bounded_variation",
        "IDT.QMClosure.NativeSignedVariationSelection.nonnegative_of_bounded_variation",
        "IDT.QMClosure.NativeSignedVariationSelection.boundedVariation_toLaw",
        "IDT.QMClosure.NativeSignedVariationSelection.boundedVariation_toLaw_entire_prob",
        "IDT.QMClosure.NativeSignedVariationSelection.ofLaw_eventwiseBoundedVariation"] },
    { sourcePath := "Proofs/QMClosure/NativeSignedVariationControl.lean"
      declarations := [
        "IDT.QMClosure.NativeSignedVariationControl.witness_parent_value",
        "IDT.QMClosure.NativeSignedVariationControl.witness_split_value",
        "IDT.QMClosure.NativeSignedVariationControl.witness_halving_defect",
        "IDT.QMClosure.NativeSignedVariationControl.witness_selectedVariation",
        "IDT.QMClosure.NativeSignedVariationControl.witness_leaf_count",
        "IDT.QMClosure.NativeSignedVariationControl.witness_variation_squared",
        "IDT.QMClosure.NativeSignedVariationControl.witness_variation_unbounded",
        "IDT.QMClosure.NativeSignedVariationControl.realPart_not_eventwiseBoundedVariation"] } ]
  plannedArtifacts := []
  dependencies := ["native_binary_phase_count_mass", "native_vacuum_probability_family",
    "native_binary_refinement_selection", "native_coherent_scalar_sufficiency",
    "native_gaussian_probability_selection"]
  limits := [
    "The eventwise variation condition is a new all-depth readout regularity assumption across unbounded finite refinement widths. It is not a bound for each individual apparatus or a physical detector-budget derivation. Boundedness at one event does not select the entire Law.",
    "Formal little-o, subcritical or liminf selection variants, full-output variation formulas, pointwise bounds and global all-output variation corollaries are outside this checked milestone. Such rate extensions remain analytic possibilities without checked evidence here.",
    "This alternative mathematical presentation applies only to actual finite native basis preparations. It supplies no arbitrary complex-preparation probability, physical probability interpretation, outcome actualization or full physical QM closure. Manifest and public QM statuses remain unchanged."] }

def responseClassPreparationCompiler : ResearchTask := {
  id := "response_class_preparation_compiler"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply response Data d, any finite logical quotient array q:iota to d.Space and an actual raw array y:iota+iota to V whose coordinatewise class array equals duplicate(q). No existence of such an available preparation is asserted."]
  conclusions := [
    "Checked raw-word congruence and compiler class identity: for arbitrary supplied logical quotient array q and representative array y with class array duplicate(q), the complete compiled output class array equals the duplicated normalized quotient output. The paired raw outputs are contextually ResponseEq."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ResponseClassPreparationCompiler.lean"
      declarations := [
        "IDT.QMClosure.ResponseClassPreparationCompiler.evalRaw_class_congr",
        "IDT.QMClosure.ResponseClassPreparationCompiler.evalRaw_compileWord_class_of_input",
        "IDT.QMClosure.ResponseClassPreparationCompiler.paired_output_responseEq"] }]
  plannedArtifacts := []
  dependencies := [
    "raw_doubled_normalization_compiler"]
  limits := [
    "No preparation existence, independent-source availability, unknown-input cloning, resource reduction or reduction of the supplied number of representatives will follow from this compiler identity.",
    "Categorical readout contracts supply no physical preparation availability, outcome actualization, Born derivation or full QM closure. Manifest and public QM statuses remain unchanged."] }

def signedRawRailVariationSelection : ResearchTask := {
  id := "signed_raw_rail_variation_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use SignedRailLaw as exactly RailLaw without nonnegative, retaining real signed readouts and the other five fields. Supply the new all-depth eventwise bounded-variation premise; signed values are not treated as physical probabilities before positivity is established on the stated domain."]
  conclusions := [
    "Checked five-field transfer: SignedRailLaw is exactly RailLaw without nonnegative. Pair-summing compiled rail readouts gives native SignedLaw, using full contextual prepared-state equality rather than a positive raw Law.",
    "Checked compiled accounting: corresponding compiled rails are equal; physical selected variation equals the logical selected-leaf variation exactly. Eventwise bounded variation transfers to the native law; a global all-output absolute bound is sufficient for this eventwise condition.",
    "Checked conditional selection: supplied eventwise bounded variation makes each compiled rail value half the logical normSq readout and constructs a positive logical CompiledLaw preserving the entire logical pair-summed field. This proves no positivity of the entire raw SignedRailLaw."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/SignedRawRailReadoutBridge.lean"
      declarations := [
        "IDT.QMClosure.SignedRawRailReadoutBridge.SignedRailLaw",
        "IDT.QMClosure.SignedRawRailReadoutBridge.toNativeSignedLaw",
        "IDT.QMClosure.SignedRawRailReadoutBridge.toNativeSignedLaw_prob",
        "IDT.QMClosure.SignedRawRailReadoutBridge.compiled_rails_equal",
        "IDT.QMClosure.SignedRawRailReadoutBridge.compiled_pair_probability",
        "IDT.QMClosure.SignedRawRailReadoutBridge.selectedVariation_eq_native",
        "IDT.QMClosure.SignedRawRailReadoutBridge.selectedVariation_le_global_bound",
        "IDT.QMClosure.SignedRawRailReadoutBridge.toNativeSignedLaw_eventwiseBoundedVariation",
        "IDT.QMClosure.SignedRawRailReadoutBridge.compiled_left_probability",
        "IDT.QMClosure.SignedRawRailReadoutBridge.compiled_right_probability",
        "IDT.QMClosure.SignedRawRailReadoutBridge.toCompiledLaw",
        "IDT.QMClosure.SignedRawRailReadoutBridge.toCompiledLaw_entire_prob"] }]
  plannedArtifacts := []
  dependencies := [
    "native_signed_variation_selection",
    "raw_rail_readout_bridge",
    "raw_doubled_normalization_compiler"]
  limits := [
    "The all-depth regularity condition remains supplied and eventwise; no physical detector-budget bound is inferred. Complete raw words outside the compiled boundary need not have nonnegative signed values.",
    "The contract assigns a categorical output label, without a joint click-pattern interpretation, physical rail-to-event identification or transport of an old original single-source Law.",
    "Categorical readout contracts supply no physical preparation availability, outcome actualization, Born derivation or full QM closure. Manifest and public QM statuses remain unchanged."] }

def signedRawRailBoundedNegativeControl : ResearchTask := {
  id := "signed_raw_rail_bounded_negative_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the existing plus/minus sector at fixed t=-1 with Q=-A+2B and per-rail signed readout Q/2, on doubled known-source preparations. The five SignedRailLaw fields hold without using any positivity-restricted witness theorem at t=-1."]
  conclusions := [
    "Checked fixed t=-1 signed control: Q=-A+2B and per-rail Q/2 satisfy all five SignedRailLaw fields. Separate sector totals equal two, so the absolute readout sum is at most three uniformly across all finite widths and all raw words.",
    "Checked exact witness bridge: the old Original Fin 3 witness equals the left-only raw Native word on Fin 3 plus Fin 3 with chronological pairs 01, then 02, then 12. Its selected rail readout is -3/16, computed directly without a positivity-constrained witness_probability theorem at t=-1.",
    "Checked joint control: global absolute bound three and EventwiseBoundedVariation coexist with a negative raw rail. Thus the positive compiled-boundary result does not extend to positivity on arbitrary raw words."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/SignedRawRailNegativeControl.lean"
      declarations := [
        "IDT.QMClosure.SignedRawRailNegativeControl.sector_totals",
        "IDT.QMClosure.SignedRawRailNegativeControl.Q_conserved",
        "IDT.QMClosure.SignedRawRailNegativeControl.law",
        "IDT.QMClosure.SignedRawRailNegativeControl.total_absolute_rail_weight_le_three",
        "IDT.QMClosure.SignedRawRailNegativeControl.eventwiseBoundedVariation",
        "IDT.QMClosure.SignedRawRailNegativeControl.evalRaw_originalNative",
        "IDT.QMClosure.SignedRawRailNegativeControl.leftWitness_literal",
        "IDT.QMClosure.SignedRawRailNegativeControl.leftWitness_negative_value",
        "IDT.QMClosure.SignedRawRailNegativeControl.globally_bounded_with_negative_rail"] }]
  plannedArtifacts := []
  dependencies := [
    "signed_raw_rail_variation_selection",
    "original_gate_probability_wall"]
  limits := [
    "The t=-1 construction is a signed categorical control, without a physical probability interpretation. Its uniform absolute bound does not establish nonnegativity away from the compiled boundary.",
    "Categorical readout contracts supply no physical preparation availability, outcome actualization, Born derivation or full QM closure. Manifest and public QM statuses remain unchanged."] }

def globalDirectionReversibilityBoundary : ResearchTask := {
  id := "global_direction_reversibility_boundary"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Fix one autonomous update T on the complete state and a score F valued in a partial order. The first route assumes nonincrease at every state and a positive return period separately at every state.",
    "The reversal route retains all-state score nonincrease and replaces the return-period premise by supplied R with T composed with R composed with T equal to R and F composed with R equal to F. An involutive interpretation of R is an additional premise, unnecessary for the algebraic identity."]
  conclusions := [
    "Checked partial-order boundary: all-state score nonincrease and a positive complete-state return imply score invariance; pointwise positive periods and finite permutations give the corresponding corollaries. The reversal theorem also retains all-state nonincrease and uses the supplied reversal identity and reversal-invariant score.",
    "Checked integer control: the involutions n maps to -n and n maps to 1-n compose to translation with a strictly decreasing score -n. This score is not globally nonincreasing under either constituent involution, so the control does not meet that premise for both maps.",
    "Checked universal clock extension: for arbitrary local f, L(x,n)=(f(x),n+1) has L^k(x,n)=(f^k(x),n+k), preserves the selected projected readout r composed with fst along its trajectory, has a strictly descending score -n and no positive full-state return. Bijectivity transfers from f. A local four-cycle supplies an explicit local-return control despite full-state descent.",
    "The existing NativeMixerInfiniteOrder.native_word_infinite_order artifact is reused through the dependency, not duplicated. Infinite order of a map does not assert that every orbit is nonperiodic."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/GlobalDirectionAndLocalReversibility.lean"
      declarations := [
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.score_eq_of_positive_return",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.score_eq_of_pointwise_periodic",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.finite_perm_score_invariant",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.score_eq_of_reversal",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.integerA_involutive",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.integerB_involutive",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.integerTranslation_strict_descent",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.integerA_not_globally_descending",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.integerB_not_globally_descending",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.clockLift_iterate",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.clockLift_readout_iterate",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.clockLift_strict_descent",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.clockLift_no_positive_return",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.clockLift_bijective",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.fourCycle_return",
        "IDT.QMClosure.GlobalDirectionAndLocalReversibility.local_return_with_full_descent"] }]
  plannedArtifacts := []
  dependencies := [
    "native_mixer_infinite_order"]
  limits := [
    "Complete-state autonomy and all-state score monotonicity must remain explicit; a local projection is not the complete state. The appended clock is compatible with readouts that ignore it, without indistinguishability for global observations.",
    "No physical availability, time reversal symmetry, energy, entropy, temporal arrow explanation or definition of physical time follows. No additional bounded-score or universal nonreturn claim for arbitrary dynamics is asserted. These are algebraic hypothesis boundaries, not a claim about nature or a Born/full QM status upgrade."] }

def reversibleResetEnvironmentCapacity : ResearchTask := {
  id := "reversible_reset_environment_capacity"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply an injective complete update, a fixed initial environment and an admissible set of input labels. Require identical outputs on ALL retained subsystem coordinates for those inputs."]
  conclusions := [
    "Checked injective erasure boundary: an injective complete update with fixed initial environment and identical ALL retained subsystem outputs forces an injective environment encoding of admissible input labels. The prepared-input adapter retains the required injectivity contract.",
    "Checked finite capacity: admissible-label cardinality is at most environment cardinality. For the complete word language Fin n to A this gives |A|^n<=|E|; restricted languages use their own cardinality. Independent variation is combinatorial, without a probabilistic independence premise.",
    "Checked SWAP control: an injective update resets the subsystem and leaves the environment output equal to the input label, with a bijective environment map. It saturates the label-capacity bound without supplying refreshed environment resources."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ReversibleErasureEnvironment.lean"
      declarations := [
        "IDT.QMClosure.ReversibleErasureEnvironment.environment_injective_of_constant_subsystem",
        "IDT.QMClosure.ReversibleErasureEnvironment.environment_injective_of_update",
        "IDT.QMClosure.ReversibleErasureEnvironment.environment_injective_of_prepared_update",
        "IDT.QMClosure.ReversibleErasureEnvironment.capacity_of_constant_subsystem",
        "IDT.QMClosure.ReversibleErasureEnvironment.capacity_of_update",
        "IDT.QMClosure.ReversibleErasureEnvironment.full_block_capacity",
        "IDT.QMClosure.ReversibleErasureEnvironment.restricted_block_capacity",
        "IDT.QMClosure.ReversibleErasureEnvironment.swapUpdate_injective",
        "IDT.QMClosure.ReversibleErasureEnvironment.swapUpdate_reset",
        "IDT.QMClosure.ReversibleErasureEnvironment.swapUpdate_environment_identity",
        "IDT.QMClosure.ReversibleErasureEnvironment.swapUpdate_environment_bijective"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "Injectivity concerns the complete retained outputs, not a selected subsystem projection. The finite bounds do not assert a further all-n impossibility theorem or quantum capacity statement.",
    "No environment-refresh mechanism, ongoing reset availability, heat, entropy or energy identification is supplied. No physical preparation availability, outcome actualization, cosmological claim or full QM closure follows."] }

def crossScalePrimitiveComparison : ResearchTask := {
  id := "cross_scale_primitive_comparison"
  stage := .openPhysicalBridge
  review := .openObligation
  assumptions := [
    "Compare closed finite bijective dynamics, irreversible rewrite or order-growth dynamics, locally reversible dynamics with an evolving environment, and contextual or probabilistic process families. No family is selected as a winner.",
    "Keep quantum interference and macroscopic entanglement; stable matter, memory and thermal fluctuations; causality and gravity; and expansion, acceleration, CMB, lensing and growth as separate obligations. V8PrimitiveEmpiricalConstraintLedger inventories 46 families. The overall candidate is unassessed; QM has partial executable coverage, while the other sectors remain unassessed. This comparison changes none of their statuses.",
    "A shared cosmic forward model must connect rulers, distances, perturbations and light deflection using declared anchors rather than independently tuned functions. Treat observations motivating dark matter, including dynamics, lensing and growth, and observations of accelerated expansion motivating dark energy, without choosing an ontology in advance."]
  conclusions := [
    "The comparison remains an open physical bridge. Current algebra supplies hypotheses to test, not a complete account of observations or a selection of the laws of nature."]
  checkedEvidence := []
  plannedArtifacts := []
  dependencies := []
  limits := [
    "External context only, not Lean evidence: Kotler mechanical entanglement, https://arxiv.org/abs/2004.05515; Berut thermal erasure and fluctuations, https://www.cpt.univ-mrs.fr/~verga/pdfs/Berut-2012yq.pdf; conditional GW170817 timing constraints, https://arxiv.org/abs/1710.05834.",
    "External context only, not Lean evidence: Planck, https://arxiv.org/abs/1807.06209; DESI DR2 distances, https://arxiv.org/abs/2503.14738v3; DES Y3 joint three-by-two-point analysis, https://arxiv.org/abs/2105.13549v3.",
    "No checked physics evidence or planned theorem is registered for this comparison. Physical availability, parameter provenance and joint observational consistency require separate evidence. No completed QM or GR derivation, dark-sector explanation or public claim upgrade is asserted."] }

def homogeneousProductInterchange : ResearchTask := {
  id := "homogeneous_product_interchange"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply two jointly homogeneous two-port maps F and G over commutative scalars, including the complex instance, and an array with entries a_i*b_j."]
  conclusions := [
    "Over any CommMonoid K, all-scalar JointHomogeneous maps F and G act on scalar product arrays by changing the first factor under columns F and the second factor under rows G. Both orders equal productArray (F a) (G b), even for distinct F and G.",
    "The checked interchange theorem needs no additivity, square-swap, conservation or continuity. Its domain is product arrays only; it supplies no interchange theorem for arbitrary arrays."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/HomogeneousProductInterchange.lean"
      declarations := [
        "IDT.QMClosure.HomogeneousProductInterchange.rows_productArray",
        "IDT.QMClosure.HomogeneousProductInterchange.columns_productArray",
        "IDT.QMClosure.HomogeneousProductInterchange.columns_rows_productArray",
        "IDT.QMClosure.HomogeneousProductInterchange.rows_columns_productArray",
        "IDT.QMClosure.HomogeneousProductInterchange.interchange_productArray"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "Product notation describes a scalar-array factorization, not a physical tensor-product structure or independent subsystem availability.",
    "These are checked conditional algebraic statements. No physical preparation availability, outcome actualization, Born derivation or full QM closure is inferred. Public and manifest statuses remain unchanged."] }

def vacuumRecordUncomputeControl : ResearchTask := {
  id := "vacuum_record_uncompute_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply arbitrary F from complex pairs to complex pairs with square-swap, agreeing with the native gate on both kinds of one-zero input. Use four retained ports labelled 00, 01, 10 and 11, with actual basis source at port zero."]
  conclusions := [
    "For generic F over concrete complex scalars, the checked literal circuits are S=pair02, C=the permutation swapping ports two and three, and R=three repetitions of pair02 followed by three repetitions of pair13. With the native coefficients a,b, S prepares (a,0,b,0), C after S prepares (a,0,0,b), and R after C after S prepares (1/2,1/2,i/2,-i/2). R after S and R after C after C after S both return (1,0,0,0). C is an involution on every retained array.",
    "The amplitude identities require square-swap and native agreement on the indicated one-zero inputs, with no mediality, linearity, homogeneity, tensor, purity or probability premise. With the SAME supplied BalancedNonmedialMixerWitness.rawLaw of BalancedNonmedialMixerCore.gate, the marked output has four probabilities 1/4; the unmarked and uncomputed outputs are point distributions. The unmarked, marked and uncomputed row {0,1} weights are respectively 1, 1/2 and 1. The checked protocol is compatible with this gate's failure of FirstChannelMedial."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/VacuumRecordUncomputeControl.lean"
      declarations := [
        "IDT.QMClosure.VacuumRecordUncomputeControl.C_involution",
        "IDT.QMClosure.VacuumRecordUncomputeControl.split_output",
        "IDT.QMClosure.VacuumRecordUncomputeControl.recorded_output",
        "IDT.QMClosure.VacuumRecordUncomputeControl.marked_output",
        "IDT.QMClosure.VacuumRecordUncomputeControl.unmarked_output",
        "IDT.QMClosure.VacuumRecordUncomputeControl.uncomputed_output"] },
    { sourcePath := "Proofs/QMClosure/VacuumRecordUncomputeControl.lean"
      declarations := [
        "IDT.QMClosure.VacuumRecordUncomputeControl.balanced_marked_probability",
        "IDT.QMClosure.VacuumRecordUncomputeControl.balanced_unmarked_probability",
        "IDT.QMClosure.VacuumRecordUncomputeControl.balanced_uncomputed_probability",
        "IDT.QMClosure.VacuumRecordUncomputeControl.protocol_passes_without_mediality"] }]
  plannedArtifacts := []
  dependencies := [
    "continuous_balanced_nonmedial_wall"]
  limits := [
    "All four ports remain retained. Recording and uncomputing name mathematical circuit operations; physical records, actualization and independently available subsystems are not conclusions.",
    "These are checked conditional circuit identities and a supplied-law control. No physical preparation availability, outcome actualization, Born derivation or full QM closure is inferred. Public and manifest statuses remain unchanged."] }

def generatedNonmedialAxisProbe : ResearchTask := {
  id := "generated_nonmedial_axis_probe"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the existing BalancedNonmedial gate and its own complete six-field rawLaw, without introducing a new model. All eight outputs remain retained.",
    "Use the actual unit-reference basis input at port zero and the preparation pair04; pair02; pair46; pair01; pair23; pair45; pair67, each initially meeting vacuum. The intended tested rows are {3,5,0,4} and {1,6,2,7}."]
  conclusions := [
    "The checked eight-wire preparation has exact leaf array [(-1+i)/4,(1+i)/4,(1+i)/4,(1-i)/4,(1+i)/4,(1-i)/4,(1-i)/4,(-1-i)/4]. Its selected block at ports (3,5,1,6) is q*(1,1,i,1), where q=(1-i)/4; the selected minor is nonzero, excluding a scalar product array in the tested grouping.",
    "Let A be pair31; pair56; pair02; pair47 and B be pair35; pair16. In the SAME BalancedNonmedialMixerWitness.rawLaw, the complete row {3,5,0,4} weights are: preparation then A gives 1/2; preparation then B then A gives 3/8+121/(16*sqrt(2993))>1/2; preparation then A then B gives 1/2. The two displayed rows partition all eight retained outputs, and the law normalizes the sum over all eight outputs for every circuit.",
    "The checked same-model continuation sensitivity compares these specified componentwise row and column lifts of BalancedNonmedialMixerCore.gate. The same gate also satisfies all-scalar JointHomogeneous and product-input interchange. The existing three-gate raw-versus-native distinction is prior work; this is not the first generated nonlinear distinction."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/GeneratedNonmedialAxisProbe.lean"
      declarations := [
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.prep_output",
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.prep_output_explicit",
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.selected_block_minor_ne_zero",
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.rows_partition",
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.all_outputs_normalized"] },
    { sourcePath := "Proofs/QMClosure/GeneratedNonmedialAxisProbe.lean"
      declarations := [
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.row0_afterA",
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.row0_afterBA",
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.row0_afterBA_gt_half",
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.row0_afterAB",
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.same_model_axis_continuation_sensitivity",
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.gate_jointHomogeneous",
        "IDT.QMClosure.GeneratedNonmedialAxisProbe.product_input_interchange"] }]
  plannedArtifacts := []
  dependencies := [
    "continuous_balanced_nonmedial_wall",
    "raw_observable_medial_wall",
    "homogeneous_product_interchange",
    "vacuum_record_uncompute_control"]
  limits := [
    "A physical factorization into independently controllable parties remains an explicit open bridge. Serial overlapping-gate order dependence is not physical signalling.",
    "The test concerns the specified componentwise row and column lifts, not every possible composite realization of the nonlinear gate. These are checked same-model mathematical statements. No physical preparation availability, outcome actualization, Born derivation or full QM closure is inferred. Public and manifest statuses remain unchanged."] }

def sparseMarginalMedialCriterion : ResearchTask := {
  id := "sparse_marginal_medial_criterion"
  stage := .analyticAwaitingFormalization
  review := .parentAccepted
  assumptions := [
    "Supply F from complex pairs to complex pairs, writing F(x,z)=(g(x,z),h(x,z)), with square-swap, diagonal transparency, normSq-sum conservation, joint complex homogeneity and native right-vacuum action F(z,0)=(a*z,b*z), where a=(1+i)/2 and b=(1-i)/2. Plan to infer left-vacuum action."]
  conclusions := [
    "Accepted analytic plan, pending kernel check: with f(x,z)=normSq(g(x,z)), define universal sparse-three marginal condition S by f(g(x,y),a*z)+f(h(x,y),b*z)=f(x,z)+normSq(y)/2 for every complex x,y,z. Under the supplied base, prove S iff literal FirstChannelMedial iff RowColumnCommutes.",
    "Plan auxiliary K(x,z)=f(x,z)-(normSq(x)+normSq(z))/2 and H(x,z)=K(x,i*z)+i*K(x,z). Derive the required separation of H from square-swap and vacuum action; do not assume that separation. With coherent-sum conservation added, plan to prove F(x,y)=(a*x+b*y,b*x+a*y), with no continuity premise.",
    "Plan to show that the SAME BalancedNonmedialMixerCore.gate fails S at (x,y,z)=(1,1,1+i), using its existing selectedPlus values. This is an analytic target, not checked evidence for the criterion or its equivalences."]
  checkedEvidence := []
  plannedArtifacts := [
    "Proofs/QMClosure/SparseMarginalMedialCriterion.lean"]
  dependencies := [
    "continuous_balanced_nonmedial_wall",
    "generated_nonmedial_axis_probe",
    "raw_network_medial_wall"]
  limits := [
    "Universal sparse joint-preparation coverage is not supplied; the generated finite probe does not establish all complex triples. A common fixed interface, compiler, spectator and scaling bridge remains open.",
    "The complex carrier, normSq readout and native vacuum action are imported hypotheses. These are tests of an existing source hypothesis, not a selection of nature or a physical Born, QM or no-signalling derivation. All conclusions remain analytic pending kernel check; public and manifest statuses remain unchanged."] }

def rawSparseMarginalReconstruction : ResearchTask := {
  id := "raw_sparse_marginal_reconstruction"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply a pointed raw carrier V with zero and a total F : V*V -> V*V satisfying square-swap and diagonal transparency. Supply real-valued W with W(0)=0 and pair-weight conservation. Write m(x,z)=fst(F(x,z)), h(x,z)=snd(F(x,z)), A(x)=m(x,0), B(x)=m(0,x), u(x)=W(A(x)) and v(x)=W(B(x)).",
    "Assume the universal actual sparse row-marginal condition on [[x,y],[z,0]]: W(m(m(x,y),A(z)))+W(m(h(x,y),B(z)))=W(m(x,z))+W(A(y)) for every raw triple x,y,z. Add W>=0 on all raw states, including every iterate, for weight descent, observational equivalence and the Hilbert reconstruction. No vacuum half-balance, complex raw carrier, raw addition, homogeneity, phase, split bijections, faithfulness or topology is assumed."]
  conclusions := [
    "With K(x,z)=W(m(x,z))-u(x)-v(z), the checked actual sparse law implies pair conservation of u and the kernel marginal law. In the signed-weight stage this gives split adjoints, commuting kernel actions, K(m(x,y),z)=K(x,B(z))+K(y,A(z)), congruence of K-profile equality and mediality modulo K-profile equality. No signed-weight descent of W or equivalence with ObservationalEq is claimed.",
    "For q(x)=2*K(x,A(A(x))) and r(x)=W(x)-q(x), the checked identities give q(A(x))=q(x)/2 and r(A^4(x))=-r(x)/4. For every natural k, 16^k*W((A^4)^k(x))=q(x)+(-4)^k*r(x). With W>=0 on all raw states and iterates, the scaled right side is nonnegative for every k; the real Archimedean argument forces r=0. Consequently W=q and both W(A(x))=W(x)/2 and W(B(x))=W(x)/2 hold, without a vacuum half-balance input.",
    "Under the explicit nonnegativity hypothesis, W descends through KernelEq, KernelEq is equivalent to the existing one-hole arbitrary-reference ObservationalEq, and the actual sparse law is equivalent to ObservedMedial. The checked construction supplies existing ObservedData, quotientData, Hilbert and feature, with feature norm-square equal to W and feature equality equivalent to ObservationalEq. A supplied positive-weight witness has nonzero feature; no positive witness is supplied by the contract."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawSparseMarginalReconstruction.lean"
      declarations := [
        "IDT.QMClosure.RawSparseMarginalReconstruction.u_conserved",
        "IDT.QMClosure.RawSparseMarginalReconstruction.sparse_implies_kernel",
        "IDT.QMClosure.RawSparseMarginalReconstruction.K_A_adjoint",
        "IDT.QMClosure.RawSparseMarginalReconstruction.K_B_adjoint",
        "IDT.QMClosure.RawSparseMarginalReconstruction.K_AB_commute",
        "IDT.QMClosure.RawSparseMarginalReconstruction.K_m",
        "IDT.QMClosure.RawSparseMarginalReconstruction.kernelEq_m_congr",
        "IDT.QMClosure.RawSparseMarginalReconstruction.kernel_medial",
        "IDT.QMClosure.RawSparseMarginalReconstruction.q_A",
        "IDT.QMClosure.RawSparseMarginalReconstruction.r_fourthVacuum",
        "IDT.QMClosure.RawSparseMarginalReconstruction.scaled_weight_iterate",
        "IDT.QMClosure.RawSparseMarginalReconstruction.scaled_weight_iterate_nonnegative",
        "IDT.QMClosure.RawSparseMarginalReconstruction.r_eq_zero",
        "IDT.QMClosure.RawSparseMarginalReconstruction.weight_eq_q",
        "IDT.QMClosure.RawSparseMarginalReconstruction.weight_A",
        "IDT.QMClosure.RawSparseMarginalReconstruction.weight_B",
        "IDT.QMClosure.RawSparseMarginalReconstruction.kernelEq_weight_eq",
        "IDT.QMClosure.RawSparseMarginalReconstruction.kernelEq_iff_observationalEq",
        "IDT.QMClosure.RawSparseMarginalReconstruction.sparse_marginal_iff_observed_medial",
        "IDT.QMClosure.RawSparseMarginalReconstruction.observedData",
        "IDT.QMClosure.RawSparseMarginalReconstruction.quotientData",
        "IDT.QMClosure.RawSparseMarginalReconstruction.Hilbert",
        "IDT.QMClosure.RawSparseMarginalReconstruction.feature",
        "IDT.QMClosure.RawSparseMarginalReconstruction.norm_feature_sq",
        "IDT.QMClosure.RawSparseMarginalReconstruction.feature_eq_iff_observationalEq",
        "IDT.QMClosure.RawSparseMarginalReconstruction.feature_ne_zero_of_positive_weight"] }]
  plannedArtifacts := []
  dependencies := [
    "operational_context_quotient",
    "raw_network_medial_wall",
    "generated_nonmedial_axis_probe"]
  limits := [
    "Universal actual sparse compatibility remains an imported primitive. Coverage of all joint triples and arbitrary fixed references is not supplied by source-generated preparations; independent physical interfaces remain open. Vacuum half-balance is a checked conclusion under nonnegativity, not an input hypothesis.",
    "Faithfulness is not assumed and literal raw mediality is not concluded. W identically zero is allowed; nontriviality needs a positive-weight witness.",
    "Mathematical Hilbert completion does not supply physical exhaustion, scalar availability, actualization, composites, QM or GR. These are checked conditional mathematical statements; public and manifest statuses remain unchanged."] }

def rawSparseConservationSelection : ResearchTask := {
  id := "raw_sparse_conservation_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply a pointed raw set V with chosenZero and a total pair operation F satisfying F squared equals swap and diagonal transparency F(x,x)=(x,x). Supply real W with W(chosenZero)=0 and W>=0 on all raw states, including every iterate.",
    "Write 0 for chosenZero, m(x,y)=fst(F(x,y)), A(x)=m(x,0), B(x)=m(0,x), u=W composed with A and v=W composed with B. Assume the universal actual sparse law S: W(m(m(x,y),A(z)))+W(m(m(y,x),B(z)))=W(m(x,z))+W(A(y)) for every raw triple x,y,z. Pair-weight conservation is a target conclusion and is not an input field."]
  conclusions := [
    "The checked actual sparse law gives W=u+v from S(0,x,x), pair conservation of u from S(x,y,0), and v(A(z))+v(B(z))=v(z). The K zero identities follow directly before any use of skew symmetry.",
    "For K(x,z)=W(m(x,z))-u(x)-v(z), the checked kernel and residual chain gives the scaled weight-iterate identity. Nonnegativity on all iterates forces the residual r to vanish, so W(A(x))=W(x)/2. Conservation of u then yields pair-weight conservation of W without a conservation input field.",
    "The checked toConservedContract constructs the existing conserved Contract and reuses RawSparseMarginalReconstruction without changing its source. Under the stated positivity and base laws, the actual sparse law is equivalent to pair-weight conservation AND ObservedMedial.",
    "The checked observedData construction supplies the existing reconstruction: feature norm-square equals W, and feature equality is equivalent to the one-hole arbitrary-reference ObservationalEq.",
    "The checked native complex mixer control with quartic readout W(z)=|z|^4 is nonnegative and first-channel medial, hence ObservedMedial, but fails pair conservation. Its actual sparse law at (0,1,1) has left side 1 and right side 1/2. Thus ObservedMedial with nonnegativity alone does not imply the actual sparse law."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawSparseConservationSelection.lean"
      declarations := [
        "IDT.QMClosure.RawSparseConservationSelection.u_add_v",
        "IDT.QMClosure.RawSparseConservationSelection.u_conserved",
        "IDT.QMClosure.RawSparseConservationSelection.v_vacuum_conserved",
        "IDT.QMClosure.RawSparseConservationSelection.K_left_zero",
        "IDT.QMClosure.RawSparseConservationSelection.sparse_implies_kernel",
        "IDT.QMClosure.RawSparseConservationSelection.scaled_weight_iterate",
        "IDT.QMClosure.RawSparseConservationSelection.r_eq_zero",
        "IDT.QMClosure.RawSparseConservationSelection.weight_A",
        "IDT.QMClosure.RawSparseConservationSelection.pair_conserved",
        "IDT.QMClosure.RawSparseConservationSelection.toConservedContract",
        "IDT.QMClosure.RawSparseConservationSelection.sparse_iff_conserved_and_observed_medial",
        "IDT.QMClosure.RawSparseConservationSelection.observedData",
        "IDT.QMClosure.RawSparseConservationSelection.norm_feature_sq",
        "IDT.QMClosure.RawSparseConservationSelection.feature_eq_iff_observationalEq" ] },
    { sourcePath := "Proofs/QMClosure/RawSparseQuarticControl.lean"
      declarations := [
        "IDT.QMClosure.RawSparseQuarticControl.nonnegative",
        "IDT.QMClosure.RawSparseQuarticControl.first_channel_medial",
        "IDT.QMClosure.RawSparseQuarticControl.observed_medial",
        "IDT.QMClosure.RawSparseQuarticControl.vacuum_first_weight",
        "IDT.QMClosure.RawSparseQuarticControl.vacuum_second_weight",
        "IDT.QMClosure.RawSparseQuarticControl.pair_output_at_10",
        "IDT.QMClosure.RawSparseQuarticControl.pair_input_at_10",
        "IDT.QMClosure.RawSparseQuarticControl.not_pair_conserved",
        "IDT.QMClosure.RawSparseQuarticControl.sparse_lhs_at_011",
        "IDT.QMClosure.RawSparseQuarticControl.sparse_rhs_at_011",
        "IDT.QMClosure.RawSparseQuarticControl.not_sparse_law",
        "IDT.QMClosure.RawSparseQuarticControl.observed_medial_nonnegative_does_not_imply_sparse" ] }]
  plannedArtifacts := []
  dependencies := [
    "raw_sparse_marginal_reconstruction",
    "raw_sparse_signed_control"]
  limits := [
    "The universal actual sparse law remains a supplied hypothesis whose physical justification and availability are open. Source-generated preparations do not yet supply all raw triples or arbitrary-reference contexts.",
    "The hypotheses permit W identically zero and do not supply a positive-weight witness. A nontrivial physical realization and physical exhaustion remain open.",
    "Actualization, independence, composites, dynamics and physical scales remain unresolved obligations. These are checked conditional mathematical statements; no QM, GR or primitive-closure claim follows, and public and manifest statuses remain unchanged."] }

def rawSparseInsertionOrigin : ResearchTask := {
  id := "raw_sparse_insertion_origin"
  stage := .openPhysicalBridge
  review := .openObligation
  assumptions := [
    "Investigate physically available sparse preparations ((x,y),(z,0)) with one common fixed-exposure unnormalized selected-row readout W(output1)+W(output2).",
    "The proposed operational requirement is invariance of that selected-row readout when the row layer is inserted before the column analyzer. Its availability and physical justification remain open."]
  conclusions := [
    "This proposed insertion-invariance requirement is operationally the actual sparse law S itself. Giving it a circuit interpretation supplies no independent derivation of S.",
    "The checked raw_sparse_conservation_tests result proves that the six universally quantified families S(0,t,t), S(x,y,0), S(t,t,z), S(A(t),B(t),z), S(B(t),A(t),z) and S(t,0,z) imply pair conservation under the supplied raw base and global nonnegativity.",
    "The additional generic families S(x,y,A(z)) and S(x,y,B(z)) remain an analytic dependency target for reconstruction. This proposed reduction to the two generic families is not a checked theorem or checked equivalence."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawSparseQuarticControl.lean"
      declarations := [
        "IDT.QMClosure.RawSparseQuarticControl.observed_medial_nonnegative_does_not_imply_sparse"] },
    { sourcePath := "Proofs/QMClosure/RawSparseConservationTests.lean"
      declarations := [
        "IDT.QMClosure.RawSparseConservationTests.pair_conserved_of_tests"] }]
  plannedArtifacts := []
  dependencies := [
    "raw_sparse_conservation_selection",
    "raw_network_medial_wall"]
  limits := [
    "The checked quartic countercontrol shows that ObservedMedial with nonnegativity alone does not imply S. Its evidence supports this mathematical limit only and supplies no physical insertion principle.",
    "Causal independence, record aggregation and exposure normalization require separate bridges. Overlapping row and column ports are not disjoint spectators, so disjoint-spectator locality does not supply the insertion law.",
    "Coverage of all sparse raw preparations and generated arbitrary-reference contexts remains open. No available physical interface, nontrivial positive physical realization, actualization, composite, dynamics, physical-scale or primitive-closure conclusion is supplied; public and manifest statuses remain unchanged."] }

def rawSparseConservationTests : ResearchTask := {
  id := "raw_sparse_conservation_tests"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the raw Contract of raw_sparse_conservation_selection with square-swap, diagonal transparency, W(0)=0 and global W>=0. Pair conservation is not an input. Retain its definitions of m, A, B and actual sparse equality S.",
    "Replace universal S by the six universally quantified families S(0,t,t), S(x,y,0), S(t,t,z), S(A(t),B(t),z), S(B(t),A(t),z) and S(t,0,z).",
    "For the separate mathematical countercontrol, use the native complex mixer N with a=(1+i)/2 and b=(1-i)/2, and W=normSq. Put T=W(x)+W(y), d=W(x)-W(y), j=Im(x*conj(y)), h=d*j/T^2 with real zero division at the origin, lambda=(1+i*h)/(1-i*h), and F=lambda*N on both outputs."]
  conclusions := [
    "The checked six universally quantified sparse families imply pair conservation of W and both vacuum half-weight identities under global nonnegativity. Tests has six fields, and every universal sparse law supplies Tests.",
    "Under the stated raw base and global nonnegativity, the checked equivalence is full SparseMarginalLaw iff Tests AND ObservedMedial. No minimality of the six families is claimed.",
    "The checked complex normSq phase-twist control squares to swap, is transparent, has native individual output weights and vacuum action, and satisfies all six tests and pair conservation.",
    "The control is jointly complex-homogeneous and globally continuous, and its row and column layers obey exact interchange on scalar-productArray inputs. Nevertheless its sparse witness at (1,1+i,i) has left side 122/41 and right side 3, so full S and ObservedMedial both fail.",
    "Thus the six families are strictly weaker than full S even with continuity, joint complex homogeneity and the stated restricted product-input interchange. The native complex geometry is supplied for this countercontrol."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawSparseConservationTests.lean"
      declarations := [
        "IDT.QMClosure.RawSparseConservationTests.Tests",
        "IDT.QMClosure.RawSparseConservationTests.of_sparse",
        "IDT.QMClosure.RawSparseConservationTests.kernel_at",
        "IDT.QMClosure.RawSparseConservationTests.scaled_weight_iterate",
        "IDT.QMClosure.RawSparseConservationTests.r_eq_zero",
        "IDT.QMClosure.RawSparseConservationTests.weight_A_of_tests",
        "IDT.QMClosure.RawSparseConservationTests.weight_B_of_tests",
        "IDT.QMClosure.RawSparseConservationTests.pair_conserved_of_tests",
        "IDT.QMClosure.RawSparseConservationTests.sparse_iff_tests_and_observed_medial" ] },
    { sourcePath := "Proofs/QMClosure/RawSparsePhaseTwistControl.lean"
      declarations := [
        "IDT.QMClosure.RawSparsePhaseTwistControl.phase_normSq",
        "IDT.QMClosure.RawSparsePhaseTwistControl.h_native",
        "IDT.QMClosure.RawSparsePhaseTwistControl.h_gate",
        "IDT.QMClosure.RawSparsePhaseTwistControl.gate_square",
        "IDT.QMClosure.RawSparsePhaseTwistControl.gate_transparent",
        "IDT.QMClosure.RawSparsePhaseTwistControl.port_weight_fst",
        "IDT.QMClosure.RawSparsePhaseTwistControl.port_weight_snd",
        "IDT.QMClosure.RawSparsePhaseTwistControl.pair_conserved",
        "IDT.QMClosure.RawSparsePhaseTwistControl.native_vacuum_A",
        "IDT.QMClosure.RawSparsePhaseTwistControl.native_vacuum_B",
        "IDT.QMClosure.RawSparsePhaseTwistControl.gate_joint_complex_homogeneity",
        "IDT.QMClosure.RawSparsePhaseTwistControl.tests",
        "IDT.QMClosure.RawSparsePhaseTwistControl.sparse_witness",
        "IDT.QMClosure.RawSparsePhaseTwistControl.not_sparse_law",
        "IDT.QMClosure.RawSparsePhaseTwistControl.not_observed_medial",
        "IDT.QMClosure.RawSparsePhaseTwistControl.continuous_gate",
        "IDT.QMClosure.RawSparsePhaseTwistControl.interchange_product_inputs",
        "IDT.QMClosure.RawSparsePhaseTwistControl.continuous_homogeneous_countercontrol" ] }]
  plannedArtifacts := []
  dependencies := [
    "raw_sparse_conservation_selection",
    "raw_sparse_insertion_origin"]
  limits := [
    "Global nonnegativity is a hypothesis, not strict positivity. The six-family result establishes conservation, and reconstruction requires the additional ObservedMedial condition in the checked equivalence.",
    "The complex countercontrol is a supplied mathematical model. Its exact restricted product-input interchange supplies no physical independence principle, general raw geometry, generated preparation availability or arbitrary-reference availability.",
    "Full S remains an open physical bridge. Actualization, independence, composites, dynamics and physical scales remain unresolved; no full QM or primitive-closure claim follows, and public and manifest statuses remain unchanged."] }

def rawSparseSelfReferenceSelector : ResearchTask := {
  id := "raw_sparse_self_reference_selector"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply the complex carrier, W=normSq and native mixer N(x,y)=(a*x+b*y,b*x+a*y), with a=(1+i)/2 and b=(1-i)/2. Let F be an arbitrary total operation on complex pairs.",
    "Assume F squared equals swap, the native vacuum action F(x,0)=(a*x,b*x) and F(0,x)=(b*x,a*x), and equality of each individual output weight with the corresponding output weight of N on every input.",
    "Write A(x)=a*x and Delta(x,y,z) for the actual sparse left side minus right side. For p=(x,y), write F(p)=(r,s) and N(p)=(u1,u2)."]
  conclusions := [
    "The checked four-defect identity is Delta(x,y,A(x))+Delta(y,x,A(y))+Delta(r,s,A(r))+Delta(s,r,A(s))=-(normSq(r-u1)+normSq(s-u2))/2. The squared output error is nonnegative and vanishes exactly when F agrees with N at that input.",
    "Four supplied local defect lower bounds -epsilon1, -epsilon2, -epsilon3, -epsilon4 give squared output error <=2*(epsilon1+epsilon2+epsilon3+epsilon4). One uniform bound Delta(x,y,A(x))>=-epsilon over every actual pair gives squared output error <=8*epsilon at every pair.",
    "Universal nonnegative self-defect or universal zero self-defect implies F=N within the supplied native complex port-profile Contract. Full SparseLaw, SelfLaw and F=N are checked equivalent under that Contract.",
    "The nativeContract is a checked inhabitant and satisfies full SparseLaw. These conclusions concern the stated supplied contract, with no minimality claim.",
    "For the phase-twist control at p=(1,1+i), the checked four defects are [-5/41,-10/41,10/41,2/41], their sum is -3/41 and squared output error is 6/41. The control violates both universal self-nondecrease and self-equality and has positive output error."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawSparseSelfReferenceSelector.lean"
      declarations := [
        "IDT.QMClosure.RawSparseSelfReferenceSelector.Contract",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.defect_native_formula",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.four_defect_identity",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.outputError_nonnegative",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.error_zero_iff_operation_eq_at",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.outputError_le_of_four_bounds",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.outputError_le_of_uniform_self_bound",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.operation_eq_native_of_self_nonnegative",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.operation_eq_native_of_self_zero",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.negative_selfDefect_of_positive_error",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.sparseLaw_iff_selfLaw",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.selfLaw_iff_operation_eq_native",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.sparseLaw_iff_operation_eq_native",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.nativeContract",
        "IDT.QMClosure.RawSparseSelfReferenceSelector.native_sparseLaw" ] },
    { sourcePath := "Proofs/QMClosure/RawSparseSelfReferenceControl.lean"
      declarations := [
        "IDT.QMClosure.RawSparseSelfReferenceControl.contract",
        "IDT.QMClosure.RawSparseSelfReferenceControl.selfDefect_witness",
        "IDT.QMClosure.RawSparseSelfReferenceControl.selfDefect_swap_witness",
        "IDT.QMClosure.RawSparseSelfReferenceControl.selfDefect_gate_witness",
        "IDT.QMClosure.RawSparseSelfReferenceControl.selfDefect_swap_gate_witness",
        "IDT.QMClosure.RawSparseSelfReferenceControl.outputError_witness",
        "IDT.QMClosure.RawSparseSelfReferenceControl.four_defect_sum",
        "IDT.QMClosure.RawSparseSelfReferenceControl.four_defect_identity_at_witness",
        "IDT.QMClosure.RawSparseSelfReferenceControl.violates_self_nondecrease",
        "IDT.QMClosure.RawSparseSelfReferenceControl.violates_self_equality",
        "IDT.QMClosure.RawSparseSelfReferenceControl.positive_output_error" ] }]
  plannedArtifacts := []
  dependencies := [
    "raw_sparse_conservation_tests"]
  limits := [
    "Positive-definite native complex geometry and individual native output weights are supplied hypotheses. The checked selection is bounded by this exact Contract.",
    "The raw_pair_plane_amalgam_wall now supplies a checked constructed raw countermodel satisfying the six tests and self-reference while failing full SparseMarginalLaw. This selector cannot transfer to arbitrary raw carriers without a separate global compatibility or geometry bridge.",
    "Simultaneous physical availability of x, y and A(x) is an open resource bridge. The bounded mathematical selection supplies no physical insertion origin, generated preparation availability, actualization, full QM or primitive-closure claim; public and manifest statuses remain unchanged."] }

def rawPairPlaneAmalgamWall : ResearchTask := {
  id := "raw_pair_plane_amalgam_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supplied complex weighted ray-plane mathematics defines a noncomputable algebraic omission countermodel. The construction uses classical choice, complex scalar action and positive quadratic chart weights as mathematical inputs, without a physical geometry origin or Born interpretation.",
    "Start from Fin 3 unit-weight rays and Empty planes. Each successor attaches one plane to each unordered uncovered pair, identifies its axes with the two old ray fibers and gives every nonzero-slope interior ray a fresh tag. Old weights and coordinates are preserved."]
  conclusions := [
    "The checked omega-stage DirectLimit construction gives an actual complete atlas and injective inclusions of every finite stage. Distinct planes share at most one ray, and every distinct ray pair is covered. This establishes atlas existence in addition to the conditional complete-atlas interface.",
    "The raw carrier has one common zero, weighted complex ray fibers and raywise complex scalar action. Local mixing with a=(1+i)/2 and b=(1-i)/2 glues to a well-defined global m. Its pair operation F(s,t)=(m(s,t),m(t,s)) squares to swap and is diagonally transparent. W(0)=0, W is nonnegative and faithful, and pair weight is conserved.",
    "All six sparse test families hold universally, as does self-reference SparseAt x y A(x). Both m and its ordered pair operation respect joint complex homogeneity. The exact chart law and sparse identity within one chart are kernel checked.",
    "The stage-two witness theorem remains conditional on an atlas inclusion, while constructed_sparse_witness instantiates it with the actual completed atlas and completionInclusion 2. Its three preparations give sparse left side 2 and right side 3. The proof handles either endpoint orientation of every chosen unordered seed pair.",
    "The constructed_countermodel theorem conjoins the six universal tests, self-reference, nonnegative faithful weight, pair conservation and joint complex homogeneity with failure of full SparseMarginalLaw. These exact raw laws therefore do not imply the full sparse marginal law.",
    "The constructed_not_observed_medial corollary shows that this same model fails global ObservedMedial. This identifies a missing global bridge for this model without establishing any continuity sufficiency theorem.",
    "All five planned algebraic modules are realized. The result is a noncomputable algebraic countermodel. It supplies neither a finite executable search experiment nor a physical reconstruction."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawPairPlaneAtlas.lean"
      declarations := [
        "IDT.QMClosure.RawPairPlaneAtlas.PartialAtlas",
        "IDT.QMClosure.RawPairPlaneAtlas.CompleteAtlas",
        "IDT.QMClosure.RawPairPlaneAtlas.Extension",
        "IDT.QMClosure.RawPairPlaneAtlas.W_nonnegative",
        "IDT.QMClosure.RawPairPlaneAtlas.W_eq_zero_iff",
        "IDT.QMClosure.RawPairPlaneAtlas.chart_injective",
        "IDT.QMClosure.RawPairPlaneAtlas.W_chart",
        "IDT.QMClosure.RawPairPlaneAtlas.Extension.rawMap_injective",
        "IDT.QMClosure.RawPairPlaneAtlas.Extension.W_rawMap",
        "IDT.QMClosure.RawPairPlaneAtlas.Extension.chart_map" ] },
    { sourcePath := "Proofs/QMClosure/RawPairPlaneExtension.lean"
      declarations := [
        "IDT.QMClosure.RawPairPlaneAtlas.nextAtlas",
        "IDT.QMClosure.RawPairPlaneAtlas.stepExtension",
        "IDT.QMClosure.RawPairPlaneAtlas.new_plane_axis_pair",
        "IDT.QMClosure.RawPairPlaneAtlas.pair_covered_next",
        "IDT.QMClosure.RawPairPlaneAtlas.fresh_on_plane_iff",
        "IDT.QMClosure.RawPairPlaneAtlas.different_fresh_edges_uncovered" ] },
    { sourcePath := "Proofs/QMClosure/RawPairPlaneLocalOperations.lean"
      declarations := [
        "IDT.QMClosure.RawPairPlaneLocalOperations.chart_mix_gluing",
        "IDT.QMClosure.RawPairPlaneLocalOperations.pair_in_chart",
        "IDT.QMClosure.RawPairPlaneLocalOperations.m_chart",
        "IDT.QMClosure.RawPairPlaneLocalOperations.contract",
        "IDT.QMClosure.RawPairPlaneLocalOperations.operation_square",
        "IDT.QMClosure.RawPairPlaneLocalOperations.operation_transparent",
        "IDT.QMClosure.RawPairPlaneLocalOperations.sparse_in_chart",
        "IDT.QMClosure.RawPairPlaneLocalOperations.tests",
        "IDT.QMClosure.RawPairPlaneLocalOperations.self_sparse",
        "IDT.QMClosure.RawPairPlaneLocalOperations.weight_nonnegative",
        "IDT.QMClosure.RawPairPlaneLocalOperations.weight_faithful",
        "IDT.QMClosure.RawPairPlaneLocalOperations.pair_conserved",
        "IDT.QMClosure.RawPairPlaneLocalOperations.m_scale",
        "IDT.QMClosure.RawPairPlaneLocalOperations.operation_scale" ] },
    { sourcePath := "Proofs/QMClosure/RawPairPlaneCompletion.lean"
      declarations := [
        "IDT.QMClosure.RawPairPlaneAtlas.AtlasTower",
        "IDT.QMClosure.RawPairPlaneAtlas.AtlasTower.transition",
        "IDT.QMClosure.RawPairPlaneAtlas.AtlasTower.rayMap",
        "IDT.QMClosure.RawPairPlaneAtlas.AtlasTower.planeMap",
        "IDT.QMClosure.RawPairPlaneAtlas.AtlasTower.limitPartialAtlas",
        "IDT.QMClosure.RawPairPlaneAtlas.AtlasTower.inclusion",
        "IDT.QMClosure.RawPairPlaneAtlas.AtlasTower.limit_pair_covered",
        "IDT.QMClosure.RawPairPlaneAtlas.AtlasTower.completeAtlas",
        "IDT.QMClosure.RawPairPlaneAtlas.threeRaySeed",
        "IDT.QMClosure.RawPairPlaneAtlas.completionStage",
        "IDT.QMClosure.RawPairPlaneAtlas.threeRayTower",
        "IDT.QMClosure.RawPairPlaneAtlas.constructedCompleteAtlas",
        "IDT.QMClosure.RawPairPlaneAtlas.completionInclusion" ] },
    { sourcePath := "Proofs/QMClosure/RawPairPlaneSparseWall.lean"
      declarations := [
        "IDT.QMClosure.RawPairPlaneSparseWall.stage_two_sparse_witness",
        "IDT.QMClosure.RawPairPlaneSparseWall.constructed_sparse_witness",
        "IDT.QMClosure.RawPairPlaneSparseWall.constructed_not_sparse",
        "IDT.QMClosure.RawPairPlaneSparseWall.constructed_not_observed_medial",
        "IDT.QMClosure.RawPairPlaneSparseWall.constructed_countermodel" ] }]
  plannedArtifacts := []
  dependencies := [
    "raw_sparse_conservation_tests",
    "raw_sparse_self_reference_selector"]
  limits := [
    "For this older atlas construction, the general transfer theorem for universal closure of quantifier-free raw-term formulas with at most two preparation variables, zero, m, W and raywise complex scalar action remains without a formal proof. Scalar parameters are allowed in the proposed scope. Arbitrary named preparation constants, nested preparation quantifiers, arbitrary-reference ObservationalEq and topology are excluded. The checked common-chart APIs support future transfer work. This broader formula claim is outside checkedEvidence.",
    "The analytic continuity obstruction remains UNCHECKED: for t_epsilon=x+epsilon*e in P and q=i*x+y in Q, the proposed calculation is W(m(t_epsilon,q))=3/2+epsilon^2/2 for nonzero real epsilon and W(m(x,q))=5/2. No kernel-checked topological conclusion is recorded.",
    "This checked pair-plane result leaves continuity open for that model. The separate checked raw_continuous_plane_phase_wall supplies a globally continuous countermodel, and raw_continuous_plane_local_theory transfers the exact two-preparation quantifier-free native-valid language to that same countermodel. Stronger global compatibility principles remain open and need not literally use three preparation variables.",
    "Only raywise complex scalar action is supplied. Global associative addition and a global vector-space structure are outside this construction.",
    "The original physics primitive goal remains open. This supplied complex-geometric countermodel gives no physical geometry origin, preparation availability, actualization, full QM or primitive closure. Public and manifest statuses remain unchanged."] }

def rawContinuousPlanePhaseWall : ResearchTask := {
  id := "raw_continuous_plane_phase_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supplied V=Fin 3 -> C with its ordinary product topology and W(v)=sum_j normSq(v_j). This complex quadratic geometry is an omission-control input, without a physical geometry origin or Born interpretation.",
    "Use kappa(r)=(1+i*r)/(1-i*r), R(v)=normSq(v_0)/W(v) with division by zero equal to zero, and H_t(v)=kappa(t*R(v))*v. The family uses ordinary complex scalar action and the native mixer N with a=(1+i)/2 and b=(1-i)/2.",
    "For the three coordinates w of x wedge y, set f(x,y)=(normSq(w_0)+normSq(w_1))/sum_j normSq(w_j), with 0/0=0. Define G_t by conjugating N on both ports with H_t, and the actual pair operation by F(x,y)=G_(f(x,y))(x,y)."]
  conclusions := [
    "H_t preserves W, is complex-homogeneous and injective and surjective, and is jointly continuous in t and its vector argument. Each fixed-parameter family operation squares to swap, is transparent and conserves pair weight.",
    "The plane parameter lies in [0,1] and is invariant under invertible changes of the two-generator basis. On dependent pairs every G_t agrees with N. For subpairs in any supplied two-generated plane, the actual mixer agrees with the one fixed family mixer selected by that plane's generating pair.",
    "The actual raw operation satisfies square-swap, transparency, nonnegative faithful weight, pair conservation, all six universal sparse test families, self-reference SparseAt x y A(x), and joint complex homogeneity. Its sparse identity holds for triples lying in a common supplied two-generated plane.",
    "The actual pair operation and its first output are globally continuous in the ordinary product topology. Away from wedge zero, the parameter is continuous. At a dependent pair, joint continuity and compactness of [0,1] control arbitrary parameter selection because the entire family has the same value there.",
    "For x=(1,0,0), y=(0,1,0), z=(1,0,1), the checked sparse left side is 2 and right side is 13/5. The mixed x,z output has weight 21/10. These exact values prove failure of full SparseMarginalLaw and ObservedMedial.",
    "The constructed_continuous_countermodel theorem conjoins the universal tests, self-reference, nonnegative faithful weight, pair conservation, joint complex homogeneity and global continuity with failure of both full laws for the same explicit operation. Continuity added to these checked raw laws is therefore insufficient to force the full sparse marginal law."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseFamily.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseFamily.W_nonnegative",
        "IDT.QMClosure.RawPlanePhaseFamily.W_eq_zero_iff",
        "IDT.QMClosure.RawPlanePhaseFamily.W_smul",
        "IDT.QMClosure.RawPlanePhaseFamily.W_H",
        "IDT.QMClosure.RawPlanePhaseFamily.H_smul",
        "IDT.QMClosure.RawPlanePhaseFamily.H_injective",
        "IDT.QMClosure.RawPlanePhaseFamily.H_surjective",
        "IDT.QMClosure.RawPlanePhaseFamily.continuous_H",
        "IDT.QMClosure.RawPlanePhaseFamily.familyOperation_square",
        "IDT.QMClosure.RawPlanePhaseFamily.familyOperation_transparent",
        "IDT.QMClosure.RawPlanePhaseFamily.familySparse",
        "IDT.QMClosure.RawPlanePhaseFamily.family_conserved",
        "IDT.QMClosure.RawPlanePhaseFamily.jointcontinuous_family" ] },
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseGeometry.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseGeometry.parameter_change_basis",
        "IDT.QMClosure.RawPlanePhaseGeometry.parameter_nonnegative",
        "IDT.QMClosure.RawPlanePhaseGeometry.parameter_le_one",
        "IDT.QMClosure.RawPlanePhaseGeometry.continuous_parameter_at",
        "IDT.QMClosure.RawPlanePhaseGeometry.familyM_of_dependent",
        "IDT.QMClosure.RawPlanePhaseGeometry.familyM_parameter_locality" ] },
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseControl.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseControl.m_eq_family_of_inPlane",
        "IDT.QMClosure.RawPlanePhaseControl.operation_square",
        "IDT.QMClosure.RawPlanePhaseControl.operation_transparent",
        "IDT.QMClosure.RawPlanePhaseControl.contract",
        "IDT.QMClosure.RawPlanePhaseControl.A_eq",
        "IDT.QMClosure.RawPlanePhaseControl.B_eq",
        "IDT.QMClosure.RawPlanePhaseControl.sparse_inPlane",
        "IDT.QMClosure.RawPlanePhaseControl.tests",
        "IDT.QMClosure.RawPlanePhaseControl.selfSparse",
        "IDT.QMClosure.RawPlanePhaseControl.weight_nonnegative",
        "IDT.QMClosure.RawPlanePhaseControl.weight_eq_zero_iff",
        "IDT.QMClosure.RawPlanePhaseControl.pair_conserved",
        "IDT.QMClosure.RawPlanePhaseControl.m_smul",
        "IDT.QMClosure.RawPlanePhaseControl.operation_smul" ] },
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseContinuity.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseContinuity.continuousAt_compact_selection",
        "IDT.QMClosure.RawPlanePhaseContinuity.continuous_operation",
        "IDT.QMClosure.RawPlanePhaseContinuity.continuous_m" ] },
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseSparseWall.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseSparseWall.witness_m_xz_weight",
        "IDT.QMClosure.RawPlanePhaseSparseWall.witness_A_y_weight",
        "IDT.QMClosure.RawPlanePhaseSparseWall.witness_outer_forward",
        "IDT.QMClosure.RawPlanePhaseSparseWall.witness_outer_reverse",
        "IDT.QMClosure.RawPlanePhaseSparseWall.constructed_sparse_witness",
        "IDT.QMClosure.RawPlanePhaseSparseWall.constructed_not_sparse",
        "IDT.QMClosure.RawPlanePhaseSparseWall.constructed_not_observed_medial",
        "IDT.QMClosure.RawPlanePhaseSparseWall.constructed_continuous_countermodel" ] }]
  plannedArtifacts := []
  dependencies := [
    "raw_pair_plane_amalgam_wall",
    "raw_sparse_conservation_tests",
    "raw_sparse_self_reference_selector"]
  limits := [
    "The checked theorem concerns the explicit noncomputable complex-geometric operation and its exact listed laws. The stronger two-preparation formula transfer is recorded separately in raw_continuous_plane_local_theory.",
    "No transfer of the existing native output-profile Contract to this operation is asserted. No triangle-inequality or global Lipschitz claim is included in the current checked scope.",
    "The proposed common Frechet derivative obstruction at the vacuum remains analytic. The smooth regularity and midpoint-convexity bridge routes retain their separate analyticAwaitingFormalization status.",
    "No physical primitive origin, preparation availability, actualization, full QM or primitive-closure conclusion is recorded. Public and manifest statuses remain unchanged."] }

def rawContinuousPlaneLocalTheory : ResearchTask := {
  id := "raw_continuous_plane_local_theory"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the supplied continuous plane-phase omission-control geometry and a Term2 language with Fin 2 preparation variables, zero, mixing and complex scalar coefficients. Interpret mixing natively in one semantics and by the actual operation in the other. Arbitrary preparation constants are excluded.",
    "QuantifierfreeFormula2 consists of term equality, readoutPredicate(P)(terms) for a finite list of terms and a fixed P : List R -> Prop, conjunction and negation. Other Boolean connectives can be expressed from these. Each predicate is identical in both semantics, has no preparation-environment argument and has no model-dependent reinterpretation. No continuity or decidability of P is required.",
    "External universally quantified complex scalar parameters are allowed through families of terms or formulas. Native validity means validity for every pair of preparations in the supplied native C3 model."]
  conclusions := [
    "For actual inputs x,y and k=f(x,y), every generated term stays in their plane and satisfies actualEval(t,x,y)=H_k(nativeEval(t,H_(-k)(x),H_(-k)(y))).",
    "Injectivity of H_k and preservation of W yield equivalence of formula truth in the two related environments, including negation and arbitrary fixed predicates of finite readout lists.",
    "For every formula, native validity implies actual validity. The comparison uses the supplied native C3 model directly.",
    "Every collection of native-valid formulas in this exact language is satisfied by the same actual globally continuous operation with nonnegative faithful weight, the six sparse tests, self-reference, pair conservation and joint complex homogeneity, while full SparseMarginalLaw and ObservedMedial fail.",
    "The native_valid_collection_does_not_force_sparse theorem records that validity of any such collection in this supplied actual model cannot imply its full sparse marginal law. External scalar-parameter families are covered by ranging over their formula instances."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseLocalTheory.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseLocalTheory.Term2",
        "IDT.QMClosure.RawPlanePhaseLocalTheory.QuantifierfreeFormula2",
        "IDT.QMClosure.RawPlanePhaseLocalTheory.evalActual_inPlane",
        "IDT.QMClosure.RawPlanePhaseLocalTheory.evalActual_transport",
        "IDT.QMClosure.RawPlanePhaseLocalTheory.readoutsActual_transport",
        "IDT.QMClosure.RawPlanePhaseLocalTheory.holdsActual_iff_transported",
        "IDT.QMClosure.RawPlanePhaseLocalTheory.nativeValid_implies_actualValid",
        "IDT.QMClosure.RawPlanePhaseLocalTheory.ActualCountermodelProperties",
        "IDT.QMClosure.RawPlanePhaseLocalTheory.actualCountermodelProperties",
        "IDT.QMClosure.RawPlanePhaseLocalTheory.native_valid_collection_countermodel",
        "IDT.QMClosure.RawPlanePhaseLocalTheory.native_valid_collection_does_not_force_sparse" ] }]
  plannedArtifacts := []
  dependencies := ["raw_continuous_plane_phase_wall"]
  limits := [
    "The collection theorem concerns the exact implemented syntax, supplied semantics and explicit actual countermodel. It is a kernel theorem about this mathematical omission control.",
    "The language excludes arbitrary raw preparation constants, nested preparation quantifiers, arbitrary-reference ObservationalEq and topology predicates. Predicates receive only finite real readout lists.",
    "The supplied complex geometry and readout control give no physical primitive origin, Born interpretation, actualization, full QM or primitive closure. Public and manifest statuses remain unchanged."] }

def rawVacuumRegularityBridge : ResearchTask := {
  id := "raw_vacuum_regularity_bridge"
  stage := .analyticAwaitingFormalization
  review := .parentAccepted
  assumptions := [
    "A supplied pointed finite-dimensional real manifold without boundary, with smooth real multiplicative scaling h satisfying h_1=id, h_0=vacuum and h_s composed with h_t=h_(s*t).",
    "Define the actual orbit velocity i(x)=d/dt at t=0 of h_t(x), valued in the vacuum tangent space. Assume only local invertibility of D i at the vacuum, the weight-one tangent selector, together with differentiability of the mixer at the vacuum pair and compatibility with h-scaling."]
  conclusions := [
    "Accepted conditional target: the inverse function theorem and scaling extend local invertibility to a global diffeomorphism i with i(h_t(x))=t*i(x). Global injectivity of an arbitrary feature map is not a premise.",
    "In these reconstructed coordinates, mixer differentiability at the vacuum pair and homogeneity force linearity. Transparency gives A+B=I, hence commuting A and B and mediality. Square-swap then gives a complex structure J with J squared equal to -I.",
    "The existing six sparse tests and nonnegativity yield pair conservation. The resulting ObservedMedial property then supplies the existing conservation-to-sparse route.",
    "For a map f on the supplied real coordinate space with f(t*p)=t*f(p) for every real t, every ray derivative with real parameter t at the vacuum exists automatically and equals the map evaluated at that ray direction. A specified common continuous real-linear map represents all directional derivatives exactly when f agrees globally with that map. For the current three-dimensional complex control, the separate real vacuum derivatives of mixing are the linear attenuation maps A and B, and all joint real ray derivatives exist. A joint real Frechet derivative at the vacuum pair is excluded analytically by homogeneity together with the checked sparse failure. These derivative assertions await Lean artifacts.",
    "For the actual orbit velocity i and a centered chart e at the vacuum, let C=De_vac be the tangent-coordinate identification and define f=C composed with i composed with e inverse on the centered chart neighborhood. Put P=Df(0). The scaling identities give P composed with f=f and P squared=P. Local isolation of f's zero at the vacuum and the ordinary inverse function theorem for g(u)=f(u)+(I-P)u imply P=I. This targets the actual velocity map and requires only local zero isolation. The full manifold reconstruction target remains in force.",
    "A separate analytic sufficient route to velocity-zero isolation assumes a C2 scaling orbit at t=0, W Frechet differentiable at the vacuum with its minimum zero there, faithful zero weight, and the exact imported scaling W(h_t(x))=t^2*W(x). If i(x)=0, the orbit displacement is O(t^2). The vacuum derivative of W vanishes at its minimum, so W(h_t(x))=o(t^2), which forces W(x)=0 and then x=vacuum."]
  checkedEvidence := []
  plannedArtifacts := [
    "Proofs/QMClosure/RawRegularScalingReconstruction.lean",
    "Proofs/QMClosure/RawHomogeneousVacuumDerivative.lean"]
  dependencies := [
    "raw_continuous_plane_phase_wall",
    "raw_sparse_conservation_tests",
    "raw_sparse_marginal_reconstruction"]
  limits := [
    "The manifold, smooth scaling, weight-one tangent selector and common Frechet derivative are supplied regularity premises with open physical origins. All new statements await Lean artifacts.",
    "Smooth scaling alone is insufficient for the velocity construction: h_t(x)=t^2*x loses the orbit velocity. A smooth weights-(1,3) nonmedial polynomial control has nonfaithful W and does not satisfy all main countermodel properties.",
    "The accepted continuous three-dimensional complex omission control separates continuity from the common mixer derivative premise. No continuity or real quadratic representation of W follows here without its own regularity argument.",
    "This is a conditional bridge plan without an actualization, full QM or primitive-closure conclusion. Public and manifest statuses remain unchanged.",
    "All new derivative, local-isolation and regularity arguments in these refinements remain ANALYTIC/UNCHECKED. The four-module Gram cluster formalizes neither the full manifold inverse-function route nor these derivative refinements. Retain the separate raw_midpoint_convexity_bridge at analyticAwaitingFormalization.",
    "The exact degree-two weight scaling used in the velocity-zero isolation argument is a supplied mathematical assumption with open physical origin. Smooth scaling alone remains insufficient. A real first-derivative regularity condition on W does not force a quadratic weight. The C1 homogeneous faithful readout-only example W(x,y)=sqrt(x^4+y^4) is nonquadratic. This comparison supplies no complete raw mixer control. Under the corresponding C2 regularity and exact scaling, the intrinsic vacuum Hessian at the critical vacuum gives W(x)=1/2 D^2 W_vac(i(x),i(x)) along actual orbit velocities. This identity makes no claim of global chart linearity. These comparison assertions await their own Lean artifacts."] }

def rawMidpointConvexityBridge : ResearchTask := {
  id := "raw_midpoint_convexity_bridge"
  stage := .analyticAwaitingFormalization
  review := .parentAccepted
  assumptions := [
    "Restrict to a supplied two-generated native-plane class with complex scalar action. The six sparse tests and self-reference alone do not establish membership in this class.",
    "Set d(x,y)^2=2*W(m(x,-i*y)), G(x,y)=(W(x)+W(y)-d(x,y)^2)/2 and h(x,y)=b*m(x,i*y), with b=(1-i)/2. In the supplied native chart of each plane, h is the Euclidean midpoint. Assume faithful distance separation and global one-point midpoint-distance convexity d(z,h(x,y)) <= (d(z,x)+d(z,y))/2."]
  conclusions := [
    "The separate checked raw_midpoint_gram_compatibility task proves the exact equivalence of squared or ordinary midpoint convexity with full kernel-row averaging under its real homogeneity and squared-distance contract. It gives all finite Gram positivity and, with LocalKernel, the actual sparse law without an asymptotic limit.",
    "The stronger native-plane target of raw associative global addition and an inner-product representation under faithful separation remains ANALYTIC/UNCHECKED. Its original RawMidpointConvexityBridge artifact is still planned.",
    "The product-nonexpansivity comparison remains ANALYTIC/UNCHECKED. Product nonexpansivity of F collapses to isometry through F^4=id and restates the full sparse law at reference pair (i*z,0). It supplies no independent physical primitive origin.",
    "The separately checked raw_plane_phase_gram_control continuous-control Gram witness has coefficient vector (-10,-10,20,-1) and quadratic value -2. Its actual three-point Gram and triangle failures are recorded in that separate task.",
    "The separate checked raw_plane_phase_midpoint_control task proves the actual midpoint failure at reference -3*z, including the strict inequality sqrt(43/2)>(sqrt(119/5)+sqrt(19))/2. Its exact threshold t>=-5/2 concerns only the chosen endpoint pair and reference orbit.",
    "The separate checked raw_dyadic_midpoint_compatibility task replaces all-real preparation scaling with independent half and antiphase maps and midpoint-half kernel compatibility. Its global squared midpoint inequality yields all finite Gram positivity and, with LocalKernel, the sparse law. The checked raw_tripod_midpoint_control records why coherent antiphase cannot simply be omitted.",
    "The independently reviewed real two-plane geometry comparison is tracked by raw_real_plane_metric_control at analyticAwaitingFormalization. It supplies no complete complex native-mixer countermodel."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/RawMidpointConvexityBridge.lean"]
  dependencies := [
    "raw_continuous_plane_phase_wall",
    "raw_sparse_conservation_tests",
    "raw_sparse_self_reference_selector",
    "raw_metric_gram_arity",
    "raw_four_point_gram_bridge",
    "raw_plane_phase_gram_control",
    "raw_midpoint_gram_compatibility",
    "raw_plane_phase_midpoint_control",
    "raw_real_plane_metric_control",
    "raw_dyadic_midpoint_compatibility",
    "raw_tripod_midpoint_control"]
  limits := [
    "Raw associative-addition and inner-product reconstruction and the product-nonexpansivity comparison remain ANALYTIC/UNCHECKED. The generic midpoint-row equivalence and sparse bridge and the actual midpoint failure have separate checked records. The supplied native-plane scope of the stronger reconstruction target must be preserved.",
    "The checked raw_metric_gram_arity task proves triangle equivalence with global real three-point Gram positivity under its exact homogeneity and squared-distance contract. Whether complete Hermitian complex two-plane coverage, coherent complex scalar action, an actual native mixer and global three-point positivity force SparseMarginalLaw remains unresolved.",
    "The physical origins of global midpoint convexity, faithful separation and four-point Gram positivity remain open. All-real reference availability is a supplied premise of the all-real route. The dyadic route instead supplies half-row homogeneity, coherent antiphase and midpoint-half compatibility, whose physical origins also remain open. This stronger reconstruction route retains analyticAwaitingFormalization status.",
    "No physical geometry origin, actualization, full QM or primitive-closure conclusion is recorded. Public and manifest statuses remain unchanged."] }

def rawMetricGramArity : ResearchTask := {
  id := "raw_metric_gram_arity"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For the generic finite Gram quadratic and null-cross transfer, supply a carrier and a symmetric real kernel G. GramNonnegative n quantifies all n-point lists, allowing repetitions, and all real coefficient lists.",
    "For triangle equivalence only, supply a real-parameter preparation map scale with G(scale(r,x),y)=r*G(x,y), and a nonnegative distance d satisfying d(x,y)^2=G(x,x)+G(y,y)-2*G(x,y)."]
  conclusions := [
    "The finite Gram quadratic is defined for every finite point list and real coefficient list. Four-point positivity transfers a three-point null relation with coefficient vector (1,1,-1) to any fourth preparation, forcing its mixed kernel response to vanish.",
    "For a fixed three-point null relation with coefficient vector (1,1,-1) and a fourth point with nonnegative diagonal kernel value, positivity on the two-parameter coefficient plane (s,s,-s,t) is equivalent to vanishing of that external mixed response. This restricted positivity restates the corresponding response identity.",
    "Global triangle inequality for d is equivalent to global real three-point Gram positivity under exactly the supplied kernel homogeneity, symmetry and nonnegative squared-distance contract.",
    "The triangle equivalence supplies no implication from three-point positivity to four-point positivity or to the sparse law in the complete native-plane class."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawGramGeometry.lean"
      declarations := [
        "IDT.QMClosure.RawGramGeometry.quadratic",
        "IDT.QMClosure.RawGramGeometry.GramNonnegative",
        "IDT.QMClosure.RawGramGeometry.Triangle",
        "IDT.QMClosure.RawGramGeometry.quadratic_three",
        "IDT.QMClosure.RawGramGeometry.quadratic_four",
        "IDT.QMClosure.RawGramGeometry.diagonal_nonnegative",
        "IDT.QMClosure.RawGramGeometry.null_plane_quadratic",
        "IDT.QMClosure.RawGramGeometry.four_point_null_transfer",
        "IDT.QMClosure.RawGramGeometry.null_plane_nonnegative_iff",
        "IDT.QMClosure.RawGramGeometry.triangle_iff_three_point" ] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "The checked scope consists of the finite quadratic identities, null-transfer statements and the triangle equivalence in RawGramGeometry. The preparation map needs only the stated real kernel homogeneity.",
    "Faithful separation, topology, a Hilbert representation and an additive carrier structure are outside the premises of the triangle equivalence.",
    "The proposed generic signed four-ray control satisfying three-point but failing four-point positivity remains ANALYTIC/UNCHECKED. No artifact for that control is included here. Its lack of complete native pair-plane coverage also leaves it outside the required complete native-plane class.",
    "The physical origin of global Gram positivity and the remaining complete-native-plane triangle-to-sparse implication are open."] }

def rawFourPointGramBridge : ResearchTask := {
  id := "raw_four_point_gram_bridge"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply the existing raw Selection.Contract and a LocalKernel with G symmetric, G(x,x)=W(x), G(A(x),z)=G(x,B(z)), and the three-point Gram quadratic at (A(x),B(y),m(x,y)) with coefficients (1,1,-1) equal to zero. Each local identity uses at most two independent preparations.",
    "Supply real four-point Gram positivity for every quadruple, including repeated points."]
  conclusions := [
    "Four-point positivity and the local mixer null relation give G(m(x,y),z)=G(x,B(z))+G(y,A(z)) for every three preparations.",
    "GramEq is equality of complete G rows. It preserves weight and is a congruence for both mixer arguments. Transparency and the two adjoint identities derive GramEq(A(B(x)),B(A(x))).",
    "This commutation modulo GramEq yields mediality modulo GramEq. Transfer to the existing ObservationalEq gives ObservedMedial, including arbitrary finite one-hole observations with fixed references.",
    "Repeated-point four-point positivity and the diagonal law yield W nonnegative. Square-swap and the adjoint kernel expansion derive pair conservation directly.",
    "Pair conservation and ObservedMedial yield SparseMarginalLaw through the existing reconstruction adapter. The resulting sparse law gives all six universal sparse test families."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawFourPointGramBridge.lean"
      declarations := [
        "IDT.QMClosure.RawFourPointGramBridge.LocalKernel",
        "IDT.QMClosure.RawFourPointGramBridge.GramEq",
        "IDT.QMClosure.RawFourPointGramBridge.weight_nonnegative",
        "IDT.QMClosure.RawFourPointGramBridge.B_adjoint",
        "IDT.QMClosure.RawFourPointGramBridge.G_m",
        "IDT.QMClosure.RawFourPointGramBridge.gramEq_weight",
        "IDT.QMClosure.RawFourPointGramBridge.gramEq_m_left",
        "IDT.QMClosure.RawFourPointGramBridge.gramEq_m_right",
        "IDT.QMClosure.RawFourPointGramBridge.gramEq_observationalEq",
        "IDT.QMClosure.RawFourPointGramBridge.gram_split",
        "IDT.QMClosure.RawFourPointGramBridge.gram_attenuation_commute",
        "IDT.QMClosure.RawFourPointGramBridge.G_attenuation_commute_right",
        "IDT.QMClosure.RawFourPointGramBridge.gram_medial",
        "IDT.QMClosure.RawFourPointGramBridge.observed_medial",
        "IDT.QMClosure.RawFourPointGramBridge.pair_conserved",
        "IDT.QMClosure.RawFourPointGramBridge.sparse_of_fourPointPositive",
        "IDT.QMClosure.RawFourPointGramBridge.conclusions_of_fourPointPositive" ] }]
  plannedArtifacts := []
  dependencies := [
    "raw_metric_gram_arity",
    "raw_sparse_conservation_tests",
    "raw_sparse_marginal_reconstruction"]
  limits := [
    "The LocalKernel premises are symmetry, the weight diagonal, one adjoint identity and the mixer null relation. Literal raw A/B commutation, the six test families and pair conservation are outside the input contract. The core bridge also supplies no global addition, faithful separation, preparation scalar action or Hilbert representation.",
    "Four-point positivity is an explicit additional premise with open physical origin. Restricted positivity around a local null relation is equivalent to the corresponding external kernel additivity and therefore does not independently derive that additivity.",
    "An expectation of a squared linear combination requires a joint Gram representation or an actual operational weight identity. Both remain open primitive-origin obligations.",
    "The bridge is conditional and supplies no physical geometry origin, actualization, full QM or primitive closure. Public and manifest statuses remain unchanged."] }

def rawPlanePhaseGramControl : ResearchTask := {
  id := "raw_plane_phase_gram_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the actual continuous three-dimensional complex plane-phase operation from raw_continuous_plane_phase_wall and its fixed-plane family. Define its actual G(x,y)=(W(x)+W(y)-2*W(m(x,-i*y)))/2 and d(x,y)=sqrt(W(x)+W(y)-2*G(x,y)).",
    "The kernel and distance are defined from that actual operation. Supplied ordinary complex geometry remains the omission-control input."]
  conclusions := [
    "Fixed-plane family transport proves the LocalKernel contract, separate real homogeneity and the nonnegative squared-distance contract for this actual G and d. Thus the generic triangle equivalence applies to the operation-defined response.",
    "For x=e1, y=e2, u=(e1+e2)/2, z=e1+e3, the checked four-point G matrix is [[1,0,1/2,4/5],[0,1,1/2,0],[1/2,1/2,1/2,1/2],[4/5,0,1/2,2]]. Coefficients (-10,-10,20,-1) give quadratic value -2, excluding global four-point positivity.",
    "For x=(0,1,1), y=(1,2,1), z=(2,2,1), the checked three-point G matrix is [[2,120/41,18483/6961],[120/41,6,12793837/1838941],[18483/6961,12793837/1838941,9]]. Coefficients (5,-7,4) give quadratic value -142257420744/524835600341, excluding global three-point positivity.",
    "For P=5*x, Q=-7*y and R=-2*z, the checked squared distances are d(P,R)^2=968306/6961, d(Q,R)^2=248623094/1838941 and d(P,Q)^2=22504/41. Their combination 2*d(P,R)^2+2*d(Q,R)^2-d(P,Q)^2=-142257420744/524835600341 is strictly negative and, using symmetry of d, gives d(P,Q)>d(P,R)+d(R,Q)."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseGramKernel.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseGramKernel.G",
        "IDT.QMClosure.RawPlanePhaseGramKernel.d",
        "IDT.QMClosure.RawPlanePhaseGramKernel.G_inPlane",
        "IDT.QMClosure.RawPlanePhaseGramKernel.G_eq_nativeG_transport",
        "IDT.QMClosure.RawPlanePhaseGramKernel.G_symmetric",
        "IDT.QMClosure.RawPlanePhaseGramKernel.G_diagonal",
        "IDT.QMClosure.RawPlanePhaseGramKernel.G_real_smul_left",
        "IDT.QMClosure.RawPlanePhaseGramKernel.G_real_smul_right",
        "IDT.QMClosure.RawPlanePhaseGramKernel.radicand_nonnegative",
        "IDT.QMClosure.RawPlanePhaseGramKernel.d_nonnegative",
        "IDT.QMClosure.RawPlanePhaseGramKernel.d_symmetric",
        "IDT.QMClosure.RawPlanePhaseGramKernel.d_sq",
        "IDT.QMClosure.RawPlanePhaseGramKernel.G_adjoint",
        "IDT.QMClosure.RawPlanePhaseGramKernel.mixer_null",
        "IDT.QMClosure.RawPlanePhaseGramKernel.localKernel",
        "IDT.QMClosure.RawPlanePhaseGramKernel.triangle_iff_three_point" ] },
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseGramControl.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseGramControl.fourX",
        "IDT.QMClosure.RawPlanePhaseGramControl.fourY",
        "IDT.QMClosure.RawPlanePhaseGramControl.fourU",
        "IDT.QMClosure.RawPlanePhaseGramControl.fourZ",
        "IDT.QMClosure.RawPlanePhaseGramControl.four_cross_entries",
        "IDT.QMClosure.RawPlanePhaseGramControl.four_diagonal_entries",
        "IDT.QMClosure.RawPlanePhaseGramControl.four_quadratic",
        "IDT.QMClosure.RawPlanePhaseGramControl.not_four_point_positive",
        "IDT.QMClosure.RawPlanePhaseGramControl.threeX",
        "IDT.QMClosure.RawPlanePhaseGramControl.threeY",
        "IDT.QMClosure.RawPlanePhaseGramControl.threeZ",
        "IDT.QMClosure.RawPlanePhaseGramControl.three_cross_entries",
        "IDT.QMClosure.RawPlanePhaseGramControl.three_diagonal_entries",
        "IDT.QMClosure.RawPlanePhaseGramControl.three_quadratic",
        "IDT.QMClosure.RawPlanePhaseGramControl.not_three_point_positive",
        "IDT.QMClosure.RawPlanePhaseGramControl.triangleP",
        "IDT.QMClosure.RawPlanePhaseGramControl.triangleQ",
        "IDT.QMClosure.RawPlanePhaseGramControl.triangleR",
        "IDT.QMClosure.RawPlanePhaseGramControl.triangle_pr_sq",
        "IDT.QMClosure.RawPlanePhaseGramControl.triangle_qr_sq",
        "IDT.QMClosure.RawPlanePhaseGramControl.triangle_pq_sq",
        "IDT.QMClosure.RawPlanePhaseGramControl.triangle_squared_defect",
        "IDT.QMClosure.RawPlanePhaseGramControl.strict_triangle_violation",
        "IDT.QMClosure.RawPlanePhaseGramControl.not_triangle",
        "IDT.QMClosure.RawPlanePhaseGramControl.constructed_continuous_countercontrol" ] }]
  plannedArtifacts := []
  dependencies := [
    "raw_continuous_plane_phase_wall",
    "raw_continuous_plane_local_theory",
    "raw_metric_gram_arity",
    "raw_four_point_gram_bridge"]
  limits := [
    "The checked rational witnesses and triangle failure concern the actual operation-defined response and distance. The generic signed-four-ray comparison in raw_metric_gram_arity remains separately ANALYTIC/UNCHECKED.",
    "This actual operation is excluded by both global three-point and four-point positivity. Whether triangle inequality or three-point positivity forces SparseMarginalLaw in the complete native-plane class remains open.",
    "Supplied complex geometry remains an omission-control input. No physical primitive origin, Born interpretation, actualization, full QM or primitive closure is recorded. Public and manifest statuses remain unchanged."] }

def rawMidpointGramCompatibility : ResearchTask := {
  id := "raw_midpoint_gram_compatibility"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For the generic geometry, supply any carrier, a symmetric real kernel G, a real-parameter preparation map scale with G(scale(r,x),y)=r*G(x,y) for every real r, any midpoint map mid, and pairwise nonnegative squaredDistance(x,y)=G(x,x)+G(y,y)-2*G(x,y).",
    "For the ordinary-distance formulation, supply a nonnegative real d with d(x,y)^2=squaredDistance(x,y). Its midpoint convexity means d(z,mid(x,y)) <= (d(z,x)+d(z,y))/2 for all z,x,y.",
    "For the raw sparse bridge, also supply the existing Selection.Contract D and four-field LocalKernel D G, consisting of symmetry, G(x,x)=W(x), the A/B adjoint identity and the mixer-null relation."]
  conclusions := [
    "Global squared midpoint convexity is equivalent to full kernel-row averaging G(mid(x,y),z)=(G(x,z)+G(y,z))/2. The forward proof uses complete real row scaling and the vanishing slope of an affine function nonnegative for every real parameter. It uses no asymptotic limit.",
    "An available anchor gives a representative for every finite real weighted sum of kernel rows by repeated scaled midpoints. Symmetry and pairwise nonnegative squares then make every finite Gram quadratic nonnegative. The empty tuple is handled directly, so this positivity theorem also covers an empty carrier.",
    "Under the nonnegative distance and squared-distance contract, ordinary distance midpoint convexity is also equivalent to full kernel-row averaging.",
    "With LocalKernel, either global midpoint-convexity formulation yields all finite Gram positivity, W nonnegative, pair conservation, ObservedMedial, SparseMarginalLaw and all six universal sparse test families. These raw conclusions use the existing four-point-positive reconstruction adapter."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawMidpointGramGeometry.lean"
      declarations := [
        "IDT.QMClosure.RawMidpointGramGeometry.squaredDistance",
        "IDT.QMClosure.RawMidpointGramGeometry.NonnegativeSquaredDistances",
        "IDT.QMClosure.RawMidpointGramGeometry.SquaredMidpointConvex",
        "IDT.QMClosure.RawMidpointGramGeometry.MidpointRowAverage",
        "IDT.QMClosure.RawMidpointGramGeometry.DistanceMidpointConvex",
        "IDT.QMClosure.RawMidpointGramGeometry.affine_slope_eq_zero",
        "IDT.QMClosure.RawMidpointGramGeometry.midpointRowAverage_of_squaredMidpointConvex",
        "IDT.QMClosure.RawMidpointGramGeometry.squaredDistance_midpoint",
        "IDT.QMClosure.RawMidpointGramGeometry.squaredMidpointConvex_of_midpointRowAverage",
        "IDT.QMClosure.RawMidpointGramGeometry.squaredMidpointConvex_iff_midpointRowAverage",
        "IDT.QMClosure.RawMidpointGramGeometry.diagonal_nonnegative",
        "IDT.QMClosure.RawMidpointGramGeometry.scaled_midpoint_row_sum",
        "IDT.QMClosure.RawMidpointGramGeometry.exists_finite_row_sum",
        "IDT.QMClosure.RawMidpointGramGeometry.gramNonnegative_of_midpointRowAverage",
        "IDT.QMClosure.RawMidpointGramGeometry.gramNonnegative_of_squaredMidpointConvex",
        "IDT.QMClosure.RawMidpointGramGeometry.nonnegativeSquaredDistances_of_distance",
        "IDT.QMClosure.RawMidpointGramGeometry.squaredMidpointConvex_of_distanceMidpointConvex",
        "IDT.QMClosure.RawMidpointGramGeometry.gramNonnegative_of_distanceMidpointConvex",
        "IDT.QMClosure.RawMidpointGramGeometry.distanceMidpointConvex_of_midpointRowAverage",
        "IDT.QMClosure.RawMidpointGramGeometry.distanceMidpointConvex_iff_midpointRowAverage" ] },
    { sourcePath := "Proofs/QMClosure/RawMidpointGramBridge.lean"
      declarations := [
        "IDT.QMClosure.RawMidpointGramBridge.conclusions_of_squaredMidpointConvex",
        "IDT.QMClosure.RawMidpointGramBridge.conclusions_of_distanceMidpointConvex" ] }]
  plannedArtifacts := []
  dependencies := ["raw_metric_gram_arity", "raw_four_point_gram_bridge"]
  limits := [
    "All real reference scalings and the global midpoint inequality are explicit mathematical premises of this route with open physical origin. The separate raw_dyadic_midpoint_compatibility task derives the corresponding kernel positivity and sparse conclusions from half and antiphase preparation maps with midpoint-half compatibility, using weaker preparation availability.",
    "The theorem gives exact kernel-row synthesis and positivity without supplying raw equality separation, native-plane coverage, scalar-action laws, raw associative addition or a Hilbert representation. Those stronger reconstruction targets remain outside this checked record.",
    "No physical geometry origin, Born interpretation, actualization, full QM or primitive closure is recorded. Public and manifest statuses remain unchanged."] }

def rawPlanePhaseMidpointControl : ResearchTask := {
  id := "raw_plane_phase_midpoint_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the actual continuous three-dimensional complex plane-phase operation, its operation-defined G and nonnegative distance d from raw_plane_phase_gram_control. Set mid(x,y)=b*m(x,i*y), with b=(1-i)/2, and ref(t)=t*Z for real t.",
    "Fix only the endpoint pair X=e1,Y=e2 and reference direction Z=e1+e3. Their actual midpoint is U=(e1+e2)/2."]
  conclusions := [
    "The actual midpoint formula gives mid(X,Y)=U. For every real t, the checked squared distances from ref(t) to X,Y,U are respectively 2*t^2+1-8*t/5, 2*t^2+1 and 2*t^2+1/2-t.",
    "For this one endpoint pair and this reference orbit, the endpoint mean squared distance minus midpoint squared distance is exactly 1/2+t/5. Its squared midpoint inequality holds exactly when t>=-5/2.",
    "At t=-3 the midpoint squared distance is 43/2 and the endpoint squared distances are 119/5 and 19. The midpoint squared distance exceeds their mean by 1/10.",
    "For the same actual operation and reference, the ordinary midpoint distance strictly exceeds the endpoint mean distance. Thus both global squared and ordinary distance midpoint convexity fail. In particular sqrt(43/2)>(sqrt(119/5)+sqrt(19))/2."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseMidpointControl.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseMidpointControl.mid",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.ref",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.selected_pair_parameter",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.mid_fourX_fourY",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.ref_fourX_sq",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.ref_fourY_sq",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.ref_fourU_sq",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.orbit_squared_midpoint_slack",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.orbit_squared_midpoint_iff",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.negative_three_squares",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.negative_three_squared_defect",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.distance_square_eq",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.not_squaredMidpointConvex",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.strict_distance_midpoint_violation",
        "IDT.QMClosure.RawPlanePhaseMidpointControl.not_distanceMidpointConvex" ] }]
  plannedArtifacts := []
  dependencies := ["raw_plane_phase_gram_control", "raw_midpoint_gram_compatibility"]
  limits := [
    "The exact threshold quantifies only the selected pair X,Y and references ref(t). Passing that selected inequality on a restricted t range supplies no all-pair or globally restricted-reference convexity theorem.",
    "The midpoint and distance come from the actual operation. Supplied ordinary complex geometry remains an omission-control input with open physical origin.",
    "No Born interpretation, actualization, full QM or primitive closure is recorded. Public and manifest statuses remain unchanged."] }

def rawRealPlaneMetricControl : ResearchTask := {
  id := "raw_real_plane_metric_control"
  stage := .analyticAwaitingFormalization
  review := .parentAccepted
  assumptions := [
    "Use ordinary R^3 with T=diag(4,1,1). For unit vectors u,v set delta(u,v)=(angle(u,v)+angle(Tu,Tv))/2. For x=r*u,y=s*v with nonnegative radii, define G(x,y)=r*s*cos(delta(u,v)) and d(x,y)^2=r^2+s^2-2*r*s*cos(delta(u,v)). Extend through zero by the zero kernel row and ordinary radial distance.",
    "The carrier, Euclidean angles, linear T and ordinary real two-plane geometry are supplied mathematical inputs. This is an analytic geometry comparison awaiting its own Lean artifact."]
  conclusions := [
    "Accepted analytic result. Delta is a metric on unit directions with antipodal identity delta(-u,v)=pi-delta(u,v). Its cone distance d is a faithful metric, G is separately homogeneous for every real scalar, and all real three-point Gram quadratics are nonnegative.",
    "On every ordinary real two-plane P, normalized T gives a monotone antipodal angular lift f_P. The angular average h_P(t)=(t+f_P(t))/2 defines an onto real-homogeneous Euclidean polar chart. Chart choices differ by O(2), collinear transported sums agree, and every whole real plane is closed under its transported addition.",
    "For unit vectors e1,e2,u=(1,2,0)/sqrt(5),v=(1,0,2)/sqrt(5), the accepted analytic kernel entries are G12=0, G1u=G2u=G1v=1/sqrt(2), G2v=0 and Guv=c>0 with c^2=(29-6*sqrt(6))/50>1/4. With B=1/sqrt(2)-sqrt(2)*c, B is nonzero and coefficients (1,1,-sqrt(2),-B) give Gram quadratic -B^2<0.",
    "This real geometry therefore combines complete ordinary real two-plane Euclidean charts and a faithful triangle distance with failure of four-point Gram positivity. These analytic properties separate the real-plane geometry question from the remaining complex native-mixer question."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/RawRealPlaneMetricControl.lean"]
  dependencies := ["raw_metric_gram_arity", "raw_four_point_gram_bridge"]
  limits := [
    "All new real-plane construction, chart and metric assertions, exact entries and the negative four-point witness in this record remain ANALYTIC/UNCHECKED. Independent analytic review supplies no machine-checked proof status.",
    "The construction supplies real geometry only. An actual raw square-swap mixer, a global multiplication by i, coherent complex scalar structure and complete Hermitian complex two-planes remain outside its scope. It is not a complete raw countermodel.",
    "The naive complex extension fails already inside a complex two-plane. Whether complete Hermitian complex two-plane coverage, coherent complex scalar action, an actual native mixer and global three-point Gram positivity force SparseMarginalLaw remains open.",
    "No physical primitive origin, Born interpretation, actualization, full QM or primitive closure is recorded. Public and manifest statuses remain unchanged."] }

def rawDyadicMidpointCompatibility : ResearchTask := {
  id := "raw_dyadic_midpoint_compatibility"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply any carrier, a symmetric real kernel G, pairwise nonnegative squaredDistance(x,y)=G(x,x)+G(y,y)-2*G(x,y), and independent supplied maps H,N with G(H(x),z)=G(x,z)/2 and G(N(x),z)=-G(x,z).",
    "Supply a chosen midpoint map mid and HalfMidpointCompatible, meaning G(mid(H(x),H(y)),z)=G(mid(x,y),z)/2. The squared midpoint inequality is required for all reference and endpoint preparations.",
    "For the raw sparse conclusion, retain the existing Selection.Contract and its four-field LocalKernel. The supplied half map H has no required identification with the raw attenuation A(D)."]
  conclusions := [
    "Under the supplied kernel symmetry, half and antiphase identities and pairwise nonnegative squares, full midpoint-row averaging is equivalent to the conjunction of global squared midpoint convexity and HalfMidpointCompatible.",
    "Iterating H contracts the target pair. Comparing the fixed references z and N(z) bounds both signs of its row defect by one fixed constant times successive real dyadic powers. The Archimedean real-number argument forces that defect to vanish.",
    "Raw preparation equality mid(H(x),H(y))=H(mid(x,y)) supplies HalfMidpointCompatible as a sufficient corollary. The main theorem requires only the kernel-row identity.",
    "Normalized finite signed-integer list synthesis proves all integer-coefficient Gram inequalities. Clearing common rational denominators and density in finite real coefficient spaces then yield every finite real Gram inequality, including empty tuples and empty carriers.",
    "With the explicit LocalKernel adapter, these dyadic midpoint premises imply all finite Gram positivity, W nonnegative, pair conservation, ObservedMedial, SparseMarginalLaw and the six universal sparse test families."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawDyadicMidpointGram.lean"
      declarations := [
        "IDT.QMClosure.RawDyadicMidpointGram.HalfMidpointCompatible",
        "IDT.QMClosure.RawDyadicMidpointGram.halfIterate",
        "IDT.QMClosure.RawDyadicMidpointGram.halfIterate_row",
        "IDT.QMClosure.RawDyadicMidpointGram.midpoint_halfIterate_row",
        "IDT.QMClosure.RawDyadicMidpointGram.halfIterate_kernel",
        "IDT.QMClosure.RawDyadicMidpointGram.midpoint_halfIterate_diagonal",
        "IDT.QMClosure.RawDyadicMidpointGram.le_zero_of_le_dyadic_mul",
        "IDT.QMClosure.RawDyadicMidpointGram.midpoint_slack_nonnegative",
        "IDT.QMClosure.RawDyadicMidpointGram.midpointRowAverage_of_squaredMidpointConvex",
        "IDT.QMClosure.RawDyadicMidpointGram.halfMidpointCompatible_of_preparationEquality",
        "IDT.QMClosure.RawDyadicMidpointGram.midpointRowAverage_iff_squaredMidpointConvex_and_compatible",
        "IDT.QMClosure.RawDyadicMidpointGram.diagonal_nonnegative",
        "IDT.QMClosure.RawDyadicMidpointGram.midpoint_antiphase_zero_row",
        "IDT.QMClosure.RawDyadicMidpointGram.exists_list_row_sum",
        "IDT.QMClosure.RawDyadicMidpointGram.signedCopies",
        "IDT.QMClosure.RawDyadicMidpointGram.signedCopies_row_sum",
        "IDT.QMClosure.RawDyadicMidpointGram.integerRows",
        "IDT.QMClosure.RawDyadicMidpointGram.integerRows_row_sum",
        "IDT.QMClosure.RawDyadicMidpointGram.exists_integer_row_sum",
        "IDT.QMClosure.RawDyadicMidpointGram.quadratic_scaled",
        "IDT.QMClosure.RawDyadicMidpointGram.integer_quadratic_nonnegative",
        "IDT.QMClosure.RawDyadicMidpointGram.exists_common_denominator",
        "IDT.QMClosure.RawDyadicMidpointGram.gramNonnegative_of_integer_tests",
        "IDT.QMClosure.RawDyadicMidpointGram.gramNonnegative_of_midpointRowAverage",
        "IDT.QMClosure.RawDyadicMidpointGram.gramNonnegative_of_squaredMidpointConvex",
        "IDT.QMClosure.RawDyadicMidpointGram.conclusions_of_squaredMidpointConvex" ] }]
  plannedArtifacts := []
  dependencies := ["raw_midpoint_gram_compatibility", "raw_four_point_gram_bridge"]
  limits := [
    "Half-row homogeneity, coherent antiphase, midpoint-half compatibility and the all-input squared midpoint inequality remain supplied mathematical premises with open physical origin.",
    "The proof uses the Archimedean real numbers and topology of finite real coefficient spaces for its density step. It supplies no preparation map for arbitrary real scaling, unbounded reference preparation, topology on the preparation carrier or physical closure under arbitrary sums.",
    "The half map is independent supplied structure. Its identification with any native raw attenuation requires a separate checked bridge.",
    "No physical primitive origin, Born interpretation, actualization, full QM or primitive closure is recorded. Public and manifest statuses remain unchanged."] }

def rawTripodMidpointControl : ResearchTask := {
  id := "raw_tripod_midpoint_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply the bounded carrier Fin 3 times Icc[0,1], retaining three zero representatives. Its real kernel is G((i,r),(j,s))=r*s on the same ray and -r*s on different rays. Set Q(x,y)=G(x,x)+G(y,y)-2*G(x,y).",
    "The half map preserves the ray and halves the radius. On one ray the chosen midpoint averages radii. On different rays it selects the longer ray with radius half the radius difference, selecting the first zero representative for a tie."]
  conclusions := [
    "On the whole bounded carrier, G is symmetric, Q is nonnegative, G(H(x),z)=G(x,z)/2 and the actual preparation identity mid(H(x),H(y))=H(mid(x,y)) holds for every endpoint pair.",
    "The strong squared midpoint inequality Q(z,mid(x,y)) <= (Q(z,x)+Q(z,y))/2-Q(x,y)/4 holds for every triple on the complete carrier. Consequently the weaker squared midpoint inequality also holds universally.",
    "The three unit-radius tips have Gram quadratic -3 at the all-ones coefficient vector, so global three-point positivity fails.",
    "No carrier map N can satisfy G(N(x),z)=-G(x,z) for every x,z, and full midpoint-row averaging fails. The combined bounded_half_midpoint_countercontrol theorem records these properties for the same explicit carrier and operations.",
    "This is an all-pair omission control for removing coherent antiphase from the dyadic midpoint contract. It establishes the failure of that implication even with the stronger squared midpoint inequality and raw midpoint-half commutation."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawTripodMidpointControl.lean"
      declarations := [
        "IDT.QMClosure.RawTripodMidpointControl.G",
        "IDT.QMClosure.RawTripodMidpointControl.Q",
        "IDT.QMClosure.RawTripodMidpointControl.half",
        "IDT.QMClosure.RawTripodMidpointControl.mid",
        "IDT.QMClosure.RawTripodMidpointControl.G_symmetric",
        "IDT.QMClosure.RawTripodMidpointControl.radius_bounds",
        "IDT.QMClosure.RawTripodMidpointControl.G_half_left",
        "IDT.QMClosure.RawTripodMidpointControl.mid_half",
        "IDT.QMClosure.RawTripodMidpointControl.nonnegativeSquaredDistances",
        "IDT.QMClosure.RawTripodMidpointControl.StrongSquaredMidpointConvex",
        "IDT.QMClosure.RawTripodMidpointControl.strongSquaredMidpointConvex",
        "IDT.QMClosure.RawTripodMidpointControl.squaredMidpointConvex",
        "IDT.QMClosure.RawTripodMidpointControl.tip",
        "IDT.QMClosure.RawTripodMidpointControl.tips_quadratic",
        "IDT.QMClosure.RawTripodMidpointControl.not_three_point_positive",
        "IDT.QMClosure.RawTripodMidpointControl.no_coherent_antipode",
        "IDT.QMClosure.RawTripodMidpointControl.not_midpointRowAverage",
        "IDT.QMClosure.RawTripodMidpointControl.bounded_half_midpoint_countercontrol" ] }]
  plannedArtifacts := []
  dependencies := ["raw_dyadic_midpoint_compatibility"]
  limits := [
    "The three zero aliases are retained. A faithful metric on this raw carrier is outside the checked claim.",
    "No actual raw square-swap mixer, global complex scalar action or native-plane structure is supplied. The result is a kernel-and-midpoint omission control within its exact listed hypotheses.",
    "No physical primitive origin, Born interpretation, actualization, full QM or primitive closure is recorded. Public and manifest statuses remain unchanged."] }

def rawPlanePhaseParameterWall : ResearchTask := {
  id := "raw_plane_phase_parameter_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the supplied carrier Vec=Fin 3 -> Complex and the particular family m_lambda(x,y)=familyM(lambda*parameter(x,y),x,y), for any real lambda. Define G_lambda(x,y)=(W(x)+W(y)-2*W(m_lambda(x,-i*y)))/2 and d_lambda(x,y)=sqrt(W(x)+W(y)-2*G_lambda(x,y)).",
    "The complex coordinates, weight W, ordinary-plane parameter, ratio and familyM are supplied mathematical structure from RawPlanePhaseFamily, RawPlanePhaseGeometry and RawPlanePhaseGramKernel. The checked claim concerns this specified family."]
  conclusions := [
    "For every real lambda, the actual response G_lambda is symmetric, real-homogeneous in each input and has diagonal W. Its distance is nonnegative and d_lambda(x,y)^2=G_lambda(x,x)+G_lambda(y,y)-2*G_lambda(x,y). Triangle inequality is equivalent to three-point Gram nonnegativity under these checked identities.",
    "The checked conjugate-first response identity is G_lambda(x,y)=Re(phase(lambda*P(x,y)*R(x))*phase(-lambda*P(x,y)*R(y))*<x,y>), with P=parameter and R=ratio.",
    "For lambda != 0, set L=36+lambda^2, epsilon=lambda/L and eta=phase(-lambda/6). The preparations X=(1,1,1), -Y with Y=(1,i,1), and eta*Z(epsilon) with Z(epsilon)=(0,i-1,epsilon), at all-ones real coefficients, have actual Gram quadratic scalarQ(lambda) <= -2*epsilon^2 < 0.",
    "The exact scalarQ reduction uses M=18+lambda^2, Uplus=L+M*(epsilon^2+epsilon), Uminus=L+M*(epsilon^2-epsilon), p=3*lambda*epsilon*(epsilon+1)/Uplus and m=3*lambda*epsilon*(1-epsilon)/Uminus, giving scalarQ=epsilon^2+4*((-m+(1+epsilon)*m^2)/(1+m^2)-(p+(epsilon-1)*p^2)/(1+p^2)). The cited scalar bounds prove the uniform exclusion.",
    "At lambda=0, G_0 equals nativeG and is Gram nonnegative at every finite arity. For this particular family, global three-point Gram nonnegativity holds exactly when lambda=0, and global triangle inequality holds exactly when lambda=0."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseParameterFamily.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseParameterFamily.m",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.G",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.d",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.G_inPlane",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.G_symmetric",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.G_diagonal",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.G_real_smul_left",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.G_real_smul_right",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.d_nonnegative",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.d_sq",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.triangle_iff_three_point",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.G_zero_parameter",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.nativeG_gram_nonnegative",
        "IDT.QMClosure.RawPlanePhaseParameterFamily.zero_parameter_gram_nonnegative" ] },
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseParameterBounds.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseParameterBounds.L",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.M",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.epsilon",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.Uplus",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.Uminus",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.p",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.m",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.scalarQ",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.epsilon_bounds",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.U_bounds",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.pm_positive",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.pm_upper",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.pm_sum_lower",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.scalarQ_upper",
        "IDT.QMClosure.RawPlanePhaseParameterBounds.scalarQ_negative" ] },
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseParameterWall.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseParameterWall.X",
        "IDT.QMClosure.RawPlanePhaseParameterWall.Y",
        "IDT.QMClosure.RawPlanePhaseParameterWall.Z",
        "IDT.QMClosure.RawPlanePhaseParameterWall.eta",
        "IDT.QMClosure.RawPlanePhaseParameterWall.preparations",
        "IDT.QMClosure.RawPlanePhaseParameterWall.G_eq_inner",
        "IDT.QMClosure.RawPlanePhaseParameterWall.actual_quadratic_scalar",
        "IDT.QMClosure.RawPlanePhaseParameterWall.actual_quadratic_upper",
        "IDT.QMClosure.RawPlanePhaseParameterWall.actual_quadratic_negative",
        "IDT.QMClosure.RawPlanePhaseParameterWall.not_three_point_nonnegative",
        "IDT.QMClosure.RawPlanePhaseParameterWall.three_point_nonnegative_iff",
        "IDT.QMClosure.RawPlanePhaseParameterWall.triangle_iff_zero" ] }]
  plannedArtifacts := []
  dependencies := ["raw_plane_phase_gram_control", "raw_metric_gram_arity"]
  limits := [
    "The parameter-uniform exclusion concerns only the supplied phase-deformation family. It supplies no general rigidity theorem for all complex native-plane models, and no smooth-rigidity claim is included among the checked conclusions.",
    "Continuity in the parameter, square-swap and a LocalKernel adapter for arbitrary lambda are outside the checked claim of these three modules.",
    "The complete Hermitian complex two-plane class with coherent complex scalars, actual native mixer and global three-point positivity remains open. Physical justification of compatibility with an external reference remains unexplained.",
    "No physical primitive origin, Born interpretation, actualization, full QM or primitive closure is recorded. Public and manifest statuses remain unchanged."] }

def rawLocalMidpointCompatibility : ResearchTask := {
  id := "raw_local_midpoint_compatibility"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply any carrier V, a symmetric real kernel G, unary maps H,N with G(H(x),z)=G(x,z)/2 and G(N(x),z)=-G(x,z), a chosen midpoint mid and HalfMidpointCompatible G H mid. No raw preparation commutation between H and N is required.",
    "For the local route, supply a predicate U that eventually contains every dyadically contracted preparation: for every x there exists M such that U(H^n(x)) for all n>=M. Require squared Jensen only when the three inputs z,x,y lie in U. Membership of mid(x,y) in U is not required.",
    "Alternatively supply SecondOrderJensenControl: for every fixed x,y,z there exists a real K such that for every natural n, squaredDistance(G,z,mid(H^n(x),H^n(y))) <= (squaredDistance(G,z,H^n(x))+squaredDistance(G,z,H^n(y)))/2+(2^(-n))^2*K. K may depend on the fixed triple and is uniform in n.",
    "For the equivalences, positive diagonal-weight-ball specialization and all-finite Gram conclusions, also supply pairwise nonnegative squared distances. The raw sparse conclusions additionally require the existing Selection.Contract D and its explicit LocalKernel D G adapter."]
  conclusions := [
    "Local squared Jensen on an arbitrary dyadically absorbing U implies complete midpoint-row averaging. With pairwise nonnegative squares, it is equivalent to midpoint-row averaging under the stated symmetry, half-row, antiphase and midpoint-half compatibility premises.",
    "Every strictly positive diagonal-weight ball G(x,x)<=R is dyadically absorbing under the stated symmetry, half-row and pairwise nonnegative-square premises. Local squared Jensen on such a ball therefore implies midpoint-row averaging.",
    "The one-sided second-order Jensen control with its per-triple constant uniform in n implies midpoint-row averaging. With pairwise nonnegative squares it is equivalent to midpoint-row averaging.",
    "Under pairwise nonnegative squares, either local Jensen on a dyadically absorbing U, local Jensen on a positive weight ball, or SecondOrderJensenControl implies Gram nonnegativity at every finite real arity.",
    "With the additional explicit LocalKernel adapter, the local absorbing-set and second-order routes imply all finite Gram positivity, nonnegative D.weight, pair conservation, ObservedMedial, SparseMarginalLaw and the six universal sparse test families."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawLocalMidpointCompatibility.lean"
      declarations := [
        "IDT.QMClosure.RawLocalMidpointCompatibility.DyadicallyAbsorbing",
        "IDT.QMClosure.RawLocalMidpointCompatibility.LocalSquaredMidpointConvex",
        "IDT.QMClosure.RawLocalMidpointCompatibility.DiagonalWeightBall",
        "IDT.QMClosure.RawLocalMidpointCompatibility.SecondOrderJensenControl",
        "IDT.QMClosure.RawLocalMidpointCompatibility.le_zero_of_eventually_le_dyadic_mul",
        "IDT.QMClosure.RawLocalMidpointCompatibility.midpointRowAverage_of_localSquaredMidpointConvex",
        "IDT.QMClosure.RawLocalMidpointCompatibility.localSquaredMidpointConvex_iff_midpointRowAverage",
        "IDT.QMClosure.RawLocalMidpointCompatibility.dyadicallyAbsorbing_diagonalWeightBall",
        "IDT.QMClosure.RawLocalMidpointCompatibility.midpointRowAverage_of_weightBallSquaredMidpointConvex",
        "IDT.QMClosure.RawLocalMidpointCompatibility.midpointRowAverage_of_secondOrderJensenControl",
        "IDT.QMClosure.RawLocalMidpointCompatibility.secondOrderJensenControl_iff_midpointRowAverage",
        "IDT.QMClosure.RawLocalMidpointCompatibility.gramNonnegative_of_localSquaredMidpointConvex",
        "IDT.QMClosure.RawLocalMidpointCompatibility.gramNonnegative_of_weightBallSquaredMidpointConvex",
        "IDT.QMClosure.RawLocalMidpointCompatibility.gramNonnegative_of_secondOrderJensenControl",
        "IDT.QMClosure.RawLocalMidpointCompatibility.conclusions_of_localSquaredMidpointConvex",
        "IDT.QMClosure.RawLocalMidpointCompatibility.conclusions_of_secondOrderJensenControl" ] }]
  plannedArtifacts := []
  dependencies := ["raw_dyadic_midpoint_compatibility", "raw_four_point_gram_bridge"]
  limits := [
    "Local Jensen and second-order Jensen control remain additional mathematical premises. Their compatibility with an external reference is an open origin obligation.",
    "The proof uses Archimedean real dyadic decay and the imported finite coefficient-space density argument. It supplies no topology or arbitrary-real scaling operation on the preparation carrier.",
    "The supplied H,N and mid require only their stated row laws and midpoint-half compatibility. They have no automatic identification with raw attenuation, antiphase or midpoint operations in an external contract.",
    "No physical primitive origin, Born interpretation, actualization, full QM or primitive closure is recorded. Public and manifest statuses remain unchanged."] }

def rawPlanePhaseLocalMidpointControl : ResearchTask := {
  id := "raw_plane_phase_local_midpoint_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the existing lambda-one supplied complex plane-phase operation, its actual response G, distance d and midpoint mid from raw_plane_phase_midpoint_control. Set half(x)=(1/2)*x, antipode(x)=-x and scale(r,x)=r*x in the supplied complex-coordinate carrier.",
    "For the selected-orbit formulas retain the existing specific preparations fourX, fourY, fourU=mid(fourX,fourY) and fourZ. For the CN identity require z in InPlane(x,y), the ordinary complex span generated by the endpoints x,y."]
  conclusions := [
    "The actual half and antipode satisfy their required kernel-row laws. Uniform complex covariance of mid gives the preparation equality mid(half(x),half(y))=half(mid(x,y)) and hence HalfMidpointCompatible. Squared distances are nonnegative, while complete midpoint-row averaging fails.",
    "Every strictly positive diagonal-weight ball fails LocalSquaredMidpointConvex for the actual G and mid. SecondOrderJensenControl G half mid also fails: some fixed triple admits no real error constant uniform over all contraction indices.",
    "For the selected pair and reference orbit, selectedSlack(t,e), defined as the endpoint mean of actual distance squares minus the actual midpoint distance square, equals e^2/2+t*e/5. The actual midpoint of scale(e,fourX),scale(e,fourY) is scale(e,fourU).",
    "At the fixed reference -fourZ, the midpoint excess over the endpoint mean equals e/5-e^2/2 and is strictly positive exactly when 0<e<2/5. On the two selected balanced reference rays t=e and t=-e, slack equals e^2*(1/2+1/5) and e^2*(1/2-1/5), respectively, and both are strictly positive for nonzero e.",
    "For every x,y and z in their endpoint-generated ordinary complex span InPlane(x,y), the actual squared-distance CN identity holds: Q(z,mid(x,y))=(Q(z,x)+Q(z,y))/2-Q(x,y)/4. The proof transports that pair plane by H(-parameter(x,y)) to the native coordinate midpoint."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseLocalMidpointControl.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.half",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.antipode",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.half_row",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.antipode_row",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.mid_smul",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.half_midpoint",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.halfMidpointCompatible",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.nonnegativeSquaredDistances",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.not_midpointRowAverage",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.not_localSquaredMidpointConvex_weightBall",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.not_secondOrderJensenControl",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.scale",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.squaredDistance_scale",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.mid_scaled_selected_pair",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.selectedSlack",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.selectedSlack_exact",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.fixed_reference_excess",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.fixed_reference_excess_positive_iff",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.balanced_selected_slacks",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.balanced_selected_slacks_positive",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.inPlane_mid",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.native_midpoint",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.H_mid",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.squaredDistance_inPlane",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.native_squared_CN",
        "IDT.QMClosure.RawPlanePhaseLocalMidpointControl.squared_CN_inPlane" ] }]
  plannedArtifacts := []
  dependencies := ["raw_local_midpoint_compatibility", "raw_plane_phase_midpoint_control"]
  limits := [
    "The passing balanced rays concern only the displayed endpoint pair and selected reference orbit. No all-triple balanced test is asserted.",
    "The checked CN identity requires the reference to lie in the complex span generated by the endpoint pair. It supplies no unrestricted external-reference Jensen law.",
    "This control uses lambda=1 only. Its supplied complex geometry and the physical origin of external-reference compatibility remain outside the checked result. No general smooth-rigidity theorem is recorded.",
    "No physical primitive origin, Born interpretation, actualization, full QM or primitive closure is recorded. Public and manifest statuses remain unchanged."] }

def threeSourceDistributiveSwapRoot : ResearchTask := {
  id := "three_source_distributive_swap_root"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "On an arbitrary carrier V supply a binary operation m with idempotence m(x,x)=x, bookend m(m(x,y),m(y,x))=y, left distributivity m(x,m(y,z))=m(m(x,y),m(x,z)) and right distributivity m(m(x,y),z)=m(m(x,z),m(y,z)). No additive, finite or division structure is supplied.",
    "For the complete-operation equivalences, supply T:(V times V)->(V times V), transparency T(x,x)=(x,x) and square-swap T(T(p))=swap(p). Use its existing firstChannel. RestrictedExchange compares all four output coordinates of row-after-column and column-after-row on ((x,x),(y,z))."]
  conclusions := [
    "The supplied binary laws imply left and right cancellation, explicit operation-term inverses for both translations and hence bijectivity of both ports on every carrier. They also imply cyclic exchange, alterability and the four-input medial law.",
    "The new Laws contract is equivalent to the existing MedialSwapRoot.Laws contract. The reverse direction obtains left and right distributivity by substituting repeated inputs in mediality.",
    "Under transparency and square-swap, RestrictedExchange is equivalent to the new Laws for the first channel and equivalent to CompleteExchange. CompleteExchange agrees with the existing RawNetworkMedialWall.RowColumnCommutes, with the equality orientation reversed.",
    "The three-source presentation counts three independent preparation values carried on four wires with one repeated value. It provides an equivalent presentation of the existing medial route and explicit division terms within that presentation."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ThreeSourceDistributiveSwapRoot.lean"
      declarations := [
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.Laws",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.oppositeLaws",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.left_injective",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.right_injective",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.rightDivisionTerm",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.leftDivisionTerm",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.rightDivisionTerm_apply",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.leftDivisionTerm_apply",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.rightDivisionTerm_reverse",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.leftDivisionTerm_reverse",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.right_bijective",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.left_bijective",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.cyclic_exchange",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.alterability",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.medial",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.toMedialSwapRootLaws",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.ofMedialSwapRootLaws",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.laws_iff_medialSwapRootLaws",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.laws_of_complete_operation",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.rowGate",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.transpose",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.columnGate",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.RestrictedExchange",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.CompleteExchange",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.completeExchange_iff_rowColumnCommutes",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.restrictedExchange_iff_laws",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.completeExchange_iff_medial",
        "IDT.QMClosure.ThreeSourceDistributiveSwapRoot.restrictedExchange_iff_completeExchange" ] }]
  plannedArtifacts := []
  dependencies := ["raw_medial_addition", "raw_network_medial_wall"]
  limits := [
    "The two distributivity laws and restricted overlapping-network exchange remain additional supplied process assumptions. Under the base laws they have the same logical strength as mediality. Their physical origin remains open.",
    "Repeating a preparation value requires repeatable preparation or explicit replay. The mathematical repeated input supplies no cloning operation.",
    "The existing raw_medial_addition record already provides raw-port reconstruction and the canonical group from medial laws. This equivalent presentation records no newly closed group-reconstruction obligation.",
    "Disjoint locality or no-signalling supplies no overlapping row/column exchange premise, and preparation exchange alone supplies no readout conservation.",
    "No physical primitive origin, actualization, Born interpretation, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def threeSourceExchangeReadoutBoundary : ResearchTask := {
  id := "three_source_exchange_readout_boundary"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Retain the exact Term2 and QuantifierfreeFormula2 syntax, supplied native and actual semantics, and ActualCountermodelProperties from raw_continuous_plane_local_theory. Let Gamma be any set of formulas each valid for every preparation pair in the supplied native complex three-dimensional model.",
    "For the independent readout boundary use the existing supplied native mixer with nonnegative quartic readout RawSparseQuarticControl.contract."]
  conclusions := [
    "The same actual lambda-one plane-phase operation satisfies every formula in Gamma and retains ActualCountermodelProperties, while RestrictedExchange fails.",
    "The quartic control satisfies the new distributive Laws, RestrictedExchange, CompleteExchange and nonnegative weight, while PairConserved and SparseMarginalLaw both fail. Thus even complete preparation exchange leaves these readout obligations open."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ThreeSourceExchangeReadoutBoundary.lean"
      declarations := [
        "IDT.QMClosure.ThreeSourceExchangeReadoutBoundary.actual_not_restrictedExchange",
        "IDT.QMClosure.ThreeSourceExchangeReadoutBoundary.native_valid_collection_exchange_countermodel",
        "IDT.QMClosure.ThreeSourceExchangeReadoutBoundary.quartic_laws",
        "IDT.QMClosure.ThreeSourceExchangeReadoutBoundary.quartic_exchange_readout_boundary" ] }]
  plannedArtifacts := []
  dependencies := ["three_source_distributive_swap_root", "raw_continuous_plane_local_theory", "raw_sparse_conservation_selection"]
  limits := [
    "The collection theorem has precisely the existing two-preparation quantifier-free syntax. It excludes arbitrary raw preparation constants, nested preparation quantifiers, arbitrary-reference ObservationalEq and topology predicates.",
    "Readout predicates receive finite real readout lists through a fixed predicate identical in both semantics, with no preparation-environment argument or model-dependent reinterpretation. External scalar-parameter families are covered only through their formula instances.",
    "The two controls are supplied mathematical constructions. Their preparation availability and an overlapping-exchange physical principle remain open.",
    "No physical primitive origin, actualization, Born interpretation, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def oneSidedDistributiveSwapControl : ResearchTask := {
  id := "one_sided_distributive_swap_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the finite carrier ((ZMod 5 times ZMod 5) times ZMod 5). Write omega(v,w)=v1*w2-v2*w1 and m((v,t),(w,s))=(-v+2*w,2*t-s-omega(v,w)). Define the complete operation T(x,y)=(m(x,y),m(y,x))."]
  conclusions := [
    "The symbolic identities establish idempotence, bookend and universal left distributivity. Both translations have explicit inverse terms, with forward and reverse identities and hence bijectivity.",
    "For X=((1,0),0), Y=((0,1),0), Z=((0,0),0), right distributivity has outputs ((1,3),3) and ((1,3),4). Consequently right distributivity, MedialSwapRoot.Laws and RestrictedExchange fail, although T is transparent and square-swap.",
    "The opposite operation m_op(x,y)=m(y,x) retains idempotence, bookend and both port bijections, satisfies universal right distributivity and fails left distributivity. Either individual distributivity law can therefore be omitted only at the cost exposed by the corresponding control."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/OneSidedDistributiveSwapControl.lean"
      declarations := [
        "IDT.QMClosure.OneSidedDistributiveSwapControl.Carrier",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.omega",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.m",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.idempotent",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.bookend",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.left_distributive",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.leftInverseTerm",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.rightInverseTerm",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.leftInverseTerm_apply",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.leftInverseTerm_reverse",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.rightInverseTerm_apply",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.rightInverseTerm_reverse",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.left_bijective",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.right_bijective",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.witnessX",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.witnessY",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.witnessZ",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.right_distributive_witness",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.not_right_distributive",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.not_medial",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.operation",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.transparent",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.square",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.not_restrictedExchange",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.opposite",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.opposite_idempotent",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.opposite_bookend",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.opposite_right_distributive",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.opposite_not_left_distributive",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.opposite_left_bijective",
        "IDT.QMClosure.OneSidedDistributiveSwapControl.opposite_right_bijective" ] }]
  plannedArtifacts := []
  dependencies := ["three_source_distributive_swap_root"]
  limits := [
    "This is a finite raw-algebra omission control on 125 carrier states. A nontrivial real readout, nonnegative conserved weight or physical realization is outside its checked scope.",
    "The control separates the individual distributivity laws under the listed raw algebraic hypotheses. It supplies no weaker physical derivation of their conjunction.",
    "No physical primitive origin, actualization, Born interpretation, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def rawProcessComparisonBridge : ResearchTask := {
  id := "raw_process_comparison_bridge"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply any real comparison D on a carrier V and a complete raw gate F on V times V. Define pairComparison(D,p,q)=D(p1,q1)+D(p2,q2) and PairComparisonNonexpanding by the all-input nonexpansion inequality for this exact sum.",
    "The isometry-from-nonexpansion theorem additionally assumes square-swap F(F(p))=swap(p). It requires no comparison nonnegativity or metric law.",
    "For the midpoint bound supply maps J,B, a zero and a midpoint map with D(Jx,Jy)=D(x,y), D(Bx,By)=D(x,y)/2, B(first(F(z,Jz)))=z, second(F(z,Jz))=zero and B(first(F(x,Jy)))=mid(x,y), together with PairComparisonNonexpanding D F. Dropping the residual additionally requires D nonnegative.",
    "For the separate four-point route supply the existing RawSparseConservationSelection.Contract, G and its LocalKernel with symmetry, weight diagonal, attenuation adjoint and mixer null relation, together with GramNonnegative G 4. Use D=squaredDistance G."]
  conclusions := [
    "Square-swap and assumed global nonexpansion imply exact pairComparison isometry. Reversibility strengthens an already supplied comparison law.",
    "The calibrated process comparison gives 2*D(mid(x,y),z)+D(second(F(x,Jy)),zero)<=D(x,z)+D(y,z). Nonnegativity of the retained residual yields the weak midpoint Jensen bound.",
    "For a symmetric real kernel G with nonnegative squared distances, the explicit comparison calibration and nonexpansion premises imply SquaredMidpointConvex G mid.",
    "The existing LocalKernel and four-point Gram-positivity contract implies pairComparison isometry under the actual complete operation for D=squaredDistance G, and hence PairComparisonNonexpanding. Pair-weight conservation is outside the input assumptions of this implication."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawProcessComparisonBridge.lean"
      declarations := [
        "IDT.QMClosure.RawProcessComparisonBridge.pairComparison",
        "IDT.QMClosure.RawProcessComparisonBridge.PairComparisonNonexpanding",
        "IDT.QMClosure.RawProcessComparisonBridge.pairComparison_swap",
        "IDT.QMClosure.RawProcessComparisonBridge.pairComparison_isometry_of_nonexpanding",
        "IDT.QMClosure.RawProcessComparisonBridge.pairComparison_isometry_of_fourPointPositive",
        "IDT.QMClosure.RawProcessComparisonBridge.pairComparisonNonexpanding_of_fourPointPositive",
        "IDT.QMClosure.RawProcessComparisonBridge.calibrated_midpoint_bound_with_residual",
        "IDT.QMClosure.RawProcessComparisonBridge.calibrated_midpoint_convex",
        "IDT.QMClosure.RawProcessComparisonBridge.squaredMidpointConvex_of_calibrated_processComparison" ] }]
  plannedArtifacts := []
  dependencies := ["raw_four_point_gram_bridge", "raw_local_midpoint_compatibility"]
  limits := [
    "The sum over the two raw pair ports is supplied as the block comparison. A Hilbert tensor product and an independent quantum-composite comparison rule remain outside the result.",
    "Quarter-turn isometry, attenuation calibration, calibrated independent-reference preparation and the port-additive all-input nonexpansion law remain explicit mathematical premises with open operational origin.",
    "Reversibility alone supplies no nonexpansion of this particular comparison. The four-point route retains the existing supplied LocalKernel and Gram-positivity assumptions.",
    "Tensor/composite, entanglement and Bell closure remain outside this result. The classical product-distribution reference in the separate classical completion is a different construction.",
    "No physical primitive origin, actualization, Born interpretation, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def pairComparisonReconstruction : ResearchTask := {
  id := "pair_comparison_reconstruction"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply an arbitrary carrier V, a chosen vacuum o and a total two-port operation F. Require F squared equal to swap and F(x,x)=(x,x) for every input.",
    "Supply a real comparison delta that is symmetric, nonnegative and zero on the diagonal. For every four preparations x,y,u,v require delta((F(x,y))1,(F(u,v))1)+delta((F(x,y))2,(F(u,v))2)<=delta(x,u)+delta(y,v). This exact sum and its universal process inequality are supplied."]
  conclusions := [
    "Derive exact pair-comparison isometry from square-swap. With Q(x)=delta(x,o), derive nonnegative vacuum-zero pair-weight conservation.",
    "For the reconstructed polarization G(x,y)=(Q(x)+Q(y)-delta(x,y))/2, derive observed mediality and the sparse marginal law. Raw addition, Gram positivity and conditional negative definiteness are absent from the input contract.",
    "Construct the observed quotient and a mathematical complex Hilbert feature map with Q(x)=norm(feature(x)) squared and the full supplied delta(x,y)=norm(feature(x)-feature(y)) squared. Derive comparison attenuation by one half under the reconstructed vacuum splitter A.",
    "The supplied comparison is zero exactly when preparations are observationally equivalent under the reconstructed weight. A separate existing complex mixer with squared-norm comparison satisfies every contract premise, has delta(1,0)=1 and produces a nonzero reconstructed feature."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/PairComparisonReconstruction.lean"
      declarations := [
        "IDT.QMClosure.PairComparisonReconstruction.Contract.comparison_isometry",
        "IDT.QMClosure.PairComparisonReconstruction.Contract.conserved",
        "IDT.QMClosure.PairComparisonReconstruction.Contract.observed_medial",
        "IDT.QMClosure.PairComparisonReconstruction.Contract.sparse",
        "IDT.QMClosure.PairComparisonReconstruction.Contract.norm_feature_sq",
        "IDT.QMClosure.PairComparisonReconstruction.Contract.comparison_half_A",
        "IDT.QMClosure.PairComparisonReconstruction.Contract.inner_feature_re",
        "IDT.QMClosure.PairComparisonReconstruction.Contract.comparison_eq_norm_sub_sq",
        "IDT.QMClosure.PairComparisonReconstruction.Contract.feature_eq_iff_observationalEq",
        "IDT.QMClosure.PairComparisonReconstruction.Contract.comparison_eq_zero_iff_observationalEq",
        "IDT.QMClosure.PairComparisonReconstruction.ComplexWitness.model",
        "IDT.QMClosure.PairComparisonReconstruction.ComplexWitness.comparison_one_zero",
        "IDT.QMClosure.PairComparisonReconstruction.ComplexWitness.feature_one_ne_zero"] }]
  plannedArtifacts := []
  dependencies := ["raw_process_comparison_bridge", "raw_observable_medial_wall",
    "raw_sparse_marginal_reconstruction", "operational_context_quotient"]
  limits := [
    "The pair-port additive comparison rule and exact all-input process inequality remain supplied separability and process laws. The Hilbert carrier is a conditional mathematical construction. The complex consistency example supplies its carrier, mixer and squared-norm comparison and establishes no primitive physical origin.",
    "The reconstructed Q=delta(-,o) is not identified with the original response Qraw. The generic identification Qraw(x)=c*delta(x,o) for a positive scale c remains open. For the negative-log-affinity specialization this is Qraw(x)=c*(-log A(x,o)); the scale and physical origin of the affinity and process laws remain open.",
    "No physical detector origin, event actualization, Born interpretation, composites, Bell, physical-scale derivation or full-QM closure is established. Public and manifest statuses remain unchanged."] }

def classicalAffinityLogWall : ResearchTask := {
  id := "classical_affinity_log_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply the three Bernoulli rows (1/5,4/5), (1/2,1/2) and (4/5,1/5). Their actual finite classical affinity is sum_r sqrt(P_i(r)*P_j(r)).",
    "The separate abstract negative-log bridge assumes a supplied strictly positive affinity A and a supplied gate F under which the product of the two output-port affinities is at least the product of the two input-port affinities."]
  conclusions := [
    "Every actual probability-row entry is positive and each row sums to one. The actual affinity is symmetric, positive, at most one, diagonal-one and positive semidefinite by its square-root-row Gram factorization. Its adjacent entry is a=3/sqrt(10) and its endpoint entry is 4/5.",
    "The actual symmetric nonnegative zero-diagonal comparison delta=-log(affinity) fails conditional negative definiteness. For zero-sum c=(1,-2,1), its quadratic form is exactly 2*log(81/80)>0.",
    "The entrywise square root of the actual affinity fails positive semidefiniteness. For c=(1,-2*sqrt(a),1), its quadratic form is 2*(1+sqrt(4/5)-2*a)<0.",
    "For a separately supplied affinity, symmetry, diagonal-one and the upper bound one transfer to negative-log symmetry, diagonal-zero and nonnegativity under positivity. The separately supplied product-affinity process inequality implies the exact summed pair negative-log nonexpansion law. The affinityContract adapter assembles these explicit laws with a supplied vacuum and transparent square-swap gate; negativeLog_distance gives the resulting full squared Hilbert distance."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ClassicalAffinityLogWall.lean"
      declarations := [
        "IDT.QMClosure.ClassicalAffinityLogWall.probabilityRow_positive",
        "IDT.QMClosure.ClassicalAffinityLogWall.probabilityRow_normalized",
        "IDT.QMClosure.ClassicalAffinityLogWall.affinity_matrix",
        "IDT.QMClosure.ClassicalAffinityLogWall.adjacent_eq_three_div_sqrt_ten",
        "IDT.QMClosure.ClassicalAffinityLogWall.affinity_positive",
        "IDT.QMClosure.ClassicalAffinityLogWall.affinity_le_one",
        "IDT.QMClosure.ClassicalAffinityLogWall.affinity_eq_gram",
        "IDT.QMClosure.ClassicalAffinityLogWall.affinity_posSemidef",
        "IDT.QMClosure.ClassicalAffinityLogWall.logWitness_zero_sum",
        "IDT.QMClosure.ClassicalAffinityLogWall.logWitness_quadraticForm",
        "IDT.QMClosure.ClassicalAffinityLogWall.logWitness_positive",
        "IDT.QMClosure.ClassicalAffinityLogWall.logComparison_not_conditionallyNegative",
        "IDT.QMClosure.ClassicalAffinityLogWall.rootWitness_quadraticForm",
        "IDT.QMClosure.ClassicalAffinityLogWall.rootWitness_negative",
        "IDT.QMClosure.ClassicalAffinityLogWall.rootAffinity_not_posSemidef",
        "IDT.QMClosure.ClassicalAffinityLogWall.negativeLog_symmetric",
        "IDT.QMClosure.ClassicalAffinityLogWall.negativeLog_self",
        "IDT.QMClosure.ClassicalAffinityLogWall.negativeLog_nonnegative",
        "IDT.QMClosure.ClassicalAffinityLogWall.negativeLog_pair_nonexpanding",
        "IDT.QMClosure.ClassicalAffinityLogWall.affinityContract",
        "IDT.QMClosure.ClassicalAffinityLogWall.negativeLog_distance"] }]
  plannedArtifacts := []
  dependencies := ["raw_process_comparison_bridge", "classical_marginal_comparison_wall",
    "pair_comparison_reconstruction"]
  limits := [
    "Ordinary classical-affinity positivity and Gram positivity do not suffice to derive CND of the negative logarithm or positive semidefiniteness of every positive entrywise power. The full universal globally covariant gate contract remains a separate stronger hypothesis.",
    "The abstract product-affinity law is supplied. No Markov data-processing theorem, admissible noise carrier, gate-compatible detector realization or statistical detector-model existence theorem is established here.",
    "No identification of the original response Qraw, physical comparison scale, event actualization, Born interpretation, composites, Bell, full QM or physical-scale closure is established. Public and manifest statuses remain unchanged."] }

def finiteOutcomeAffinityRigidity : ResearchTask := {
  id := "finite_outcome_affinity_rigidity"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply PairComparisonReconstruction.Contract on an arbitrary raw carrier V and normalized nonnegative real probability rows K(x) on one fixed finite outcome space Omega. Identify the full contract comparison with minus the logarithm of the actual finite affinity sum_w sqrt(K(x,w)*K(y,w)).",
    "For equality of the actual probability rows, additionally require strictly positive affinity for every pair of raw preparations. No finite raw carrier, uniform positive floor, input group, topology or completeness is assumed."]
  conclusions := [
    "Among card(Omega)+1 normalized rows, two distinct indices have affinity at least 1/card(Omega). Combining this finite packing bound with constructed natural multiples in the reconstructed feature image forces every reconstructed feature and comparison to vanish. The observed quotient is a subsingleton.",
    "Under the separate all-pairs positive-affinity guard, every actual probability row K(x) is equal to every K(y). This excludes nontrivial law families satisfying the entire supplied reconstruction contract on one fixed finite outcome space."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FiniteOutcomeAffinityRigidity.lean"
      declarations := [
        "IDT.QMClosure.FiniteOutcomeAffinityRigidity.finite_affinity_packing",
        "IDT.QMClosure.FiniteOutcomeAffinityRigidity.law_eq_of_affinity_one",
        "IDT.QMClosure.FiniteOutcomeAffinityRigidity.exists_feature_nat_multiple",
        "IDT.QMClosure.FiniteOutcomeAffinityRigidity.feature_eq_zero",
        "IDT.QMClosure.FiniteOutcomeAffinityRigidity.comparison_eq_zero",
        "IDT.QMClosure.FiniteOutcomeAffinityRigidity.observed_quotient_subsingleton",
        "IDT.QMClosure.FiniteOutcomeAffinityRigidity.all_laws_equal"] }]
  plannedArtifacts := []
  dependencies := ["pair_comparison_reconstruction", "classical_affinity_log_wall"]
  limits := [
    "The feature, comparison and observed-quotient conclusions also hold algebraically when some affinity is zero because Lean's real logarithm is totalized. Equality of actual laws requires positive affinity. Zero-overlap negative logarithms receive no statistical-distance interpretation here.",
    "Identical law rows and a subsingleton observed quotient do not imply a singleton raw carrier. The theorem does not exclude individual finite experiments, all finite measurement families or approximate realizations, and supplies no quantitative approximation bound.",
    "The input contract retains its exact universal process-comparison law. Physical carrier availability, the original response Qraw, actualization, Born, composites, Bell and physical scales remain open."] }

def relativeEntropyDataProcessing : ResearchTask := {
  id := "relative_entropy_data_processing"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply actual probability measures on arbitrary measurable spaces. Deterministic processing is a measurable map. Stochastic processing uses one common Markov kernel for the two compared measures. Independent products use the ordinary product measures."]
  conclusions := [
    "Actual measure-theoretic relative entropy cannot increase under a measurable map or one common Markov kernel. Measurable equivalences preserve relative entropy.",
    "Relative entropy is additive on independent products, including infinite values. Finite input relative entropy remains finite under measurable-map processing.",
    "The proofs use the existing Radon-Nikodym conditional-expectation identity, convex Jensen inequality and KL chain rule. No comparison-level contraction inequality, Standard Borel structure, disintegration or reference-measure-preserving hypothesis is supplied."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RelativeEntropyDataProcessing.lean"
      declarations := [
        "IDT.QMClosure.RelativeEntropyDataProcessing.klDiv_map_le",
        "IDT.QMClosure.RelativeEntropyDataProcessing.klDiv_map_ne_top",
        "IDT.QMClosure.RelativeEntropyDataProcessing.klDiv_map_measurableEquiv",
        "IDT.QMClosure.RelativeEntropyDataProcessing.klDiv_prod_swap",
        "IDT.QMClosure.RelativeEntropyDataProcessing.klDiv_prod",
        "IDT.QMClosure.RelativeEntropyDataProcessing.klDiv_markov_le"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "These theorems concern ordinary statistical measures and channels. Physically available preparations, channels and detector events remain separate obligations.",
    "Actual affinity data processing and product multiplicativity on arbitrary measurable outcome spaces remain unformalized. The finite-KL entropy route leaves that weaker positive-affinity route open. The checked stochastic-affinity adapter covers finite outcome spaces only.",
    "Product additivity supplies no physical tensor/composite interpretation, Bell closure, actualization or identification of the original response Qraw."] }

def classicalStatisticalProcessBridge : ResearchTask := {
  id := "classical_statistical_process_bridge"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply an arbitrary raw carrier V, a chosen reference o and a total operation F with F squared equal to swap and F(x,x)=(x,x). Supply actual preparation probability measures K(x) on an arbitrary measurable space Omega, with finite KL(K(x),K(y)) for every ordered raw pair.",
    "Supply one state-independent Markov kernel T on Omega times Omega. For every raw input pair (x,y), require T applied to K(x) product K(y) to equal K(F(x,y)1) product K(F(x,y)2). This exact common-channel full-product covariance and the product-preparation family remain explicit inputs."]
  conclusions := [
    "Define delta(x,y)=KL(K(x),K(y)).toReal+KL(K(y),K(x)).toReal, the ordinary Jeffreys comparison. Actual KL data processing and product additivity derive summed pair nonexpansion. No comparison-level inequality is assumed.",
    "The resulting comparison law instantiates PairComparisonReconstruction.Contract. Its existing reconstruction gives exact pair isometry, conservation of Qnoise(x)=delta(x,o), observed mediality, the sparse marginal law and the full squared Hilbert distance delta(x,y)=norm(feature(x)-feature(y)) squared.",
    "Zero comparison is equivalent to equality of the actual preparation measures. The reconstructed feature distinguishes exactly those measures and has squared norm Qnoise(x)."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ClassicalStatisticalProcessBridge.lean"
      declarations := [
        "IDT.QMClosure.ClassicalStatisticalProcessBridge.Contract",
        "IDT.QMClosure.ClassicalStatisticalProcessBridge.Contract.comparison",
        "IDT.QMClosure.ClassicalStatisticalProcessBridge.Contract.pairEntropy",
        "IDT.QMClosure.ClassicalStatisticalProcessBridge.Contract.directed_pair_nonexpanding",
        "IDT.QMClosure.ClassicalStatisticalProcessBridge.Contract.comparison_nonexpanding",
        "IDT.QMClosure.ClassicalStatisticalProcessBridge.Contract.reconstruction",
        "IDT.QMClosure.ClassicalStatisticalProcessBridge.Contract.comparison_eq_norm_sub_sq",
        "IDT.QMClosure.ClassicalStatisticalProcessBridge.Contract.norm_feature_sq",
        "IDT.QMClosure.ClassicalStatisticalProcessBridge.Contract.comparison_eq_zero_iff",
        "IDT.QMClosure.ClassicalStatisticalProcessBridge.Contract.feature_eq_iff_preparation_eq"] }]
  plannedArtifacts := []
  dependencies := ["relative_entropy_data_processing", "pair_comparison_reconstruction"]
  limits := [
    "All ordered KL divergences are required finite so conversion to real numbers retains their ordinary meaning and excludes infinity.toReal=0. This premise is stronger than positive affinity. Jeffreys divergence is not identified with minus log affinity in general.",
    "The contract's physical origin remains open. The separate unit-variance Gaussian witness supplies a checked nontrivial model under supplied real coordinates, Gaussian preparations and the native mixer. Native iid Gaussian characterization and general-variance and affinity results retain their analytic, unformalized status.",
    "Qnoise is a newly constructed comparison readout. The original response Qraw=c*delta(-,o), its positive calibration c, detector-event realization, actualization, Born, QM closure, composites, Bell and physical scales remain open."] }

def finiteOutcomeChannelWall : ResearchTask := {
  id := "finite_outcome_channel_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply normalized nonnegative preparation rows on one fixed finite outcome space, with strictly positive actual affinity for every raw pair. The raw carrier V is arbitrary. Supply a transparent square-swap operation F.",
    "Supply one common finite stochastic channel on outcome pairs, with nonnegative normalized rows, whose output on every independent preparation K(x) product K(y) is exactly K(F(x,y)1) product K(F(x,y)2)."]
  conclusions := [
    "Actual finite affinity obeys data processing under the supplied stochastic channel and is multiplicative on independent products. These facts derive the product-affinity comparison law required by the separate negative-log reconstruction.",
    "The finite-outcome affinity rigidity theorem then forces all preparation rows to be identical. The common stochastic channel and exact product covariance establish the full comparison inequality.",
    "A separate omission control uses Dirac rows on ZMod 5 and F(x,y)=(4*x+2*y,2*x+4*y). It has normalized nonnegative laws, a deterministic common channel, square-swap, diagonal transparency and exact product covariance, yet distinct laws with zero affinity. Thus positive overlap is essential to equality of laws."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FiniteOutcomeChannelWall.lean"
      declarations := [
        "IDT.QMClosure.FiniteOutcomeChannelWall.Channel.affinity_data_processing",
        "IDT.QMClosure.FiniteOutcomeChannelWall.affinity_product",
        "IDT.QMClosure.FiniteOutcomeChannelWall.comparison_nonexpanding_of_common_channel",
        "IDT.QMClosure.FiniteOutcomeChannelWall.reconstructionOfCommonChannel",
        "IDT.QMClosure.FiniteOutcomeChannelWall.all_laws_equal_of_common_channel",
        "IDT.QMClosure.FiniteOutcomeChannelWall.ZeroOverlapControl.dirac_nonnegative",
        "IDT.QMClosure.FiniteOutcomeChannelWall.ZeroOverlapControl.dirac_normalized",
        "IDT.QMClosure.FiniteOutcomeChannelWall.ZeroOverlapControl.operation_square",
        "IDT.QMClosure.FiniteOutcomeChannelWall.ZeroOverlapControl.operation_diagonal",
        "IDT.QMClosure.FiniteOutcomeChannelWall.ZeroOverlapControl.common_channel_covariance",
        "IDT.QMClosure.FiniteOutcomeChannelWall.ZeroOverlapControl.logarithmic_comparison_zero",
        "IDT.QMClosure.FiniteOutcomeChannelWall.ZeroOverlapControl.distinct_laws",
        "IDT.QMClosure.FiniteOutcomeChannelWall.ZeroOverlapControl.zero_overlap"] }]
  plannedArtifacts := []
  dependencies := ["finite_outcome_affinity_rigidity", "classical_affinity_log_wall"]
  limits := [
    "This wall applies to one fixed finite outcome space under exact all-input product covariance and positive pairwise overlap. It assumes no finite raw carrier and establishes no exclusion for all finite measurements or approximate models.",
    "The Dirac omission control has zero totalized-log comparison even between its distinct laws. Its zero affinities receive no statistical-distance interpretation through the totalized logarithm.",
    "No physical channel availability, original-response calibration, actual detector events, Born interpretation, QM closure or physical-scale derivation follows."] }

def nativeStationaryNoiseClassification : ResearchTask := {
  id := "native_stationary_noise_classification"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For the scalar theorem supply a Borel probability measure mu on the reals satisfying charFun(mu,t)=charFun(mu,t/2)^3*conj(charFun(mu,t/2)) for every real t. No moment, density or nondegeneracy premise is supplied.",
    "For the native theorem supply the exact real two-coordinate Sample carrier and specified native real-linear mixer G. Two independently re-prepared identical probability inputs define S(mu)=(mu product mu).map(firstOutput). Require exact two-step stationarity S(S(mu))=mu; first-marginal stationarity S(mu)=mu is sufficient.",
    "For the countable-concentration corollary additionally supply a countable set S in this same real sample carrier with mu(S)=1."]
  conclusions := [
    "The scalar signed-smoothing equation implies a finite second moment and equality with gaussianReal at the law's actual mean and variance, including the zero-variance case.",
    "Native two-step stationarity implies a product of two real Gaussian laws with their actual coordinate means and one shared coordinate variance. Gaussianity, moments and coordinate independence are conclusions.",
    "A countably concentrated two-step stationary law on this explicit native carrier is the Dirac law at its actual coordinate means."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/GaussianSignedSmoothingMoments.lean"
      declarations := [
        "IDT.QMClosure.GaussianSignedSmoothingMoments.integrable_sq_of_fixedPoint",
        "IDT.QMClosure.GaussianSignedSmoothingMoments.memLp_two_of_fixedPoint"] },
    { sourcePath := "Proofs/QMClosure/GaussianSignedSmoothingCharacterization.lean"
      declarations := [
        "IDT.QMClosure.GaussianSignedSmoothingCharacterization.eq_gaussianReal_of_fixedPoint"] },
    { sourcePath := "Proofs/QMClosure/NativeStationaryNoiseCharacterization.lean"
      declarations := [
        "IDT.QMClosure.NativeStationaryNoiseCharacterization.TwoStepStationary",
        "IDT.QMClosure.NativeStationaryNoiseCharacterization.twoStepStationary_of_stationary",
        "IDT.QMClosure.NativeStationaryNoiseCharacterization.eq_product_gaussian_of_twoStepStationary",
        "IDT.QMClosure.NativeStationaryNoiseCharacterization.eq_dirac_of_twoStepStationary_countable_concentration",
        "IDT.QMClosure.NativeStationaryNoiseCharacterization.eq_product_gaussian_of_stationary"] }]
  plannedArtifacts := []
  dependencies := ["unit_variance_gaussian_statistical_witness"]
  limits := [
    "The real sample carrier, native mixer, independent input re-preparation and exact stationarity remain supplied. The theorem selects no physical coordinates, variance, noise source or primitive origin.",
    "The countable-concentration corollary concerns this supplied native real carrier and exact stationarity, not arbitrary discrete outcome models, approximate laws or all finite detectors.",
    "The separate native_marginal_stationarity_noise_origin task supplies the weaker raw-family bridge, shared family variance and its precisely conditioned finite-entropy bridge. No physical preparation origin, Qraw identification, calibration, detector selection, actualization, Born rule or QM closure follows."] }

def nativeMarginalStationarityNoiseOrigin : ResearchTask := {
  id := "native_marginal_stationarity_noise_origin"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply NativeMarginalProcessBridge.Contract D on an arbitrary raw carrier V: probability preparations on the specified real two-coordinate sample carrier, the specified native real-linear mixer G, raw operation squared equal to swap, and exact first-marginal covariance for every ordered raw pair using independent input preparations. Raw diagonal transparency, second-marginal covariance, full-product covariance, moments and finite entropy are absent from this contract.",
    "To instantiate the observed classical statistical bridge, supply a reference and finite ordered KL; equivalent family-specific conditions are positive shared variance or constant preparation measures. A non-Dirac member or absolute continuity of every preparation with respect to one reference preparation suffices."]
  conclusions := [
    "Raw square-swap and first-marginal covariance give two-step stationarity of each preparation and second-marginal covariance. Each preparation is an isotropic Gaussian at its actual coordinate mean, and all preparations have one shared coordinate variance.",
    "The actual mean map intertwines the raw operation and native mixer. Two raw labels have equal means exactly when their preparation measures agree. Full independent-output product covariance and preparation-measure diagonal transparency follow.",
    "The observed carrier is the range of actual preparation measures. Its induced operation satisfies square-swap and diagonal transparency; finite entropy gives an actual ClassicalStatisticalProcessBridge.Contract on this carrier.",
    "For each ordered pair, KL is finite exactly when shared variance is positive or the two preparation measures agree. All ordered KL divergences are finite exactly when shared variance is positive or the family is constant. Non-Dirac membership is sufficient, while a constant Dirac family is also admitted. Reference absolute continuity supplies the bridge through this family's classification.",
    "The hidden Sample times Fin 5 control has nonconstant unit-variance Gaussian preparations, finite KL and full covariance while raw diagonal transparency fails.",
    "The varying-variance control has positive input variances 1 and 3, both exact marginal laws and fixed raw diagonals, but raw square-swap and full-product covariance fail. A selected joint characteristic function is exp(-3), while the independent target gives exp(-2)."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeIsotropicGaussianFamily.lean"
      declarations := [
        "IDT.QMClosure.NativeIsotropicGaussianFamily.preparation_ext_iff",
        "IDT.QMClosure.NativeIsotropicGaussianFamily.klDiv_preparation_ne_top",
        "IDT.QMClosure.NativeIsotropicGaussianFamily.map_first_preparation_prod",
        "IDT.QMClosure.NativeIsotropicGaussianFamily.map_second_preparation_prod",
        "IDT.QMClosure.NativeIsotropicGaussianFamily.map_preparation_prod"] },
    { sourcePath := "Proofs/QMClosure/NativeMarginalProcessBridge.lean"
      declarations := [
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.twoStepStationary",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.preparation_eq_gaussian",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.secondMarginal",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.coordinateVariance_eq",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.mean_compatibility",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.mean_eq_iff_preparation_eq",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.map_preparation_prod",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.preparation_diagonal",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.observedOperation_square",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.observedOperation_transparent",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.klDiv_ne_top_iff",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.finiteEntropy_iff",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.observedContractOfFiniteEntropy",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.observedContractOfReferenceAC",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.observedContract",
        "IDT.QMClosure.NativeMarginalProcessBridge.Contract.observedContractOfConstant"] },
    { sourcePath := "Proofs/QMClosure/NativeMarginalProcessControls.lean"
      declarations := [
        "IDT.QMClosure.NativeMarginalProcessControls.hiddenMixer_square",
        "IDT.QMClosure.NativeMarginalProcessControls.hiddenPreparation_firstMarginal",
        "IDT.QMClosure.NativeMarginalProcessControls.hiddenPreparation_fullCovariance",
        "IDT.QMClosure.NativeMarginalProcessControls.hiddenPreparation_finiteKL",
        "IDT.QMClosure.NativeMarginalProcessControls.hiddenPreparation_not_dirac",
        "IDT.QMClosure.NativeMarginalProcessControls.hiddenPreparation_nonconstant",
        "IDT.QMClosure.NativeMarginalProcessControls.hiddenMixer_diagonal_moves",
        "IDT.QMClosure.NativeMarginalProcessControls.variablePreparation_firstMarginal",
        "IDT.QMClosure.NativeMarginalProcessControls.variablePreparation_secondMarginal",
        "IDT.QMClosure.NativeMarginalProcessControls.variableMixer_diagonal",
        "IDT.QMClosure.NativeMarginalProcessControls.unequalInputs_positive_variances",
        "IDT.QMClosure.NativeMarginalProcessControls.variableMixer_square_fails",
        "IDT.QMClosure.NativeMarginalProcessControls.variablePreparation_variance_differs",
        "IDT.QMClosure.NativeMarginalProcessControls.actual_joint_characteristic",
        "IDT.QMClosure.NativeMarginalProcessControls.independent_target_characteristic",
        "IDT.QMClosure.NativeMarginalProcessControls.variablePreparation_fullCovariance_fails"] }]
  plannedArtifacts := []
  dependencies := ["native_stationary_noise_classification",
    "classical_statistical_process_bridge", "unit_variance_gaussian_statistical_witness"]
  limits := [
    "Real sample coordinates, the native linear mixer, independent input preparations and exact all-pair first-marginal covariance remain supplied. Raw label diagonal transparency requires a separate condition such as preparation-map injectivity; the checked generic bridge uses the observed carrier.",
    "Distinct zero-variance Dirac preparations have infinite KL. Reference absolute continuity is sufficient here through the shared-Gaussian-family classification; this is not a general implication from absolute continuity to finite KL.",
    "Unequal-variance all-pair entropy finiteness is outside the checked control scope. Nonlinear outcome conjugation remains in the separate analytic gaussian_statistical_realization_detector_boundary frontier.",
    "No physical preparation origin, variance selection, independently given Qraw, calibration, detector selection, event actualization, Born rule or QM closure follows."] }


def nativeMarginalMeanDensity : ResearchTask := {
  id := "native_marginal_mean_density"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply NativeMarginalProcessBridge.Contract D on an arbitrary raw carrier: probability preparations on the specified real two-coordinate sample carrier, the specified native real-linear mixer G, raw operation squared equal to swap, and exact first-marginal covariance for every ordered pair using independent input preparations.",
    "Require two distinct preparation measures in the family. For the optional exact-coverage corollary additionally require the actual complex mean range to be closed in the supplied ordinary complex topology."]
  conclusions := [
    "The checked result gives a dense range of actual complex preparation means. Distinct preparations give two distinct actual means; normalize these to 0 and 1. Mean compatibility gives native mixer closure, and induction on the four evalRaw constructors puts every allocated scalar-program value in the normalized mean range. The preexisting NativeGaussianDyadicDensity.exists_program_approx then gives approximation at every positive tolerance.",
    "If the actual mean range is also closed, density implies that it is the entire complex plane. No finite-KL or non-Dirac premise is used: a nonconstant zero-variance family of Dirac preparations remains covered."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeMarginalMeanDensity.lean"
      declarations := [
        "IDT.QMClosure.NativeMarginalMeanDensity.evalRaw_mem",
        "IDT.QMClosure.NativeMarginalMeanDensity.eval_mem",
        "IDT.QMClosure.NativeMarginalMeanDensity.complexMean_eq_iff_preparation_eq",
        "IDT.QMClosure.NativeMarginalMeanDensity.complexMean_compatibility",
        "IDT.QMClosure.NativeMarginalMeanDensity.scalarProgram_mem_normalizedRange",
        "IDT.QMClosure.NativeMarginalMeanDensity.denseRange_complexMean_of_ne",
        "IDT.QMClosure.NativeMarginalMeanDensity.denseRange_complexMean",
        "IDT.QMClosure.NativeMarginalMeanDensity.surjective_complexMean_of_closed"] },
    { sourcePath := "Proofs/QMClosure/NativeGaussianDyadicDensity.lean"
      declarations := ["IDT.QMClosure.NativeGaussianDyadicDensity.exists_program_approx"] }]
  plannedArtifacts := []
  dependencies := ["native_stationary_noise_classification",
    "native_marginal_stationarity_noise_origin", "native_allocated_ball_observation"]
  limits := [
    "The mean-range membership and density results reuse the preexisting Gaussian-dyadic approximation theorem. The scalar compiler and ordinary complex topology are supplied context; this task does not rederive that prior density result.",
    "The exact real carrier, native mixer, ordinary complex topology, independent input preparation and exact first-marginal covariance remain supplied. Density alone gives no exact surjectivity, closedness, finite uniform program budget, physical preparation or resource availability.",
    "No physical variance, detector selection, Qraw identity, calibration, event actualization, Born rule or QM closure follows."] }

def countableHistoryNativeNoiseWall : ResearchTask := {
  id := "countable_history_native_noise_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply an entire history carrier H with Countable H and a measurable structure, a probability measure rho on H, and a deterministic measurable output map f into the specified real two-coordinate native sample carrier.",
    "Require exact two-step native smoothing stationarity of rho.map f, with independent re-preparation at each smoothing step. Exact first-marginal stationarity is sufficient."]
  conclusions := [
    "The pushed-forward outcome law is the Dirac measure at its actual coordinate means, by countable concentration and the checked native two-step classifier."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/CountableHistoryNativeNoiseWall.lean"
      declarations := [
        "IDT.QMClosure.CountableHistoryNativeNoiseWall.map_eq_dirac_of_twoStepStationary",
        "IDT.QMClosure.CountableHistoryNativeNoiseWall.map_eq_dirac_of_firstMarginalStationary"] }]
  plannedArtifacts := []
  dependencies := ["native_stationary_noise_classification"]
  limits := [
    "The entire H must be countable. Infinite histories over a finite alphabet can form an uncountable carrier; a finite alphabet alone does not supply this premise.",
    "The output map is deterministic and measurable, and its law is exactly stationary under the supplied native real mixer. Stochastic emission kernels, approximate stationarity and other outcome carriers lie outside this theorem.",
    "The wall does not derive a physical history model, outcome actualization, Born rule, detector selection, calibrated scale or QM closure."] }

def referenceEntropyFactorizationOrigin : ResearchTask := {
  id := "reference_entropy_factorization_origin"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply an arbitrary measurable outcome space Omega, probability preparations K(x), a probability reference alpha and one actual common Markov kernel kappa on outcome pairs preserving alpha product alpha. Require finite KL(K(x)||alpha) for every raw label. The external reference need not be among the preparations.",
    "Supply a raw operation F with F squared equal to swap and both exact output marginal covariance laws under kappa. No raw measurability, Gaussianity, coordinates, diagonal transparency, channel inverse or finite pairwise KL premise is supplied. First-marginal covariance suffices in the separate theorem with explicit sample-kernel swap symmetry."]
  conclusions := [
    "For P(p)=K(p1) product K(p2), Q(p)=kappa(P(p)) and S(p)=KL(K(p1)||alpha)+KL(K(p2)||alpha), the checked product-reference decomposition and data processing give MI(p)+S(F(p))<=S(p). Apply the inequality at F(p) and use square-swap to obtain conservation of S; finite cancellation forces MI(p)=0 and exact full-product covariance. Reference-relative data processing is an equality for every input pair.",
    "A normalized Radon-Nikodym-density construction gives a Markov disintegration of any joint probability dominated by a supplied probability product on arbitrary measurable spaces, with no StandardBorel or nonempty instance premise. The supplied second reference gives fallback rows at zero or infinite normalization. The product-reference decomposition holds unconditionally in ENNReal; faithful real conversion requires finite reference divergence.",
    "Checked omission controls give correlated outputs when reference invariance, finite reference KL or raw square-swap is omitted. The infinite-reference-KL copy control also violates absolute continuity and does not isolate integrability alone. The square-swap control preserves the fair product reference, has finite directed pairwise KL and both prescribed marginals, with output masses 5/16 on the diagonal and 3/16 off it.",
    "The Fin 5 Dirac control has an external uniform reference with finite reference KL, invariant reference product and full covariance while distinct pair KL is infinite. The unit-Gaussian control uses sample mixer -G and satisfies the reference contract and finite directed pairwise KL while its observed diagonal sends x to minus x. Changing G to -G preserves the boundary of the earlier G-specific diagonal theorem.",
    "The classicalProcess adapter supplies the existing ClassicalStatisticalProcessBridge contract only after separately choosing a raw state and supplying raw fixed diagonals and finite directed pairwise KL."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/DominatedProductDisintegration.lean"
      declarations := [
        "IDT.QMClosure.DominatedProductDisintegration.fst_withDensity_prod",
        "IDT.QMClosure.DominatedProductDisintegration.exists_markov_disintegration_of_ac"] },
    { sourcePath := "Proofs/QMClosure/ProductReferenceEntropyDecomposition.lean"
      declarations := [
        "IDT.QMClosure.ProductReferenceEntropyDecomposition.product_reference_decomposition_of_ac",
        "IDT.QMClosure.ProductReferenceEntropyDecomposition.product_reference_decomposition",
        "IDT.QMClosure.ProductReferenceEntropyDecomposition.product_reference_terms_ne_top",
        "IDT.QMClosure.ProductReferenceEntropyDecomposition.product_reference_decomposition_toReal",
        "IDT.QMClosure.ProductReferenceEntropyDecomposition.marginal_kl_sum_le",
        "IDT.QMClosure.ProductReferenceEntropyDecomposition.marginal_product_kl_eq_zero_iff"] },
    { sourcePath := "Proofs/QMClosure/ReferenceEntropyFactorization.lean"
      declarations := [
        "IDT.QMClosure.ReferenceEntropyFactorization.operation_commutes_swap",
        "IDT.QMClosure.ReferenceEntropyFactorization.channel_comp_map_swap",
        "IDT.QMClosure.ReferenceEntropyFactorization.secondMarginal_of_first",
        "IDT.QMClosure.ReferenceEntropyFactorization.Contract.entropy_budget",
        "IDT.QMClosure.ReferenceEntropyFactorization.Contract.referenceEntropy_conserved",
        "IDT.QMClosure.ReferenceEntropyFactorization.Contract.mutualInformation_eq_zero",
        "IDT.QMClosure.ReferenceEntropyFactorization.Contract.covariance",
        "IDT.QMClosure.ReferenceEntropyFactorization.Contract.reference_dpi_equality",
        "IDT.QMClosure.ReferenceEntropyFactorization.Contract.classicalProcess"] },
    { sourcePath := "Proofs/QMClosure/ReferenceEntropyFactorizationControls.lean"
      declarations := [
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.no_invariant_reference",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.no_finite_reference_entropy",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.sharedFlip_preserves_reference",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.sharedFlip_firstMarginal",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.sharedFlip_secondMarginal",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.biasedPreparation_finiteKL",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.sharedFlip_joint_probabilities",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.sharedFlip_not_product",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.collapseOperation_square_fails",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.finite_reference_not_pairwise_finite",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.negativeMixer_square",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.negativeMixer_fullCovariance",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.gaussianPreparation_finiteKL",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.negativeMixer_preserves_reference",
        "IDT.QMClosure.ReferenceEntropyFactorizationControls.negativeMixer_observed_diagonal_moves"] }]
  plannedArtifacts := []
  dependencies := ["relative_entropy_data_processing", "classical_statistical_process_bridge",
    "native_marginal_stationarity_noise_origin", "detector_conservation_closure_wall"]
  limits := [
    "The common channel is retained as the intended physical contract. Its mathematical minimality is unproved.",
    "Finite reference KL does not imply finite directed pairwise KL or mutual absolute continuity among preparations. The detector endpoint wall therefore does not follow from this contract alone.",
    "The supplied reference law, reference invariance, finite entropy, raw root-swap and marginal laws retain open physical justification. Raw fixed diagonals, a chosen raw state and finite directed pairwise KL remain separate process-adapter inputs.",
    "No detector selection, independently specified Qraw identity, physical scale, event actualization, Born interpretation, Hilbert representation, composite or dynamics closure, full QM or GR follows."] }

def detectorEndpointSupportWall : ResearchTask := {
  id := "detector_endpoint_support_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For null-event transfer supply arbitrary measures mu absolutely continuous with respect to nu and one common detector kernel. The checked proof uses Mathlib AbsolutelyContinuous.comp_right.",
    "For response classification supply a probability family whose preparation measures are mutually absolutely continuous and one common measurable effect g valued in [0,1]. Finite directed pairwise KL is sufficient. No process, conservation, square-swap or geometry premise is needed."]
  conclusions := [
    "Common-kernel output laws preserve absolute continuity, so a null output event for the dominating preparation remains null for the dominated preparation. A common bounded effect transfers zero acceptance in this direction; the complementary effect transfers acceptance one.",
    "For a mutually absolutely continuous probability family, a zero response or a one response occurs everywhere or nowhere. The response family is all zero, all one or pointwise strictly interior. The theorem supplies no uniform positive margin from either endpoint.",
    "A target assigning both zero and a nonzero value, or both one and a non-one value, cannot exactly equal this common bounded-effect response. Finite directed pairwise KL supplies the support premise. The native isotropic Gaussian specialization requires nonzero variance.",
    "Checked positive Bool controls have finite directed pairwise KL and unequal indicator responses 1/3 and 2/3. Distinct Dirac preparations give indicator responses 1 and 0 with infinite directed KL."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/DetectorEndpointSupportWall.lean"
      declarations := [
        "IDT.QMClosure.DetectorEndpointSupportWall.kernel_event_zero_of_absolutelyContinuous",
        "IDT.QMClosure.DetectorEndpointSupportWall.kernel_event_not_one_zero",
        "IDT.QMClosure.DetectorEndpointSupportWall.acceptance_zero_of_absolutelyContinuous",
        "IDT.QMClosure.DetectorEndpointSupportWall.acceptance_one_of_absolutelyContinuous",
        "IDT.QMClosure.DetectorEndpointSupportWall.acceptance_zero_iff",
        "IDT.QMClosure.DetectorEndpointSupportWall.acceptance_one_iff",
        "IDT.QMClosure.DetectorEndpointSupportWall.acceptance_trichotomy",
        "IDT.QMClosure.DetectorEndpointSupportWall.absolutelyContinuous_of_finiteEntropy",
        "IDT.QMClosure.DetectorEndpointSupportWall.acceptance_trichotomy_of_finiteEntropy",
        "IDT.QMClosure.DetectorEndpointSupportWall.process_acceptance_trichotomy",
        "IDT.QMClosure.DetectorEndpointSupportWall.no_effect_matching_zero_target",
        "IDT.QMClosure.DetectorEndpointSupportWall.no_effect_matching_one_target",
        "IDT.QMClosure.DetectorEndpointSupportWall.native_acceptance_trichotomy"] },
    { sourcePath := "Proofs/QMClosure/DetectorEndpointSupportControls.lean"
      declarations := [
        "IDT.QMClosure.DetectorEndpointSupportControls.positiveEvent_response_zero",
        "IDT.QMClosure.DetectorEndpointSupportControls.positiveEvent_response_one",
        "IDT.QMClosure.DetectorEndpointSupportControls.finiteEntropy_nonconstant_response",
        "IDT.QMClosure.DetectorEndpointSupportControls.diracEvent_response_zero",
        "IDT.QMClosure.DetectorEndpointSupportControls.diracEvent_response_one",
        "IDT.QMClosure.DetectorEndpointSupportControls.dirac_endpoint_separation"] }]
  plannedArtifacts := []
  dependencies := ["relative_entropy_data_processing", "classical_statistical_process_bridge",
    "native_marginal_stationarity_noise_origin", "invariant_effect_readout_bridge",
    "gaussian_soft_detector_boundary", "detector_conservation_closure_wall"]
  limits := [
    "The theorem allows nonconstant interior responses and supplies no uniform quantitative approximation bound. Zero-variance nonconstant native Dirac families need not satisfy its support premise.",
    "Finite reference KL to one external reference does not imply mutual absolute continuity or finite directed pairwise KL. This wall does not automatically apply to the general reference-entropy factorization contract.",
    "Any Born or QM exclusion requires a separately stipulated direct identification with the detector-event response. The wall identifies no independently supplied Qraw and supplies no detector selection, physical scale, actualization, Born interpretation, Hilbert representation, composite or dynamics closure, full QM or GR."] }

def detectorConservationClosureWall : ResearchTask := {
  id := "detector_conservation_closure_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For the universal wall supply an arbitrary measurable probability family K, a raw operation F with F squared equal to swap, and one common transport respecting equality of full product laws. At even one fixed input pair require acceptance-product conservation for every measurable effect g with values in [0,1].",
    "For the separate complementary-effect wall retain the existing ClassicalStatisticalProcessBridge.Contract, including finite ordered latent KL and common full-product Markov covariance. For one selected measurable effect g require conservation of both acceptance products for g and for 1-g at every raw input pair; equivalently require g and (1+g)/2."]
  conclusions := [
    "The universal wall forces the two input preparation measures at the selected pair to agree. The sure effect, averaging and mixed-effect orientation identify the output measure pair as the input pair or its swap; common transport around the square-swap four-cycle then collapses the pair. No finite-KL, diagonal-transparency or Gaussian premise is needed for this universal wall.",
    "The complementary-effect wall forces q(x)=integral g dK(x) to be constant. Conservation preserves the unordered response pair. Both output maps contract the reconstructed squared comparison by a factor of one half when the other input is fixed; choose a branch retaining q. A positive actual binary KL between differing responses would be bounded by DPI by geometrically vanishing latent comparison. The argument uses no Pinsker inequality, detector completeness or common record-channel premise.",
    "The no-common-transport control uses five labels and diagonal-fixed four-cycles (01,02,10,20), (03,04,30,40), (12,13,21,31), (14,23,41,32), (24,34,42,43). With K(0)=mu and K(1)=K(2)=K(3)=K(4)=nu for distinct positive Bool laws, all effect products are conserved and F squared is swap, but no common full-product transport exists.",
    "A separate finite-KL omission control uses Dirac K(x), the actual deterministic F channel, and g(0)=1/3 with g=2/3 at the other labels. Both g and its complement conserve products and both observed events have positive probabilities, while distinct latent Dirac laws have infinite KL."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/DetectorEffectOperations.lean"
      declarations := ["IDT.QMClosure.DetectorEffectOperations.measure_ext_of_acceptance_eq"] },
    { sourcePath := "Proofs/QMClosure/UniversalDetectorConservationWall.lean"
      declarations := [
        "IDT.QMClosure.UniversalDetectorConservationWall.preparations_equal_of_universal_products",
        "IDT.QMClosure.UniversalDetectorConservationWall.preparations_equal_of_common_kernel"] },
    { sourcePath := "Proofs/QMClosure/ComplementaryDetectorConservationWall.lean"
      declarations := [
        "IDT.QMClosure.ComplementaryDetectorConservationWall.acceptance_eq_of_complement",
        "IDT.QMClosure.ComplementaryDetectorConservationWall.complement_iff_average_sure",
        "IDT.QMClosure.ComplementaryDetectorConservationWall.acceptance_eq_reference_of_average_sure"] },
    { sourcePath := "Proofs/QMClosure/DetectorConservationOmissionControls.lean"
      declarations := [
        "IDT.QMClosure.DetectorConservationOmissionControls.operation_square",
        "IDT.QMClosure.DetectorConservationOmissionControls.operation_diagonal",
        "IDT.QMClosure.DetectorConservationOmissionControls.positivePreparation_kl_ne_top",
        "IDT.QMClosure.DetectorConservationOmissionControls.positivePreparation_all_products",
        "IDT.QMClosure.DetectorConservationOmissionControls.positivePreparation_no_common_transport",
        "IDT.QMClosure.DetectorConservationOmissionControls.diracPreparation_covariance",
        "IDT.QMClosure.DetectorConservationOmissionControls.selectedEffect_nonconstant",
        "IDT.QMClosure.DetectorConservationOmissionControls.selectedEffect_product",
        "IDT.QMClosure.DetectorConservationOmissionControls.selectedComplement_product",
        "IDT.QMClosure.DetectorConservationOmissionControls.diracPreparation_kl_top"] }]
  plannedArtifacts := []
  dependencies := ["classical_statistical_process_bridge",
    "invariant_effect_readout_bridge", "finite_outcome_channel_wall"]
  limits := [
    "The complementary-effect wall uses the full existing finite-KL contract; the universal wall has its separately stated weaker hypotheses. Checked omission controls isolate the common-transport and finite-KL premises.",
    "The selected pair universal conclusion does not assert equality of all family laws unless universal conservation is required at all pairs. No detector availability, physical interpretation, Qraw identity, actualization, Born rule or QM closure follows."] }

def gaussianDetectorRandomizationFront : ResearchTask := {
  id := "gaussian_detector_randomization_front"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Use the same actual unit-variance Gaussian translation family and native sample channel as the checked witness. Independently at each detector, fairly randomize between the centered effects exp(-norm(u)^2/2) and exp(-norm(u)^2). Write t=norm(mean)^2.",
    "For a separate conditional selection candidate supply measurable f, detector-coordinate factorization g(u,v)=f(u)*f(v), f(0)=1 and 0<f<=1, together with invariance under one supplied 45-degree rotation. These are additional detector assumptions.",
    "For the separate analytic response-versus-microscopic-invariance equivalence use the complete Gaussian translation family and bounded measurable effects under the native channel."]
  conclusions := [
    "Each component conserves its acceptance product, but independent fair detector randomization gives q(t)=exp(-t/4)/4+exp(-t/3)/6, whose product is not conserved. For raw input means (1,0) and native output means (A,B), input product minus output product is exactly (exp(-1/8)-exp(-1/6))^2/24>0.",
    "The randomized effect remains smooth, positive, phase-isotropic and localized with a unique centered maximum. A shared pair-level detector choice instead creates correlated settings and does not factor as the randomized effect tensor itself.",
    "Under the separate measurable factorization and supplied 45-degree rotation premises, h(x)=-log(f(x)) obeys the parallelogram equation. Measurable quadratic classification gives h(x)=c*x^2 and hence g(u,v)=exp(-c*(u^2+v^2)), c>=0. Quarter-turn invariance alone fails to select this family, as exp(-u^4-v^4) shows. Without strict positivity, f=1_{0} gives a degenerate zero-acceptance control for the actual Gaussian preparations.",
    "For complete Gaussian translations, response-product conservation is analytically equivalent to microscopic effect-product invariance almost everywhere by injectivity of Gaussian convolution. Pointwise invariance additionally needs continuity; null-set edits can preserve every response."]
  checkedEvidence := []
  plannedArtifacts := [
    "Proofs/QMClosure/GaussianParameterizedDetector.lean",
    "Proofs/QMClosure/GaussianDetectorRandomizationControls.lean",
    "Proofs/QMClosure/DetectorCoordinateModularitySelection.lean",
    "An explicit Lean obligation for Gaussian-convolution injectivity and the almost-everywhere versus continuous pointwise product-invariance equivalence."]
  dependencies := ["gaussian_soft_detector_boundary", "invariant_effect_readout_bridge"]
  limits := [
    "These randomization, conditional selection and convolution claims await formalization. The checked chosen soft detector does not provide Lean evidence for these broader results.",
    "Microscopic product invariance is not independently established from weaker detector properties. The 45-degree symmetry, its associated geometry and coordinate modularity are supplied candidate premises; the existing native quarter-turn does not select them. Physical detector selection and all supplied parameters remain open.",
    "No independently specified Qraw, physical calibration, event actualization, Born rule or QM closure follows."] }

def nativeGaussianIndependenceCharacterization : ResearchTask := {
  id := "native_gaussian_independence_characterization"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Supply iid Borel random vectors X,Y on R squared with common law mu, the fixed 90-degree rotation J, and linear maps A=(I+J)/2 and B=(I-J)/2. Require AX+BY and BX+AY to be independent. No moment, density or growth premise is used in the reviewed analytic argument."]
  conclusions := [
    "The independently reviewed analytic argument characterizes mu as N(m,sigma squared I), allowing sigma squared=0 and hence Dirac laws. Both outputs have the same marginal mu.",
    "The characteristic-function route first excludes zeros using the contracting A and B maps, fixes the continuous sign, takes a global continuous logarithm on R squared, and derives a finite-difference identity. Mollification makes the Hessian rotation-invariant and yields an isotropic quadratic plus affine logarithm. Characteristic-function symmetry and boundedness give the Gaussian form."]
  checkedEvidence := []
  plannedArtifacts := [
    "A Lean artifact for the native two-dimensional iid independence characterization, including zero exclusion, continuous logarithm, finite-difference regularization and the degenerate Gaussian case."]
  dependencies := []
  limits := [
    "This is an analytic result awaiting formalization and carries no kernel-checked evidence. It classifies one iid noise law after supplying real coordinates and the specified linear mixer.",
    "A translated preparation family, common variance across preparations, physical coordinates, a detector, the original response Qraw and physical comparison scale remain outside this characterization."] }

def gaussianStatisticalRealizationAndDetectorBoundary : ResearchTask := {
  id := "gaussian_statistical_realization_detector_boundary"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "For the residual analytic formulas supply centered isotropic Gaussian preparations K(x)=N(x,sigma squared I) on R squared with arbitrary sigma squared>0 and the native orthogonal two-port mixer. The translated family, real coordinates and shared variance are supplied.",
    "For the separate analytic detector classification supply a continuous positive effect g with g<=1 and g(0)=1, and require its product effect to be invariant under the native mixer."]
  conclusions := [
    "The separately checked native marginal family task supplies arbitrary shared-variance full-product covariance and finite KL at positive variance. Residual analytic formulas give actual affinity exp(-norm(x-y) squared/(8*sigma squared)) and Jeffreys comparison norm(x-y) squared/sigma squared. The unit-variance witness separately supplies its actual KL and Jeffreys formulas; the arbitrary-variance numerical formulas and actual affinity formula remain analytic.",
    "The analytic product-effect invariance argument gives g(z)=exp(-c*norm(z) squared), c>=0. Centered Gaussian acceptance is (1+2*c*sigma squared)^(-1)*exp(-c*norm(x) squared/(1+2*c*sigma squared)). Its normalized negative logarithm is quadratic with a free detector parameter c. The separate checked soft detector supplies the chosen case sigma squared=1 and c=1/2, leaving the general classification and formulas analytic.",
    "For a generic nonzero noise mean m, minus the log density ratio at external zero is (norm(m+x) squared-norm(m) squared)/(2*sigma squared). Radial identification requires centering or evaluation at the baseline center. Nonlinear coordinate conjugation preserves the native construction in the conjugated coordinates without selecting an external norm."]
  checkedEvidence := []
  plannedArtifacts := [
    "Lean artifacts for arbitrary-positive-variance numerical entropy formulas and the actual affinity formula.",
    "Lean artifacts for continuous positive product-effect classification, arbitrary detector parameter and explicit centering and coordinate-conjugation statements."]
  dependencies := ["classical_statistical_process_bridge",
    "native_marginal_stationarity_noise_origin",
    "native_gaussian_independence_characterization"]
  limits := [
    "This entry retains the residual analytic claims and carries no kernel-checked evidence. The separately checked general-variance family, unit-variance numerical witness and chosen soft-detector case do not upgrade the residual arbitrary-variance numerical entropy, affinity or detector-classification claims.",
    "A density value at a point depends on the chosen density version, and a Gaussian singleton has zero probability. Point-density evaluation supplies no finite detector event.",
    "The detector invariance law and a physical readout identity are additional premises. No independently given Qraw is identified, and no calibrated scale, actualization, Born, composites, Bell or QM closure follows."] }

def unitVarianceGaussianStatisticalWitness : ResearchTask := {
  id := "unit_variance_gaussian_statistical_witness"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply complex mean coordinates x and the actual product preparation gaussianReal(x.re,1) product gaussianReal(x.im,1) on R times R. Each real coordinate has variance one.",
    "Supply the existing native linear transparent square-swap mixer and its deterministic sample map G on pairs of samples."]
  conclusions := [
    "For every ordered pair x,y, actual KL is normSq(x-y)/2 and is finite. Actual Jeffreys comparison is normSq(x-y). Distinct means give distinct preparation measures.",
    "One deterministic Markov kernel induced by G maps every full independent preparation product exactly to the product at the native mixed means. All ClassicalStatisticalProcessBridge.Contract fields are instantiated in model.",
    "The instantiated comparison is normSq(x-y), and its reconstructed feature at mean one is nonzero. The contract therefore has a checked nontrivial statistical consistency witness."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/GaussianLocationEntropy.lean"
      declarations := [
        "IDT.QMClosure.GaussianLocationEntropy.klDiv_preparation",
        "IDT.QMClosure.GaussianLocationEntropy.klDiv_preparation_ne_top",
        "IDT.QMClosure.GaussianLocationEntropy.jeffreys_preparation",
        "IDT.QMClosure.GaussianLocationEntropy.preparation_zero_ne_one"] },
    { sourcePath := "Proofs/QMClosure/NativeGaussianStatisticalProcess.lean"
      declarations := [
        "IDT.QMClosure.NativeGaussianStatisticalProcess.coordinateEnergy_G",
        "IDT.QMClosure.NativeGaussianStatisticalProcess.map_preparation_prod",
        "IDT.QMClosure.NativeGaussianStatisticalProcess.channel_covariance",
        "IDT.QMClosure.NativeGaussianStatisticalProcess.model",
        "IDT.QMClosure.NativeGaussianStatisticalProcess.model_comparison",
        "IDT.QMClosure.NativeGaussianStatisticalProcess.preparation_injective",
        "IDT.QMClosure.NativeGaussianStatisticalProcess.feature_one_ne_zero"] }]
  plannedArtifacts := []
  dependencies := ["classical_statistical_process_bridge"]
  limits := [
    "The coordinates, Gaussian location family, unit variance and mixer are supplied mathematical inputs. Their physical origin remains open.",
    "This witness does not prove Gaussian independence characterization, the arbitrary-variance family or actual affinity formula. It identifies no independently given Qraw and derives no physical scale, actualization, Born, composites, Bell or QM closure."] }

def invariantEffectReadoutBridge : ResearchTask := {
  id := "invariant_effect_readout_bridge"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply probability preparations on a measurable space, a measurable effect with values in [0,1], and one Markov channel with exact full-product covariance under a supplied raw operation.",
    "Supply dual invariance of the product effect under the channel. For normalized logarithmic weights require positive acceptance at every preparation and a chosen reference. Nonnegative weight additionally requires reference acceptance maximality."]
  conclusions := [
    "The effect defines an actual binary Markov detector. Its true-event probability is the integral acceptance q, and its false-event probability is 1-q.",
    "Full-product covariance and dual product-effect invariance derive conservation of q on pairs as a product. Positivity then derives pair-sum conservation of W(x)=-log(q(x)/q(reference)); W(reference)=0. Maximal reference acceptance gives W>=0."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/InvariantEffectReadoutBridge.lean"
      declarations := [
        "IDT.QMClosure.InvariantEffectReadoutBridge.Effect.binaryKernel",
        "IDT.QMClosure.InvariantEffectReadoutBridge.Effect.binaryKernel_comp_true",
        "IDT.QMClosure.InvariantEffectReadoutBridge.Effect.binaryKernel_comp_false",
        "IDT.QMClosure.InvariantEffectReadoutBridge.Contract.response_event",
        "IDT.QMClosure.InvariantEffectReadoutBridge.Contract.response_product",
        "IDT.QMClosure.InvariantEffectReadoutBridge.Contract.weight_reference",
        "IDT.QMClosure.InvariantEffectReadoutBridge.Contract.weight_nonnegative",
        "IDT.QMClosure.InvariantEffectReadoutBridge.Contract.weight_pair_conserved"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "The invariant effect and full-product channel covariance are explicit inputs. Their physical availability and selection remain open.",
    "The constructed normalized logarithmic weight identifies no independently specified Qraw. The bridge derives no event actualization, Born rule, composite interpretation, Bell closure or physical scale."] }

def gaussianSoftDetectorBoundary : ResearchTask := {
  id := "gaussian_soft_detector_boundary"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the checked unit-coordinate-variance Gaussian location family, its native deterministic full-product channel and the chosen effect g(u)=exp(-(u1 squared+u2 squared)/2). Choose mean zero as the reference."]
  conclusions := [
    "The chosen effect is measurable, positive and bounded by one. Its product is invariant under the native sample map. Actual binary-event acceptance is q(z)=exp(-normSq(z)/4)/2, with q(0)=1/2 and 0<q(z)<=q(0).",
    "The normalized logarithmic detector weight is W(z)=-log(q(z)/q(0))=normSq(z)/4. The general bridge derives response-product and weight-pair conservation under the native mixer.",
    "The actual finite detector-product rows for input probes (1,1) and (1,i) are equal, while their required native output rows differ. No single finite stochastic channel transports even those two detector-product rows to their required output products. Consequently no all-input common finite product channel exists for these detector rows, despite conserved selected acceptance products."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/GaussianSoftDetectorBoundary.lean"
      declarations := [
        "IDT.QMClosure.GaussianSoftDetectorBoundary.softEffect",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.q_formula",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.q_actual_event",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.rejection_actual_event",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.soft_product_invariant",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.detectorModel",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.q_product_conserved",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.W_formula",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.W_pair_conserved",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.eventRow_actual",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.input_jointRows_equal",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.output_jointRows_ne",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.selected_true_products_equal",
        "IDT.QMClosure.GaussianSoftDetectorBoundary.no_single_binary_record_channel"] }]
  plannedArtifacts := []
  dependencies := ["unit_variance_gaussian_statistical_witness",
    "invariant_effect_readout_bridge", "finite_outcome_channel_wall"]
  limits := [
    "The particular effect and unit variance are supplied. The arbitrary-variance and arbitrary-effect classification remains analytic and unformalized.",
    "The obstruction concerns this fixed binary detector and exact common product-channel transport. It excludes no approximate detector transport or all finite measurements.",
    "These are ordinary statistical preparations and events. The result identifies no independently given Qraw, derives no physical scale or event actualization and does not close Born, composites, Bell or QM."] }

def rawPlanePhaseProcessComparisonControl : ResearchTask := {
  id := "raw_plane_phase_process_comparison_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the supplied actual lambda-one plane-phase operation, its existing response G, Q(x,y)=G(x,x)+G(y,y)-2*G(x,y), and midpoint mid from raw_plane_phase_local_midpoint_control. Let quarter(x)=i*x, attenuate(x)=b*x and comparison(p,q)=Q(p1,q1)+Q(p2,q2).",
    "Retain the existing selected preparations fourX, fourY, fourZ and real scale(r,x)=r*x. The supplied operation has the existing complete scalar-weight conservation property."]
  conclusions := [
    "The actual comparison Q is symmetric and common complex scaling multiplies it by normSq(c). Quarter-turn preserves Q, attenuation divides Q by two, the reference operation sends (z,quarter(z)) to ((1+i)*z,0), and attenuation of its first output returns z. The midpoint calibration is the actual preparation identity.",
    "The unused output residual is exactly Q(x,y)/2. On inputs (x,quarter(y)) and (z,quarter(z)), comparison input equals Q(z,x)+Q(z,y) and output equals 2*Q(z,mid(x,y))+Q(x,y)/2.",
    "On the selected scaled orbit, input comparison is 4*t^2+2*e^2-(8/5)*t*e, output comparison is 4*t^2+2*e^2-2*t*e, and output minus input is exactly -(2/5)*t*e.",
    "At e=1/5,t=-1 the exact comparison grows from 22/5 to 112/25. PairComparisonNonexpanding Q operation therefore fails despite the existing scalar-weight conservation law. At the fixed selected reference t=-1 the comparison defect is strictly positive for every e>0.",
    "For the selected balanced reference t=-e and any nonzero e, weak squared Jensen has positive slack while the process comparison increases. This selected passing Jensen orbit does not provide the all-input comparison law."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawPlanePhaseProcessComparisonControl.lean"
      declarations := [
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.Q",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.quarter",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.attenuate",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.comparison",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.Q_symmetric",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.G_complex_smul",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.Q_complex_smul",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.quarter_comparison",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.attenuate_comparison",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.operation_reference",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.reference_calibration",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.midpoint_calibration",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.Q_zero",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.Q_response",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.residual_comparison",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.comparison_input",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.comparison_output",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.comparison_defect",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.selected_endpoint_comparison",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.selected_input_exact",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.selected_defect_exact",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.selected_output_exact",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.rational_witness",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.not_pairComparisonNonexpanding",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.fixed_reference_defect_positive",
        "IDT.QMClosure.RawPlanePhaseProcessComparisonControl.balanced_pass_with_comparison_increase" ] }]
  plannedArtifacts := []
  dependencies := ["raw_process_comparison_bridge", "raw_plane_phase_local_midpoint_control", "raw_plane_phase_gram_control"]
  limits := [
    "The orbit formulas concern only the displayed endpoint pair and selected reference orbit. No all-triple balanced Jensen statement is recorded.",
    "The argument uses the actual response-defined nonnegative comparison. A triangle metric, global bilinear Gram representation or physical comparison interpretation is outside its premises.",
    "The block comparison sums two raw pair-port comparisons. Its operational port additivity and independent-reference availability remain open origin obligations, with no tensor/composite or Bell closure implied.",
    "No physical primitive origin, actualization, Born interpretation, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def rawClassicalProcessEnvelopeOmissionRoute : ResearchTask := {
  id := "raw_classical_process_envelope_omission_route"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For any supplied carrier V use rational finite-support probability distributions FinDist V, Dirac preparations, Markov bind, pushforward, independent product, marginals and rational mixtures. V may be infinite. Each distribution and each Markov row has finite support.",
    "Use TV(mu,nu)=(1/2)*sum_v abs(mu(v)-nu(v)). Raw deterministic gates act by pushforward on distributions over their raw wire tuples. For any supplied real response Q define Qbar(mu,nu)=sum_(x,y) mu(x)*nu(y)*Q(x,y), with rational coefficients cast to real numbers. The gate-isometry specialization assumes the raw square-swap identity."]
  conclusions := [
    "Markov bind is associative and respects mixtures. Disjoint local Markov operations commute on arbitrary correlated joint inputs and preserve untouched marginals. TV obeys Markov data processing and is exactly invariant under adjoining a common independent distribution reference. A supplied square-swap gate acts as a TV isometry.",
    "Dirac is injective. Equality Dirac(m)=(Dirac(x)+Dirac(y))/2 forces x=y=m. Classical mixing therefore cannot supply the selected distinct coherent pure midpoint.",
    "Qbar agrees with the original Q on Dirac inputs. On the actual plane control, the selected pure midpoint comparison defect is exactly 1/10 and remains strictly positive after Dirac embedding.",
    "The TV process laws and the Qbar obstruction concern different comparisons. This establishes a nonidentification and origin gap for the raw response comparison, with no countermodel to an explicitly supplied data-processing contract for that same Q."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RationalFiniteDistribution.lean"
      declarations := [
        "IDT.QMClosure.RationalFiniteDistribution.bind_bind",
        "IDT.QMClosure.RationalFiniteDistribution.bind_mixture",
        "IDT.QMClosure.RationalFiniteDistribution.disjoint_local_commute",
        "IDT.QMClosure.RationalFiniteDistribution.remote_marginal_left",
        "IDT.QMClosure.RationalFiniteDistribution.remote_marginal_right",
        "IDT.QMClosure.RationalFiniteDistribution.tv_bind_le",
        "IDT.QMClosure.RationalFiniteDistribution.tv_product_right",
        "IDT.QMClosure.RationalFiniteDistribution.dirac_injective",
        "IDT.QMClosure.RationalFiniteDistribution.half_mixture_dirac"] },
    { sourcePath := "Proofs/QMClosure/RawClassicalProcessEnvelope.lean"
      declarations := [
        "IDT.QMClosure.RawClassicalProcessEnvelope.tv_map_eq_of_leftInverse",
        "IDT.QMClosure.RawClassicalProcessEnvelope.gate_fourfold",
        "IDT.QMClosure.RawClassicalProcessEnvelope.gate_pushforward_tv",
        "IDT.QMClosure.RawClassicalProcessEnvelope.Qbar_dirac",
        "IDT.QMClosure.RawClassicalProcessEnvelope.pure_midpoint_mixture_wall",
        "IDT.QMClosure.RawClassicalProcessEnvelope.plane_Qbar_midpoint_defect",
        "IDT.QMClosure.RawClassicalProcessEnvelope.plane_Qbar_midpoint_violation",
        "IDT.QMClosure.RawClassicalProcessEnvelope.plane_midpoint_not_classical_mixture"] }]
  plannedArtifacts := []
  dependencies := ["raw_process_comparison_bridge", "raw_plane_phase_process_comparison_control"]
  limits := [
    "TV is a classical comparison on the supplied distributions. No identification with the original response Q or physical outcome probabilities is established, and no Qbar data-processing inequality is asserted.",
    "The completion has a classical joint carrier. It supplies no Bell or non-hidden-joint closure. Dirac embedding supplies no continuous embedding of the original pure-preparation topology.",
    "Independent product-distribution references do not derive the calibrated coherent reference, pair-port comparison additivity or overlapping exchange required by the separate raw process route. Existing raw calibration identities remain supplied.",
    "No physical primitive origin, actualization, Born interpretation, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def rawPowerLossReadoutControl : ResearchTask := {
  id := "raw_power_loss_readout_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply any finite complex array x and natural k>=1. Set e_i=normSq(x_i), E=sum_i e_i, exposure E^k, port_i=e_i^k/E^k and global residual=1-sum_i port_i. Option outcomes assign some i to port_i and none to the residual, using the totalized division convention at E=0.",
    "Use the existing supplied native complex circuit grammar and mixer. Their conserved quadratic energy E supplies a common exposure. The general residual identity separately assumes fixed B>0 and the same outside-port normalization S before and after a process."]
  conclusions := [
    "All Option outcomes are nonnegative, normalized and at most one. On a zero-energy array every port is zero and the residual is one. Equal prepared arrays have equal readouts, output permutations fix none, and arbitrary finite vacuum padding preserves all old ports and the residual while assigning zero to new ports.",
    "Every native circuit preserves E and exposure. A pair gate preserves the unconditional probability of each untouched wire. Nonzero basis inputs are calibrated, and all ports use the common fixed-exposure response. The corresponding prepared native circuit statements are checked.",
    "At fixed B>0 and unchanged outside contribution S, the two normalization equations imply Wout-Win=B*(Lin-Lout), hence pair-weight conservation iff the global residual is invariant.",
    "For the actual native balanced split, the residual changes from zero to 1-2*(1/2)^k and is invariant iff k=1 within this power family. Every k>1 fails pair-weight conservation on that split.",
    "On the actual three-wire witness the untouched port has unconditional probability (1/2)^k both before and after. Conditioning on any port record changes its probability from 1/2 to 2^k/(2^k+2), with unequal values for every k>1. At k=2 this reproduces the existing 1/2 versus 2/3 control."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawPowerLossReadoutControl.lean"
      declarations := [
        "IDT.QMClosure.RawPowerLossReadoutControl.probability_nonneg",
        "IDT.QMClosure.RawPowerLossReadoutControl.probability_sum_all_outcomes",
        "IDT.QMClosure.RawPowerLossReadoutControl.probability_le_one",
        "IDT.QMClosure.RawPowerLossReadoutControl.zero_energy_port",
        "IDT.QMClosure.RawPowerLossReadoutControl.zero_energy_residual",
        "IDT.QMClosure.RawPowerLossReadoutControl.common_local_response",
        "IDT.QMClosure.RawPowerLossReadoutControl.prepared_array_consistency",
        "IDT.QMClosure.RawPowerLossReadoutControl.probability_permutation",
        "IDT.QMClosure.RawPowerLossReadoutControl.port_padding_old",
        "IDT.QMClosure.RawPowerLossReadoutControl.port_padding_new",
        "IDT.QMClosure.RawPowerLossReadoutControl.residual_padding",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_energy",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_exposure",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_spectator_port",
        "IDT.QMClosure.RawPowerLossReadoutControl.circuit_prepared_consistency",
        "IDT.QMClosure.RawPowerLossReadoutControl.circuit_output_permutation",
        "IDT.QMClosure.RawPowerLossReadoutControl.circuit_spectator",
        "IDT.QMClosure.RawPowerLossReadoutControl.circuit_vacuum_old",
        "IDT.QMClosure.RawPowerLossReadoutControl.circuit_vacuum_new",
        "IDT.QMClosure.RawPowerLossReadoutControl.circuit_vacuum_residual",
        "IDT.QMClosure.RawPowerLossReadoutControl.basis_calibration",
        "IDT.QMClosure.RawPowerLossReadoutControl.residual_defect",
        "IDT.QMClosure.RawPowerLossReadoutControl.conservation_iff_residual_invariant",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_split_residual_after",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_split_residual_invariant_iff",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_pair_not_conserved",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_spectator_unconditional_invariant",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_spectator_port_before",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_spectator_port_after",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_click_conditional_before",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_click_conditional_after",
        "IDT.QMClosure.RawPowerLossReadoutControl.native_click_conditioning_changes_spectator",
        "IDT.QMClosure.RawPowerLossReadoutControl.quartic_click_conditional_matches_existing",
        "IDT.QMClosure.RawPowerLossReadoutControl.quartic_response_matches_existing"] }]
  plannedArtifacts := []
  dependencies := ["native_vacuum_probability_family", "native_contextual_probability_control"]
  limits := [
    "The none outcome is one global no-port-record event. It supplies no additional circuit spectator wire, and unconditional spectator locality imposes no invariance of that global residual.",
    "For k>1 the Option-valued family has a nonzero residual on split inputs and does not satisfy the earlier port-only normalized Law. The k=1 selection here is restricted to this supplied power family and this split, with no uniqueness theorem for arbitrary readouts.",
    "The complex carrier, native geometry and conserved quadratic exposure are supplied countermodel resources. The elementary fixed-exposure residual identity supplies accounting; its use does not derive those resources from IDT primitives.",
    "These real readouts on arbitrary complex arrays are separate from the rational finite-distribution envelope. No combination on a common probability carrier is established without additional restrictions.",
    "Physical detector availability, exhaustive event interpretation, residual invariance and continuity at the vacuum remain open. No actualization, Bell, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def boundedComparisonReferenceWall : ResearchTask := {
  id := "bounded_comparison_reference_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For finite depth N supply a real sequence f, real c>=0, real error epsilon, terminal bound f(N)<=M and recurrence f(n)<=c*f(n+1)+epsilon for n<N. The infinite recurrence additionally assumes c<1 and one upper bound M uniform over every n. Epsilon and M may be signed.",
    "For comparisons D and a total reference map R on one carrier, the upper bound may depend on the input pair but must be uniform along its full R-iterate orbit. The exact collapse specialization assumes nonnegative D, attenuation D(Bx,By)=D(x,y)/2 and total calibration B(Rx)=x. The approximate specialization supplies errors directly in comparison units."]
  conclusions := [
    "Finite depth gives f(0)<=c^N*M+epsilon*sum_(j<N)c^j. At c=1/2 this is 2^(-N)*M+2*epsilon*(1-2^(-N)). The infinite uniformly bounded recurrence gives f(0)<=epsilon/(1-c), hence f(0)<=2*epsilon for half attenuation.",
    "A per-pair orbit-uniform bound and D(x,y)<=D(Rx,Ry)/2+epsilon imply D(x,y)<=2*epsilon. With attenuation error epsilon and comparison-level calibration error abs(D(BRx,BRy)-D(x,y))<=eta, the bound is D(x,y)<=2*(epsilon+eta).",
    "Nonnegative D, exact half attenuation, a total reference right inverse and per-pair orbit-uniform upper bounds force D=0. A global upper bound is a sufficient special case. The process-reference adapter takes R(z)=(F(z,Jz)).first under a global comparison bound, without a metric, reversibility, nonexpansion or additive-port premise.",
    "For epsilon>=0, the bounded Bool comparison with values zero and 2*epsilon attains the robust half-attenuation error ceiling. A finite sharp chain has terminal value M and initial value 2^(-N)*M. For M>=0 it stays in [0,M]. Its exact step law is asserted only for n<N, so it supplies no infinite calibrated reference orbit.",
    "Real-cast TV on rational FinDist is between zero and one, and distinct Dirac preparations have TV one. On the entire FinDist carrier of a nontrivial V, exact TV half attenuation is incompatible with any total reference right inverse."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/BoundedComparisonReferenceWall.lean"
      declarations := [
        "IDT.QMClosure.BoundedComparisonReferenceWall.finite_recurrence_bound",
        "IDT.QMClosure.BoundedComparisonReferenceWall.finite_half_recurrence_bound",
        "IDT.QMClosure.BoundedComparisonReferenceWall.bounded_recurrence_bound",
        "IDT.QMClosure.BoundedComparisonReferenceWall.bounded_half_recurrence_bound",
        "IDT.QMClosure.BoundedComparisonReferenceWall.comparison_le_twice_error_of_orbit_bound",
        "IDT.QMClosure.BoundedComparisonReferenceWall.comparison_le_twice_combined_error",
        "IDT.QMClosure.BoundedComparisonReferenceWall.comparison_eq_zero_of_exact_half_reference",
        "IDT.QMClosure.BoundedComparisonReferenceWall.comparison_eq_zero_of_global_bound",
        "IDT.QMClosure.BoundedComparisonReferenceWall.process_reference_comparison_eq_zero",
        "IDT.QMClosure.BoundedComparisonReferenceWall.twoPointComparison_bounded",
        "IDT.QMClosure.BoundedComparisonReferenceWall.twoPointComparison_half_error",
        "IDT.QMClosure.BoundedComparisonReferenceWall.twoPointComparison_attains_error_ceiling",
        "IDT.QMClosure.BoundedComparisonReferenceWall.finiteSharpChain_step",
        "IDT.QMClosure.BoundedComparisonReferenceWall.finiteSharpChain_admissible",
        "IDT.QMClosure.BoundedComparisonReferenceWall.finiteSharpChain_attainment",
        "IDT.QMClosure.BoundedComparisonReferenceWall.real_tv_bounds",
        "IDT.QMClosure.BoundedComparisonReferenceWall.real_tv_dirac_of_ne",
        "IDT.QMClosure.BoundedComparisonReferenceWall.no_total_tv_half_reference"] }]
  plannedArtifacts := []
  dependencies := ["raw_process_comparison_bridge", "raw_classical_process_envelope_omission_route"]
  limits := [
    "A finite bound at each separate iteration is insufficient. One upper bound must hold along the complete orbit for each fixed pair. Finite-depth estimates retain the terminal term and do not imply exact collapse.",
    "All maps in the total-reference theorem act on one carrier. Changing resource budgets or moving between resource-indexed carriers does not establish its fixed-carrier hypotheses.",
    "Pointwise preparation closeness alone supplies no comparison calibration error. Exact and approximate comparison laws, reference availability and resource bounds remain supplied mathematical hypotheses.",
    "The TV incompatibility concerns exact total calibration on the entire normalized distribution carrier. It supplies no exclusion of restricted preparation domains or of the separate unbounded raw response comparison.",
    "No physical primitive origin, actualization, Born interpretation, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def classicalMarginalComparisonWall : ResearchTask := {
  id := "classical_marginal_comparison_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the existing native complex mixer and rational finite-support probability distributions. Compare distinct raw values by TV of their Dirac preparations, and form the pair comparison by adding its two port comparisons. The squared variant squares each single-port Dirac TV before adding.",
    "For the mixture identities supply rational t in [0,1] and a common distribution rho. The flagged control uses the supplied Bool plus Unit disjoint carrier with ordinary probability weights."]
  conclusions := [
    "On the actual input pairs (1,0) and (0,0), the summed single-port Dirac TV changes from one to two under the native mixer. The summed squared single-port Dirac TV also changes from one to two. Each comparison fails the existing PairComparisonNonexpanding contract.",
    "TV on distributions over the whole pair is preserved by the native mixer for all supplied distributions. On the same selected Dirac witness its value is one before and after. Whole-pair TV and the sum of marginal comparisons therefore obey different process laws.",
    "TV(t*mu+(1-t)*rho,t*nu+(1-t)*rho)=t*TV(mu,nu), and squaring gives the factor t squared. On the actual flagged control squared TV is 1/4 while the ordinary probability-weighted sum of squared component comparisons is 1/2."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ClassicalMarginalComparisonWall.lean"
      declarations := [
        "IDT.QMClosure.ClassicalMarginalComparisonWall.marginal_tv_before",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.marginal_tv_after",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.marginal_tv_not_nonexpanding",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.squared_marginal_tv_before",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.squared_marginal_tv_after",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.squared_marginal_tv_not_nonexpanding",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.joint_tv_preserved",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.joint_tv_before",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.joint_tv_after",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.tv_shared_mixture",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.squared_tv_shared_mixture",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.flagged_squared_tv",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.flag_weighted_squared_comparison",
        "IDT.QMClosure.ClassicalMarginalComparisonWall.squared_tv_fails_ordinary_flagged_additivity"] }]
  plannedArtifacts := []
  dependencies := ["raw_classical_process_envelope_omission_route", "raw_process_comparison_bridge"]
  limits := [
    "These controls concern the displayed classical TV comparisons. They exclude neither all quadratic comparisons nor a separately supplied data-processing contract for the original response Q.",
    "The Dirac witnesses use the supplied complex native mixer. Its physical origin and identification of a comparison with physical detector response remain open.",
    "No actualization, Bell, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def vacuumSupportEffectBoundary : ResearchTask := {
  id := "vacuum_support_effect_boundary"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For a partially ordered effect carrier supply an order automorphism preserving the vacuum-certain subset. The detector-invariance theorem additionally supplies evaluation covariance, a vacuum-fixed state process and identification of the chosen detector effect with the least vacuum-certain effect.",
    "The full-effect control supplies every function from states to [0,1], pointwise order, evaluation and pullbacks by state equivalences. Its complex-array specialization uses the existing finite-array power residuals and the actual native three-wire split."]
  conclusions := [
    "An order automorphism preserving a subset fixes its least element. Under the supplied covariance and detector-identification hypotheses the selected detector's residual evaluation is invariant.",
    "The full function effect space has a least vacuum-certain effect, the exact-vacuum indicator. Every state-equivalence pullback is an order automorphism, and every vacuum-fixed equivalence preserves vacuum certainty and fixes that indicator.",
    "Every supplied power residual with k>=1 is a vacuum-certain effect. For all finite complex arrays the k=1 residual equals the vacuum indicator. On Fin 3 arrays the power residual is the least vacuum-certain effect exactly when k=1.",
    "The actual native split has fourth iterate identity and defines a vacuum-fixed state equivalence. For every k>1 its pullback changes the chosen power residual although the full effect space has a least vacuum-certain effect, the pullback preserves vacuum certainty and evaluation is covariant."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/VacuumSupportEffectBoundary.lean"
      declarations := [
        "IDT.QMClosure.VacuumSupportEffectBoundary.least_fixed",
        "IDT.QMClosure.VacuumSupportEffectBoundary.identified_detector_invariant",
        "IDT.QMClosure.VacuumSupportEffectBoundary.pullback_covariance",
        "IDT.QMClosure.VacuumSupportEffectBoundary.pullback_preserves_vacuum_certainty",
        "IDT.QMClosure.VacuumSupportEffectBoundary.vacuumIndicator_least",
        "IDT.QMClosure.VacuumSupportEffectBoundary.pullback_fixes_vacuumIndicator",
        "IDT.QMClosure.VacuumSupportEffectBoundary.residualEffect_vacuum_certain",
        "IDT.QMClosure.VacuumSupportEffectBoundary.residual_one_eq_indicator",
        "IDT.QMClosure.VacuumSupportEffectBoundary.residualEffect_least_iff",
        "IDT.QMClosure.VacuumSupportEffectBoundary.native_split_fourth",
        "IDT.QMClosure.VacuumSupportEffectBoundary.nativeSplitEquiv_vacuum",
        "IDT.QMClosure.VacuumSupportEffectBoundary.native_pullback_changes_residual",
        "IDT.QMClosure.VacuumSupportEffectBoundary.native_full_effect_countercontrol"] }]
  plannedArtifacts := []
  dependencies := ["raw_power_loss_readout_control"]
  limits := [
    "Existence of a least vacuum-certain effect and covariance alone do not identify the actual chosen detector with that effect. The native countercontrol keeps the former properties while changing a different vacuum-certain residual.",
    "The full function space includes discontinuous state tests. Availability of its effects and identification of a physical detector remain open, as do the origins of the supplied complex carrier and quadratic energy.",
    "The k=1 leastness result is restricted to this supplied power family. It gives no uniqueness theorem for arbitrary readouts.",
    "No actualization, Bell, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def finiteCovariantNoiseWall : ResearchTask := {
  id := "finite_covariant_noise_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For the common-twins theorem supply a finite nontrivial carrier V, a gate F with F squared equal to swap and any family of real-valued functions whose pair sums are conserved by F. The multiplicative specialization supplies a strictly positive family with conserved pair products.",
    "For kernel rigidity additionally supply a strictly positive real matrix K with each row summing to one, diagonal transparency of F and full product covariance K(F(x,y).first,F(a,b).first)*K(F(x,y).second,F(a,b).second)=K(x,a)*K(y,b) for every input pair and output pair."]
  conclusions := [
    "Every supplied additively conserved family has distinct x and y agreeing on every member of that family. This core conclusion requires neither positivity nor normalization nor diagonal transparency. Applying it to logarithms gives common twins for strictly positive multiplicatively conserved families, without normalization.",
    "Normalized full product covariance respects equality of rows and descends the gate to the row-equivalence quotient. Under all kernel-rigidity hypotheses every row of K is identical.",
    "The identity kernel has normalized, injectively distinguished rows and full covariance under every injective gate. On a nontrivial carrier it has zero entries, exhibiting the boundary of the strict-positivity hypothesis."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FiniteCovariantNoiseWall.lean"
      declarations := [
        "IDT.QMClosure.FiniteCovariantNoiseWall.no_injective_ordered_conserved",
        "IDT.QMClosure.FiniteCovariantNoiseWall.conserved_family_has_twins",
        "IDT.QMClosure.FiniteCovariantNoiseWall.positive_product_family_has_twins",
        "IDT.QMClosure.FiniteCovariantNoiseWall.covariance_respects_equal_rows",
        "IDT.QMClosure.FiniteCovariantNoiseWall.strictly_positive_covariant_kernel_constant_rows",
        "IDT.QMClosure.FiniteCovariantNoiseWall.identity_kernel_normalized",
        "IDT.QMClosure.FiniteCovariantNoiseWall.identity_kernel_injective",
        "IDT.QMClosure.FiniteCovariantNoiseWall.identity_kernel_covariant",
        "IDT.QMClosure.FiniteCovariantNoiseWall.identity_kernel_has_zero"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "Common twins are equal only for the supplied conserved family. Full physical observational equivalence is a separate obligation.",
    "Kernel rigidity gives identical rows, without a uniform-row conclusion. Its proof uses full product covariance for arbitrary inputs and outputs; diagonal-input invariance alone does not supply the row-quotient argument.",
    "The theorem concerns finite carriers and exact covariance. It supplies no continuum exclusion or physical origin of a noise carrier, strict positivity, normalization or covariance.",
    "No actualization, Bell, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def binaryNoiseMixingWall : ResearchTask := {
  id := "binary_noise_mixing_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply any carrier V, a gate F with F squared equal to swap and F(x,x)=(x,x), and distinct a,b in V. For rational p in [0,1] let mu=p*Dirac(a)+(1-p)*Dirac(b), using rational finite-support distributions and their independent product.",
    "The nonproduct conclusion additionally assumes 0<p<1 and quantifies over arbitrary, possibly unequal, rational finite-support probability distributions nu and rho on V."]
  conclusions := [
    "The image of each off-diagonal binary input lies outside {a,b} squared.",
    "TV(F_*(mu product mu),mu product mu)=2*p*(1-p), including the endpoint cases. At p=1/2 this value is exactly 1/2.",
    "For 0<p<1 the output differs from every product nu product rho. The output retains positive diagonal coefficients p squared and (1-p) squared while its cross coefficient at (a,b) is zero."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/BinaryNoiseMixingWall.lean"
      declarations := [
        "IDT.QMClosure.BinaryNoiseMixingWall.mixed_output_outside_binary",
        "IDT.QMClosure.BinaryNoiseMixingWall.binary_noise_tv_exact",
        "IDT.QMClosure.BinaryNoiseMixingWall.balanced_binary_noise_tv",
        "IDT.QMClosure.BinaryNoiseMixingWall.binary_noise_not_product"] }]
  plannedArtifacts := []
  dependencies := ["raw_classical_process_envelope_omission_route", "finite_covariant_noise_wall"]
  limits := [
    "The carrier may be infinite, while every probability distribution in the statement has rational finite support. The nonproduct theorem has no assertion about all unrestricted real probability laws.",
    "This is a classical independent-noise test on a supplied binary distribution and gate. It supplies no coherent-amplitude comparison, universal Gaussian-noise exclusion or physical noise origin.",
    "No actualization, Bell, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def covariantNoiseApproximationControl : ResearchTask := {
  id := "covariant_noise_approximation_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply a finite nonempty carrier V of cardinality n and 0<t<1. Set K_t(x,r)=(1-t)*indicator(r=x)+t/n. Row TV is half the sum of absolute row differences. The coefficient covariance defect is the signed difference between the two sides of full product covariance, and channel covariance TV is half the sum of its absolute coefficients for one input pair.",
    "The coefficient and channel bounds assume an injective gate F. Coefficient-bound attainment additionally assumes a nontrivial carrier, F squared equal to swap and diagonal transparency. The concrete four-state specialization uses the existing RawNetworkMedialWall.State and gate."]
  conclusions := [
    "Every K_t entry is at least t/n>0 and at most one, and each row sums to one. Every pair of distinct rows has TV exactly 1-t.",
    "For every injective F each absolute covariance coefficient defect is at most t*(1-t)/n. Under the additional nontrivial square-swap and diagonal hypotheses this coefficient bound is attained.",
    "For every injective F and every input pair channel covariance TV is at most 2*t*(1-t), a dimension-free bound. On a finite carrier injectivity makes F bijective, so output reindexing identifies this half-sum with TV between the corresponding two channels.",
    "For every epsilon>0 there is 0<t<1 with positive normalized K_t, TV at least 1-epsilon between every distinct pair of rows, and both every absolute coefficient defect and every input channel-TV defect at most epsilon. On a nontrivial carrier a distinct row pair exists. The existing four-state square-swap gate supplies a concrete nonvacuous specialization."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/CovariantNoiseApproximationControl.lean"
      declarations := [
        "IDT.QMClosure.CovariantNoiseApproximationControl.positivity_floor",
        "IDT.QMClosure.CovariantNoiseApproximationControl.row_sum",
        "IDT.QMClosure.CovariantNoiseApproximationControl.entry_le_one",
        "IDT.QMClosure.CovariantNoiseApproximationControl.rowTV_distinct",
        "IDT.QMClosure.CovariantNoiseApproximationControl.coefficient_defect_bound",
        "IDT.QMClosure.CovariantNoiseApproximationControl.coefficient_bound_attained",
        "IDT.QMClosure.CovariantNoiseApproximationControl.channel_covariance_TV_bound",
        "IDT.QMClosure.CovariantNoiseApproximationControl.arbitrarily_small_covariance_defects",
        "IDT.QMClosure.CovariantNoiseApproximationControl.nontrivial_near_distinguishable_family",
        "IDT.QMClosure.CovariantNoiseApproximationControl.four_state_near_distinguishable_family"] }]
  plannedArtifacts := []
  dependencies := ["finite_covariant_noise_wall", "raw_network_medial_wall"]
  limits := [
    "Exact-covariance rigidity remains valid. In this approximation family the positive lower bound t/n tends to zero as t tends to zero, while distinct rows approach maximal TV. Small coefficient or channel-TV error alone therefore supplies no floor-independent vanishing row-distinction bound.",
    "The checked channel bound is 2*t*(1-t). No sharper analytic estimate is registered as checked evidence. Quantitative stability under a fixed positive entry floor or other additional assumptions remains open.",
    "These are finite real stochastic matrices and specified finite-sum norms. They establish no continuum, resource-graded budget or Gaussian-noise theorem and supply no physical noise origin.",
    "No actualization, Bell, full QM, GR or physical-scale closure is recorded. Public and manifest statuses remain unchanged."] }

def rawSparseSignedControl : ResearchTask := {
  id := "raw_sparse_signed_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the native complex mixer and real-part readout W as a mathematical omission control. Retain zero weight, square-swap, diagonal transparency, pair-weight conservation and the actual sparse row-marginal condition; omit nonnegativity."]
  conclusions := [
    "The checked native-complex-mixer real-part control satisfies the actual sparse law, has K identically zero and KernelEq for every pair, but W(-1)=-1. Thus this signed example satisfies the sparse and kernel laws without nonnegativity.",
    "The checked vacuum value is W(A(i))=-1/2, different from W(i)/2=0. KernelEq(0,1) holds while W(0) differs from W(1), and the universal weight-descent implication fails. This is an omission countercontrol for extending half-balance or weight descent to signed weights.",
    "Universal KernelEq in this signed control does not authorize the nonnegative-stage equivalence with ObservationalEq. In particular, the weight-distinct pair 0,1 is not asserted to be observationally equivalent."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RawSparseSignedControl.lean"
      declarations := [
        "IDT.QMClosure.RawSparseSignedControl.contract",
        "IDT.QMClosure.RawSparseSignedControl.sparse_law",
        "IDT.QMClosure.RawSparseSignedControl.kernel_zero",
        "IDT.QMClosure.RawSparseSignedControl.kernelEq_all",
        "IDT.QMClosure.RawSparseSignedControl.imaginary_vacuum_weight",
        "IDT.QMClosure.RawSparseSignedControl.vacuum_half_failure",
        "IDT.QMClosure.RawSparseSignedControl.negative_weight",
        "IDT.QMClosure.RawSparseSignedControl.not_nonnegative",
        "IDT.QMClosure.RawSparseSignedControl.kernel_equiv_weight_distinction",
        "IDT.QMClosure.RawSparseSignedControl.kernel_equiv_does_not_force_weight_descent"] }]
  plannedArtifacts := []
  dependencies := [
    "raw_sparse_marginal_reconstruction"]
  limits := [
    "The complex carrier, native mixer and signed real-part readout define only a mathematical omission control. Signed weights are not physical probabilities; no physical availability, actualization or QM conclusion is inferred.",
    "These are checked conditional mathematical statements; public and manifest statuses remain unchanged."] }

def equivariantOutcomeSelectionWall : ResearchTask := {
  id := "equivariant_outcome_selection_wall"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "A deterministic single-label selector whose complete input is a supplied profile, and covariance under the stated outcome relabelings.",
    "For the dynamics extension, symmetry acts on the full process state, the initial state is fixed, both the update and extraction are equivariant, and extraction takes values in Option outcomes with a symmetry-fixed pending value."]
  conclusions := [
    "Independently accepted algebraic obstruction: the profile stabilizer must fix the selected label. A uniform binary profile with the swapping symmetry has no such single-label selector.",
    "The general stabilizer obstruction needs no probability normalization; ties alone need not exclude a fixed label.",
    "Equivariant updates preserve a symmetric initial full state at every finite iterate. If no outcome is fixed, an equivariant Option-valued extraction remains pending; this avoids the vacuity of requiring an already total single-label extraction at the symmetric initial state.",
    "A separately supplied distinguished label, transformed jointly with the profile, permits an equivariant deterministic selector."]
  checkedEvidence := []
  plannedArtifacts := ["ANALYTIC ONLY: a bounded stabilizer/profile-selector obstruction and explicit asymmetry control."]
  dependencies := ["particle_as_process_result_hypothesis", "standing_matter_regime_constraint"]
  limits := [
    "No new theorem is kernel checked. Equal probabilities do not imply symmetry of the complete physical process, apparatus, environment or realization datum.",
    "This is not an impossibility theorem for deterministic physics and does not choose a stochastic ontology.",
    "A covariant probability kernel or set of admissible labels is not a realized single outcome.",
    "An unrestricted equivariant-selector existence criterion using orbit representatives requires classical choice; no choice-free global sufficiency is claimed.",
    "Archival transition laws, physical detectors and matter-regime applicability remain open."] }

def primitivePresentationAlternatives : ResearchTask := {
  id := "primitive_presentation_alternatives"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "For the algebraic comparison, a binary operation with idempotency and the quadratical identity (x*y)*x=(z*x)*(y*z).",
    "For the analytic comparison, an exactly homogeneous map between real normed vector spaces and differentiability at the origin."]
  conclusions := [
    "Source-supported algebraic route: idempotency plus the quadratical identity is equivalent to idempotency, bookend and mediality; no separately supplied quasigroup or division premise is needed.",
    "The three variable symbols do not by themselves specify a three-wire experiment: inputs recur and first-channel expressions omit companion outputs.",
    "Independently reviewed analytic boundary: exact homogeneity and a common linear derivative at zero force global linearity. Mere existence of directional derivatives does not.",
    "On complex pairs, joint complex homogeneity then gives complex linearity; transparency and square-swap leave the native mixer and its inverse, with exact vacuum output selecting the orientation."]
  checkedEvidence := []
  plannedArtifacts := [
    "ANALYTIC ONLY: a possible Lean equivalence between the quadratical and existing transparent medial primitive presentations.",
    "ANALYTIC ONLY: a possible generic homogeneous-map derivative equivalence; existing tangent countermodels already record the directional-versus-Frechet boundary."]
  dependencies := ["continuous_balanced_nonmedial_wall", "raw_medial_addition"]
  limits := [
    "The quadratical comparison is supported by Drapal, Griggs and Kozlik, Quadratical quasigroups and Mendelsohn designs, Theorems 2.8, 2.10 and 2.11: https://oro.open.ac.uk/82222/1/quadra.pdf; its universal equivalence is not kernel checked here.",
    "These are equivalent mathematical presentations or explicit additional regularity premises, not a derivation of physical inevitability.",
    "Differentiation at the origin presupposes ambient linear and topological structure; it cannot be inferred from regularity only on normalized states or away from zero.",
    "No implication from physical no-signalling to mediality has been established."] }

def particleAsProcessResultHypothesis : ResearchTask := {
  id := "particle_as_process_result_hypothesis"
  stage := .openPhysicalBridge
  review := .openObligation
  assumptions := [
    "User-proposed research hypothesis, not an adopted ontology: a particle may be a result of processes and interactions rather than a supplied object with completed properties."]
  conclusions := []
  checkedEvidence := []
  plannedArtifacts := [
    "Separate a local registration event from a stable reproducible type of manifestations, and test candidate bridges between them.",
    "Probe extensions sharing probability values and calibrated presence marginals while distinguishing joint registration and archival laws; keep per-run realization and liveness separate.",
    "Compare IDT-native process/context mechanisms for producing one actual recorded fact without presupposing deterministic or fundamentally stochastic outcome selection.",
    "Specify candidate invariants by which repeated events could share charge, mass and spin, with exact conservation and correlation obligations."]
  dependencies := [
    "probability_actualization", "physical_state_process_completeness",
    "tensor_local_tomography_bell", "physical_scales"]
  limits := [
    "A registration event does not establish the absence of a persisting carrier.",
    "A probability law, including a selected Born-form law, does not by itself actualize one outcome.",
    "Any candidate must account for localization and discreteness of registrations, stable charge/mass/spin, interference, correlations and conservation laws.",
    "Neither an event-selection symbol nor a particle-type label counts as a derivation of the phenomenon it names.",
    "No particle ontology, event actualization, particle spectrum, physical mass scale or full QM/QFT result has been established."] }

def standingMatterRegimeConstraint : ResearchTask := {
  id := "standing_matter_regime_constraint"
  stage := .openPhysicalBridge
  review := .openObligation
  assumptions := [
    "Standing user direction: primitive selection must admit different organizations of matter and inspect whether definitions exclude known effects before any derivation begins.",
    "Independent objects with predetermined individual properties are not a mandatory starting ontology; using an ordinary carrier in a mathematical countermodel does not impose that ontology."]
  conclusions := []
  checkedEvidence := []
  plannedArtifacts := [
    "For each proposed or rejected primitive route, explicitly record regime applicability, identified conflicts and unassessed regions against matterRegimeObligations.",
    "Keep analogy, compatibility, finite models, conditional derivations and full physical derivations as distinct evidence levels with named assumptions.",
    "Ultimately include detectors, memory and observers within the same process rules used for the measured world."]
  dependencies := ["particle_as_process_result_hypothesis", "probability_actualization",
    "tensor_local_tomography_bell", "physical_state_process_completeness"]
  limits := [
    "No entry in the regime checklist is passed by default; the present entries are unassessed physical obligations.",
    "Bose-Einstein condensation and superfluidity are distinct properties and must not be identified.",
    "Decoherence and stable records do not by themselves establish a unique actual outcome.",
    "Effective quasiparticles give a concrete example of emergent particle-like behavior, not a proof of that ontology for all elementary particles.",
    "Defining charge through interactions does not prove that charge originates only during measurement.",
    "Do not tune primitives to a preferred ontology or upgrade compatibility to derivation; completed QM is not claimed."] }

def recordMarginalActualizationWall : ResearchTask := {
  id := "record_marginal_actualization_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A finite nonnegative normalized probability vector in one declared acquisition context, with two distinct positive labels for the nontrivial perturbation.",
    "Registration sets count distinct labels; their calibrated presence marginals are supplied. An exclusive categorical-outcome interpretation is not assumed.",
    "For the IDT adapter, the existing normalized record Family and positive source weight; any supplied event probability is linked only through the existing conditional record-probability theorem with its full domain and calibration hypotheses."]
  conclusions := [
    "Checked universal finite-label extension of the existing binary IntensityActualizationBoundary control: for an arbitrary finite label type, reducing two singleton masses by epsilon and adding epsilon to both empty and two-label registrations preserves every calibrated presence marginal and total probability.",
    "Normalized presence marginals fix expected distinct-label count at one; silent mass equals expected excess count. Silent and multiple-label defects are coupled, not independent omission witnesses.",
    "A zero-mass silent sample separates zero defect probability from a claim about every sample; a designated realized run requires an explicit support or realization premise.",
    "Diagonal and product archival couplings retain identical one-time marginals, but disagree with masses zero and 1-sum(p_r^2), respectively; the latter is positive for two distinct positive labels.",
    "The checked adapter leaves the original channels, effects and probability values intact while varying joint registration and archival laws."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RecordMarginalActualizationWall.lean"
      declarations := [
        "IDT.QMClosure.RecordMarginalActualizationWall.RecordModel.card_silent_excess_balance",
        "IDT.QMClosure.RecordMarginalActualizationWall.RecordModel.silent_eq_expectedExcess",
        "IDT.QMClosure.RecordMarginalActualizationWall.RecordModel.silent_zero_iff_multiple_zero",
        "IDT.QMClosure.RecordMarginalActualizationWall.RecordModel.one_on_positive_support",
        "IDT.QMClosure.RecordMarginalActualizationWall.calibrated_registration_wall",
        "IDT.QMClosure.RecordMarginalActualizationWall.balancedRecords_values",
        "IDT.QMClosure.RecordMarginalActualizationWall.zeroSilentRecords_boundary",
        "IDT.QMClosure.RecordMarginalActualizationWall.calibrated_archive_wall"] },
    { sourcePath := "Proofs/QMClosure/RecordMarginalActualizationAdapter.lean"
      declarations := [
        "IDT.QMClosure.RecordMarginalActualizationAdapter.ratioLaw",
        "IDT.QMClosure.RecordMarginalActualizationAdapter.ratio_registration_wall",
        "IDT.QMClosure.RecordMarginalActualizationAdapter.ratio_archive_wall",
        "IDT.QMClosure.RecordMarginalActualizationAdapter.conditionalLaw_eq_ratioLaw_mass",
        "IDT.QMClosure.RecordMarginalActualizationAdapter.conditional_registration_wall",
        "IDT.QMClosure.RecordMarginalActualizationAdapter.conditional_archive_wall"] }]
  plannedArtifacts := []
  dependencies := [
    "conditional_record_probabilities", "particle_as_process_result_hypothesis",
    "standing_matter_regime_constraint"]
  limits := [
    "The generic finite control is inhabited. Application to a particular supplied Family and DomainLaw remains conditional; no new physical family, detector or chosen sample is furnished.",
    "The shared values are probability numbers and label-presence marginals, not an already supplied mutually exclusive categorical-event interpretation. The adapter does not preserve the entire effect-domain event interpretation: identifying operator sums with unions of these presence events is an additional bridge.",
    "Distinct-label sets do not count repeated same-label clicks. The single-record question is scoped to eligible exclusive acquisition slots, not every interaction or the entire world.",
    "Empty registration, indefinite pending and an explicit terminal noClick or failure record are different; extra outcomes require a new normalized family or explicit conditioning.",
    "Archival agreement must follow from an independently specified transition/frame law; defining read-only as preservation supplies that fact rather than explaining it.",
    "Probability measures over possible histories do not select a realized history or settle deterministic versus fundamentally stochastic ontology.",
    "All standing matter-regime obligations remain unassessed; no particle type, stable charge/mass/spin, physical detector realization, or full QM conclusion follows."] }

def compositionExchangeScope : ResearchTask := {
  id := "composition_exchange_scope"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For the alternating wall: one source weight in both slots, an output zero of zero weight, universal product-weight factorization and zero output when both inputs coincide.",
    "For the symmetric wall: the actual separate-additivity, separate-phase, positive-quadratic and product-weight premises of CompositeProductKernel.product_kernel with the same source readout and phase in both slots.",
    "Commutation is either literal equality of the two ordered products or an explicitly supplied zero-weight difference in the output carrier."]
  conclusions := [
    "Checked diagonal wall: alternating diagonal cancellation and universal product-weight factorization force every source weight to vanish; no additivity or Hilbert premise is needed for that diagonal argument.",
    "Under the full product-kernel contract, commutation forces normSq(K(x,y)) = Q(x)*Q(y). A positive-weight orthogonal pair therefore excludes commutation.",
    "The same pairwise identity follows from commutation modulo an output null difference through existing null-kernel lemmas.",
    "Complex scalar multiplication supplies a nontrivial commutative factorizing control; the obstruction needs an orthogonal positive pair, not symmetry alone."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/CompositionExchangeScope.lean"
      declarations := [
        "IDT.QMClosure.CompositionExchangeScope.source_zero_of_diagonal_zero",
        "IDT.QMClosure.CompositionExchangeScope.all_source_zero_of_diagonal_zero",
        "IDT.QMClosure.CompositionExchangeScope.positive_source_excludes_universal_diagonal_zero",
        "IDT.QMClosure.CompositionExchangeScope.normSq_kernel_eq_of_null_exchange_difference",
        "IDT.QMClosure.CompositionExchangeScope.normSq_kernel_eq_of_exchange_eq",
        "IDT.QMClosure.CompositionExchangeScope.positive_orthogonal_excludes_null_exchange_difference",
        "IDT.QMClosure.CompositionExchangeScope.positive_orthogonal_excludes_exchange_eq",
        "IDT.QMClosure.CompositionExchangeScope.ComplexMultiplicationControl.nontrivial_symmetric_factorizing_control"] }]
  plannedArtifacts := []
  dependencies := ["composite_product_kernel", "standing_matter_regime_constraint"]
  limits := [
    "These are conditional scope theorems for the supplied product contract; no dimension or rank classification is asserted.",
    "The existing product theorem remains a correct sufficient bridge. This task bounds treating its factorization as a primitive for every kind of composition.",
    "Universal factorization with the full additive and phase contract is essential here; restricted factorization on orthogonal inputs or nonlinear normalized products is not excluded.",
    "Output null-difference commutation is not arbitrary physical observational equivalence without a matching bridge.",
    "Single-reference native circuits are not already a particle sector. Tensor-factor exchange, mode permutations and particle exchange require distinct interpretations.",
    "Symmetric and exterior pair preparations are different supplied embeddings; a later tensor illustration would not be different predictions for an identical fully specified input.",
    "Physical indistinguishability, particle statistics, spin-statistics and every standing matter-regime obligation remain unassessed."] }

def pairExchangeCombinations : ResearchTask := {
  id := "pair_exchange_combinations"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The same-source ordered product bridge from CompositeProductKernel: additive source and target groups, positive quadratic readouts, compatible quarter-turn phases, separate additivity, both phase compatibilities and universal product readout for the supplied ordered map p.",
    "The new maps are mathematical target-group expressions Splus(x,y)=p(x,y)+p(y,x) and Sminus(x,y)=p(x,y)-p(y,x)."]
  conclusions := [
    "Checked conditional construction: both pair maps retain separate additivity and phase compatibility; the plus map is symmetric and the minus map is alternating.",
    "Their same-sign kernels are twice the sum or difference of the direct and exchanged product kernels. The mixed plus/minus kernel vanishes.",
    "Their readouts are 2*Q(x)*Q(y) plus or minus 2*normSq(K(x,y)); positivity is inherited from the target readout.",
    "The minus diagonal is zero, the plus diagonal has weight 4*Q(x)^2, and the two readouts sum to 4*Q(x)*Q(y). An orthogonal positive-weight pair has positive minus readout."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/PairExchangeCombinations.lean"
      declarations := [
        "IDT.QMClosure.PairExchangeCombinations.plus_exchange",
        "IDT.QMClosure.PairExchangeCombinations.minus_exchange",
        "IDT.QMClosure.PairExchangeCombinations.minus_diagonal",
        "IDT.QMClosure.PairExchangeCombinations.plus_add_minus",
        "IDT.QMClosure.PairExchangeCombinations.plus_kernel",
        "IDT.QMClosure.PairExchangeCombinations.minus_kernel",
        "IDT.QMClosure.PairExchangeCombinations.mixed_kernel",
        "IDT.QMClosure.PairExchangeCombinations.plus_readout",
        "IDT.QMClosure.PairExchangeCombinations.minus_readout",
        "IDT.QMClosure.PairExchangeCombinations.plus_diagonal_readout",
        "IDT.QMClosure.PairExchangeCombinations.sum_readouts",
        "IDT.QMClosure.PairExchangeCombinations.minus_positive_of_orthogonal",
        "IDT.QMClosure.PairExchangeCombinations.scalar_control_minus_zero"] }]
  plannedArtifacts := []
  dependencies := ["composition_exchange_scope", "composite_product_kernel"]
  limits := [
    "No tensor carrier, scalar multiplication or square-root normalization is an input to these raw pair constructions.",
    "The original ordered map retains universal product factorization; the new pair combinations generally do not.",
    "Argument-swap identities do not by themselves supply a global raw-target exchange operator. Pair-map images need not be additive subgroups, and no direct sum or target exhaustion is asserted.",
    "Without halving, only Splus+Sminus equals twice the ordered product follows at the raw level. Semidefinite weights permit nonzero null intersections.",
    "Alternating nontriviality is conditional; complex scalar multiplication gives an identically zero minus map.",
    "Physical availability of products and sums, coherent repeated inputs, exchange-sign selection, species, spin-statistics, probabilities of pair creation and every standing matter regime remain open."] }

def productFeatureExchange : ResearchTask := {
  id := "product_feature_exchange"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The same-source weighted ordered-product Bridge retains exactly QA, QC, their positive quadratic contracts, compatible phases jA and jC, p, separate additivity, both phase compatibilities and universal product readout factorization.",
    "The target H is the existing CanonicalQuadraticHilbert output constructed from QC and jC; the exchange domain Hp is only the closed complex span of features of the supplied ordered products p(x,y).",
    "The generic equal-Gram utility compares supplied complete complex inner-product spaces. Its product instantiation uses only the already constructed H and Hp."]
  conclusions := [
    "Checked equal-Gram extension: arbitrary indexed families with equal Gram entries determine a unique complex linear isometry equivalence of their generated closed spans, including empty or degenerate families without coefficient-map injectivity or a nontriviality premise.",
    "Swapping the same-source product indices preserves all generator inner products and constructs the unique exchange isometry on Hp with that generator action; the exchange is involutive and self-adjoint.",
    "Within Hp, (I+S)/2 and (I-S)/2 are self-adjoint idempotents with complementary orthogonal ranges equal to the closed spans of the plus and minus pair features.",
    "Projected generator squared norms are (QA(x)*QA(y) plus or minus normSq(K(x,y)))/2; the minus range is nonzero exactly when some pair has strict overlap inequality.",
    "The standard Hp completeness and adjoint Star instances are constructed from existing mathematical outputs and add no supplied assumptions or Bridge fields."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/EqualGramSpanEquivalence.lean"
      declarations := [
        "IDT.QMClosure.EqualGramSpanEquivalence.dense_spanGenerator",
        "IDT.QMClosure.EqualGramSpanEquivalence.inner_linearCombination",
        "IDT.QMClosure.EqualGramSpanEquivalence.denseEquivalence",
        "IDT.QMClosure.EqualGramSpanEquivalence.denseEquivalence_apply",
        "IDT.QMClosure.EqualGramSpanEquivalence.dense_generator_ext",
        "IDT.QMClosure.EqualGramSpanEquivalence.denseEquivalence_unique",
        "IDT.QMClosure.EqualGramSpanEquivalence.closedSpanEquivalence",
        "IDT.QMClosure.EqualGramSpanEquivalence.closedSpanEquivalence_apply",
        "IDT.QMClosure.EqualGramSpanEquivalence.closedSpanEquivalence_unique"] },
    { sourcePath := "Proofs/QMClosure/UnitaryInvolutionProjections.lean"
      declarations := [
        "IDT.QMClosure.UnitaryInvolutionProjections.plus_idempotent",
        "IDT.QMClosure.UnitaryInvolutionProjections.minus_idempotent",
        "IDT.QMClosure.UnitaryInvolutionProjections.plus_add_minus",
        "IDT.QMClosure.UnitaryInvolutionProjections.plus_comp_minus",
        "IDT.QMClosure.UnitaryInvolutionProjections.minus_comp_plus",
        "IDT.QMClosure.UnitaryInvolutionProjections.op_selfAdjoint",
        "IDT.QMClosure.UnitaryInvolutionProjections.plus_selfAdjoint",
        "IDT.QMClosure.UnitaryInvolutionProjections.minus_selfAdjoint",
        "IDT.QMClosure.UnitaryInvolutionProjections.plus_norm_sq",
        "IDT.QMClosure.UnitaryInvolutionProjections.minus_norm_sq",
        "IDT.QMClosure.UnitaryInvolutionProjections.mixed_inner",
        "IDT.QMClosure.UnitaryInvolutionProjections.range_eq_closedSpan",
        "IDT.QMClosure.UnitaryInvolutionProjections.range_ne_bot_iff"] },
    { sourcePath := "Proofs/QMClosure/ProductFeatureExchange.lean"
      declarations := [
        "IDT.QMClosure.ProductFeatureExchange.Bridge",
        "IDT.QMClosure.ProductFeatureExchange.hp_completeSpace",
        "IDT.QMClosure.ProductFeatureExchange.hp_clmStar",
        "IDT.QMClosure.ProductFeatureExchange.inner_generator",
        "IDT.QMClosure.ProductFeatureExchange.equalGram",
        "IDT.QMClosure.ProductFeatureExchange.exchange",
        "IDT.QMClosure.ProductFeatureExchange.exchange_generator",
        "IDT.QMClosure.ProductFeatureExchange.exchange_unique",
        "IDT.QMClosure.ProductFeatureExchange.exchange_involutive",
        "IDT.QMClosure.ProductFeatureExchange.exchange_selfAdjoint",
        "IDT.QMClosure.ProductFeatureExchange.plus_selfAdjoint",
        "IDT.QMClosure.ProductFeatureExchange.minus_selfAdjoint",
        "IDT.QMClosure.ProductFeatureExchange.plus_idempotent",
        "IDT.QMClosure.ProductFeatureExchange.minus_idempotent",
        "IDT.QMClosure.ProductFeatureExchange.coe_plus_generator",
        "IDT.QMClosure.ProductFeatureExchange.coe_minus_generator",
        "IDT.QMClosure.ProductFeatureExchange.plus_generator_norm_sq",
        "IDT.QMClosure.ProductFeatureExchange.minus_generator_norm_sq",
        "IDT.QMClosure.ProductFeatureExchange.plus_range_eq_closedSpan",
        "IDT.QMClosure.ProductFeatureExchange.minus_range_eq_closedSpan",
        "IDT.QMClosure.ProductFeatureExchange.orthogonal_decomposition",
        "IDT.QMClosure.ProductFeatureExchange.minus_range_ne_bot_iff"] }]
  plannedArtifacts := []
  dependencies := ["pair_exchange_combinations", "composite_product_kernel",
    "canonical_hilbert_completion", "canonical_hilbert_uniqueness"]
  limits := [
    "This is the weighted ordered-product route, not an end-to-end weight-free composite reconstruction from the response-probability theorem.",
    "The generic utility assumes mathematical comparison spaces; the product adapter explicitly instantiates the constructed target. Q(x)*Q(y) with componentwise addition is generally quartic and is not supplied to quadratic completion.",
    "Division by two occurs only in the constructed Hilbert output. No raw halving, raw exchange operator, raw direct sum, whole-target exhaustion or physical exchange/projection availability is asserted.",
    "Argument exchange, mode permutations and physical particle exchange remain distinct. Exchange-sign selection, species, spin-statistics, pair-preparation availability, outcome actualization and every matter-regime obligation remain open."] }

def productExchangeObservationBoundary : ResearchTask := {
  id := "product_exchange_observation_boundary"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "For generic invariance, a supplied complex linear isometry equivalence U and bounded complex-linear E commute pointwise; no involution, positivity, nonzero-vector or completeness premise is required.",
    "The product adapter retains the exact weighted ProductFeatureExchange.Bridge D and constructed Hp; g=generator(x,y), q=QA(x)*QA(y), r=normSq(K(x,y)) and S=exchange D."]
  conclusions := [
    "Commuting E and U give identical complex expectations and normalized expectations on u and U(u), including zero under the numerical division convention.",
    "The full complex overlap inner(g,S(g)) equals (r:Complex). The strict inequality r<q implies q>0 and nonzero g, plus(g) and minus(g) for the same generator.",
    "The actual singleton starProjection E_g onto the complex span of g in constructed Hp is positive, at most identity in the standard Loewner order, and has operator norm at most one.",
    "The exact normalized response on S(g) is (r/q)^2 without a strictness premise, using the division convention. Under r<q the response on g is 1, the response on S(g) is strictly below 1, and S(g) is not any complex scalar multiple of g.",
    "The assembled strict-pair theorem retains both nonzero components, every commuting-operator equality and the specified mathematical discriminator for one generator. Nonzero minus range supplies such a strict pair and the same witness."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ProductExchangeObservationBoundary.lean"
      declarations := [
        "IDT.QMClosure.ProductExchangeObservationBoundary.inner_invariant",
        "IDT.QMClosure.ProductExchangeObservationBoundary.normalizedExpectation_invariant",
        "IDT.QMClosure.ProductExchangeObservationBoundary.inner_exchange_generator",
        "IDT.QMClosure.ProductExchangeObservationBoundary.strict_pair_facts",
        "IDT.QMClosure.ProductExchangeObservationBoundary.generatorProjector_positive",
        "IDT.QMClosure.ProductExchangeObservationBoundary.generatorProjector_le_one",
        "IDT.QMClosure.ProductExchangeObservationBoundary.generatorProjector_norm_le",
        "IDT.QMClosure.ProductExchangeObservationBoundary.generatorProjector_self",
        "IDT.QMClosure.ProductExchangeObservationBoundary.generatorProjector_expectation_self",
        "IDT.QMClosure.ProductExchangeObservationBoundary.generatorProjector_expectation_exchange",
        "IDT.QMClosure.ProductExchangeObservationBoundary.generatorProjector_expectation_exchange_lt_one",
        "IDT.QMClosure.ProductExchangeObservationBoundary.exchange_not_scalar",
        "IDT.QMClosure.ProductExchangeObservationBoundary.strict_pair_observation_boundary",
        "IDT.QMClosure.ProductExchangeObservationBoundary.minus_range_observation_witness"] }]
  plannedArtifacts := []
  dependencies := ["product_feature_exchange", "coherent_port_ray_boundary"]
  limits := [
    "Every weighted ordered-product Bridge assumption remains supplied. The construction acts only in the product-generated closed span Hp, not a raw/global exchange or a whole-target exhaustion.",
    "The singleton projector is a mathematical positive contraction, not an established native or physically available discriminator. No probability-law or Born premise is used for these numerical quantities.",
    "Response equality concerns g and S(g); it neither identifies arbitrary states nor makes sector weights invisible. Restriction to S-commuting operators does not select exchange eigenstates.",
    "Physical ordered-product and discriminator availability, exchange sector, species, spin-statistics, actualization and every matter-regime obligation remain open. No QM or manifest claim is upgraded."] }

def nativePreparationNaturality : ResearchTask := {
  id := "native_preparation_naturality"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Function-only covariance of both outputs of supplied raw operations gives evaluator covariance on arbitrary arrays and finite native words; no raw algebra or Fintype premise is supplied.",
    "The r:RawOperationalData V and s:RawOperationalData W adapters retain their structural contracts. Prepared covariance and law pullback preserve chosen zero and intertwine the normalized operations; normalization covariance itself needs no zero-preservation premise.",
    "Forward mapLaw needs only reflection of equal prepared arrays at the same reference, source and width. Injectivity together with prepared covariance suffices for this reflection; lawEquiv also retains zero preservation and normalized covariance for the reverse direction."]
  conclusions := [
    "Checked both-output covariance transports the raw evaluator and is preserved by term-defined diagonal normalization without original-gate transparency.",
    "Zero preservation and normalized covariance transport basis-prepared arrays. pullLaw uses this equality preservation; mapLaw uses only the stated prepared-equality reflection.",
    "The two adapters form a Law equivalence retaining the entire identical probability field and all six conditions. Their construction uses neither normSq selection nor a canonical probability witness.",
    "Negation in the reconstructed group gives normalized common-array and common-reference sign covariance, injective prepared-equality reflection and the same-field negLawEquiv."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativePreparationNaturality.lean"
      declarations := [
        "IDT.QMClosure.NativePreparationNaturality.MapsOperation",
        "IDT.QMClosure.NativePreparationNaturality.evalRaw_covariance",
        "IDT.QMClosure.NativePreparationNaturality.normalizedOperation_covariance",
        "IDT.QMClosure.NativePreparationNaturality.basisInput_covariance",
        "IDT.QMClosure.NativePreparationNaturality.prepared_covariance",
        "IDT.QMClosure.NativePreparationNaturality.prepared_equality_preserved",
        "IDT.QMClosure.NativePreparationNaturality.PreparedEqualityReflecting",
        "IDT.QMClosure.NativePreparationNaturality.preparedEqualityReflecting_of_injective",
        "IDT.QMClosure.NativePreparationNaturality.pullLaw",
        "IDT.QMClosure.NativePreparationNaturality.mapLaw",
        "IDT.QMClosure.NativePreparationNaturality.lawEquiv",
        "IDT.QMClosure.NativePreparationNaturality.pullLaw_probability",
        "IDT.QMClosure.NativePreparationNaturality.mapLaw_probability",
        "IDT.QMClosure.NativePreparationNaturality.negMap_zero",
        "IDT.QMClosure.NativePreparationNaturality.negMap_injective",
        "IDT.QMClosure.NativePreparationNaturality.negMap_normalized_covariance",
        "IDT.QMClosure.NativePreparationNaturality.prepared_neg",
        "IDT.QMClosure.NativePreparationNaturality.negLawEquiv",
        "IDT.QMClosure.NativePreparationNaturality.negLawEquiv_probability"] }]
  plannedArtifacts := []
  dependencies := ["weight_free_raw_probability"]
  limits := [
    "Original-gate semantics requires transparency or a separate original-operation covariance proof.",
    "Prepared-equality reflection is sufficient for this adapter construction; it is not asserted necessary for probability-law existence, whose existing criterion is infinite additive reference order.",
    "The adapters concern literal raw arrays. Raw injectivity alone does not transport response-context Law.",
    "A compatible map need not be executable, native, physically available, unitary or a gauge map. No U(1) symmetry, independent per-wire quotient, actualization or full QM is established."] }

def responsePhaseQuotientWall : ResearchTask := {
  id := "response_phase_quotient_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Ambient d:ResponseContextQuotient.Data retains its supplied structural fields. The zero-reference contradiction proof uses only normalized, prepared_eq, output_perm and vacuum probability fields with identity/permutation semantics and the Unit-plus-Unit vacuum embedding.",
    "The separate structural negative-fixed-point statement uses the reconstructed additive half, public PhaseMixerCancellation.doubling_injective and reconstruction.halves; it requires neither observed transparency nor a Law."]
  conclusions := [
    "Checked conditional theorem: a supplied response Law forbids a reference contextually equivalent to chosenZero without an observed-transparency premise.",
    "In the reconstructed response quotient, x=-x iff x=0. Consequently any supplied response Law has a nonzero reference class [v] distinct from -[v], without observed transparency.",
    "A raw representative w of -[v] is contextually distinguishable from v; signature blindness by itself does not identify contextual classes."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ResponsePhaseQuotientWall.lean"
      declarations := [
        "IDT.QMClosure.ResponsePhaseQuotientWall.response_equal_coordinate_probabilities",
        "IDT.QMClosure.ResponsePhaseQuotientWall.no_law_of_reference_response_zero",
        "IDT.QMClosure.ResponsePhaseQuotientWall.neg_fixed_iff_zero",
        "IDT.QMClosure.ResponsePhaseQuotientWall.classOf_eq_zero_iff_response_zero",
        "IDT.QMClosure.ResponsePhaseQuotientWall.reference_class_ne_zero",
        "IDT.QMClosure.ResponsePhaseQuotientWall.reference_class_ne_neg",
        "IDT.QMClosure.ResponsePhaseQuotientWall.negative_representative_distinguishable"] }]
  plannedArtifacts := []
  dependencies := ["response_context_probability", "raw_native_probability_existence",
    "coherent_port_ray_boundary"]
  limits := [
    "Existing response uniqueness and infinite-order theorems retain their observed-transparency premises.",
    "This wall does not exclude ordinary rays or a common sign transformation on complete prepared arrays. No independent per-wire phase quotient, physical reference availability or outcome interpretation follows."] }

def portFrameAlignment : ResearchTask := {
  id := "port_frame_alignment"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Pure function contract: chosen alignments kappa:A equiv B and lambda:C equiv E define swap_kappa(a,b)=(kappa.inverse(b),kappa(a)) and the analogous target swap_lambda.",
    "Separate maps f:A to C and g:B to E intertwine the full two-output gates: S composed with (f times g) equals (f times g) composed with T; T squared is swap_kappa and S squared is swap_lambda.",
    "An alternative constructive formulation supplies only raw T:A times B to A times B and crossmaps u:B to A and v:A to B with T(T(a,b))=(u(b),v(a)); a chosen equivalence is then constructed from four-use return."]
  conclusions := [
    "Checked conditional theorem: squaring full both-output intertwining forces g composed with kappa equals lambda composed with f. Literal common-carrier swaps force f=g.",
    "Alignment compatibility is exactly equivalent to swap_lambda composed with (f times g) equals (f times g) composed with swap_kappa. A common map is necessary, not sufficient, for gate intertwining.",
    "Independent bijective frame changes conjugate the gate and transform alignment to lambda=g composed with kappa composed with f.inverse. In the same-carrier case the transformed alignment is the literal swap exactly when the two frame maps coincide.",
    "On a restricted joint domain, compatibility follows only on projections of pairs p for which covariance at p and T(p), and the needed square identities, hold. Individual reachability does not supply fullness of the joint domain.",
    "Dropping the root-square premise permits unequal maps in the countercontrol T=S=identity. Existing MixerRecordNaturality.first_output_iff already assumes one common map and cannot infer it from first-output covariance alone.",
    "Checked constructive alternative: under cross-local double routing, T applied four times is identity iff u(v(a))=a for every a and v(u(b))=b for every b. Evaluating at (a,v(a)) and (u(b),b) supplies both inverse laws without choice or nonemptiness and constructs kappa with exact forward map v and inverse u.",
    "Crossmaps are unique under equal double-routing factorizations even without four-use return, by evaluations at (u(b),b) and (a,v(a)). This is an exact reformulation of the aligned-root contract, not a weaker physical premise."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/PortFrameAlignment.lean"
      declarations := [
        "IDT.QMClosure.PortFrameAlignment.root_alignment_compatible",
        "IDT.QMClosure.PortFrameAlignment.literal_root_forces_common_map",
        "IDT.QMClosure.PortFrameAlignment.alignedSwap_map_iff",
        "IDT.QMClosure.PortFrameAlignment.conjugate_alignedSwap",
        "IDT.QMClosure.PortFrameAlignment.conjugateGate_square",
        "IDT.QMClosure.PortFrameAlignment.conjugated_root_square",
        "IDT.QMClosure.PortFrameAlignment.twistedSwap_eq_swap_iff",
        "IDT.QMClosure.PortFrameAlignment.partial_swap_intertwining",
        "IDT.QMClosure.PortFrameAlignment.partial_pair_agreement",
        "IDT.QMClosure.PortFrameAlignment.cross_square_fourfold",
        "IDT.QMClosure.PortFrameAlignment.fourfold_iff_cross_return",
        "IDT.QMClosure.PortFrameAlignment.alignmentOfCrossReturn",
        "IDT.QMClosure.PortFrameAlignment.alignmentOfCrossReturn_apply",
        "IDT.QMClosure.PortFrameAlignment.alignmentOfCrossReturn_symm_apply",
        "IDT.QMClosure.PortFrameAlignment.square_eq_alignmentOfCrossReturn",
        "IDT.QMClosure.PortFrameAlignment.crossmaps_unique",
        "IDT.QMClosure.PortFrameAlignment.WithoutSquareControl.full_covariance",
        "IDT.QMClosure.PortFrameAlignment.WithoutSquareControl.maps_differ",
        "IDT.QMClosure.PortFrameAlignment.WithoutSquareControl.square_is_not_swap",
        "IDT.QMClosure.PortFrameAlignment.FirstOutputControl.first_output_covariance",
        "IDT.QMClosure.PortFrameAlignment.FirstOutputControl.gate_square",
        "IDT.QMClosure.PortFrameAlignment.FirstOutputControl.maps_differ",
        "IDT.QMClosure.PortFrameAlignment.FirstOutputControl.not_full_covariance",
        "IDT.QMClosure.PortFrameAlignment.WithoutFourthControl.gate_square",
        "IDT.QMClosure.PortFrameAlignment.WithoutFourthControl.gate_bijective",
        "IDT.QMClosure.PortFrameAlignment.WithoutFourthControl.not_fourfold_identity",
        "IDT.QMClosure.PortFrameAlignment.WithoutFourthControl.transferForward_comp_transferBack_ne_id",
        "IDT.QMClosure.PortFrameAlignment.WithoutFourthControl.transferBack_comp_transferForward_ne_id"] }]
  plannedArtifacts := []
  dependencies := ["mixer_record_naturality", "response_context_probability"]
  limits := [
    "The pure alignment theorem requires no transparency, mediality, algebra, chosen zero, injectivity, readout, probability Law or nonemptiness premise.",
    "The checked FirstOutputControl has root-square routing and first-output covariance with unequal maps, while full both-output covariance fails. First-output covariance does not force the alignment conclusion.",
    "The checked WithoutFourthControl is bijective and cross-local under double routing, yet four-use return and both crossmap inverse laws fail. Four-use return is independent; no physical synchronization follows.",
    "The root-square law contains a port identification; it does not physically create reference alignment. Physical gates, references, QM closure and matter applicability remain open."] }

def nativeSingleSourceReferenceWall : ResearchTask := {
  id := "native_single_source_reference_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Weight-free r:WeightFreeRawProbability.RawOperationalData V, v:r.Carrier and ReferenceInfiniteOrder r v; each finite native preparation starts from one basis source v and otherwise chosen-zero ports.",
    "Set u=firstMix r v=(r.normalizedOperation(v,zero)).first and w=secondMix r v=(r.normalizedOperation(v,u)).first. The direct core assumes no probability Law, positive raw weight, feature or Hilbert premise."]
  conclusions := [
    "Checked conditional theorem: v and u are individually one-source native-accessible, but w is not any output of any one-source finite native circuit, at any finite width.",
    "For r.zeroWeightData, secondMix_related represents w by the scalar coefficient 1+i/2. Infinite reference order and raw/scalar semantic reflection exclude an alleged raw prepared equality.",
    "source_readout and output_normSq_le_one derive the scalar normSq bound 1 from native circuit conservation. The forbidden scalar coefficient has normSq 5/4; the auxiliary identically zero raw weight is not a positivity or probability input.",
    "counterexample_accounting separately records the scalar two-input budget 3/2 and output norms 5/4 and 1/4; one_a_not_jointly_prepared separates individual accessibility from joint preparation.",
    "aligned_sum_difference retains the same source and actual event recipes: a common finite circuit has distinct outputs (z+t)/2 and i*(z-t)/2. These coherent attenuated joins require no probability Law and remain available despite the unattenuated wall."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeSingleSourceReferenceWall.lean"
      declarations := [
        "IDT.QMClosure.NativeSingleSourceReferenceWall.reference_raw_reachable",
        "IDT.QMClosure.NativeSingleSourceReferenceWall.firstMix_raw_reachable",
        "IDT.QMClosure.NativeSingleSourceReferenceWall.secondMix_related",
        "IDT.QMClosure.NativeSingleSourceReferenceWall.secondMix_not_prepared",
        "IDT.QMClosure.NativeSingleSourceReferenceWall.secondMix_not_raw_reachable",
        "IDT.QMClosure.NativeSingleSourceReferenceWall.raw_reachable_not_closed",
        "IDT.QMClosure.NativeSingleSourceReferenceWall.source_readout",
        "IDT.QMClosure.NativeSingleSourceReferenceWall.output_normSq_le_one",
        "IDT.QMClosure.NativeSingleSourceReferenceWall.mixer_one_a_normSq",
        "IDT.QMClosure.NativeSingleSourceReferenceWall.counterexample_accounting",
        "IDT.QMClosure.NativeSingleSourceReferenceWall.one_a_not_jointly_prepared",
        "IDT.QMClosure.NativeSingleSourceReferenceWall.aligned_sum_difference"] }]
  plannedArtifacts := []
  dependencies := ["weight_free_raw_probability", "raw_native_probability_existence",
    "native_vacuum_probability_family", "raw_native_scalar_circuit_bridge",
    "native_gaussian_probability_selection"]
  limits := [
    "Infinite reference order is essential to the raw wall; the zero carrier defeats an unrestricted claim. No Law is an input to the weight-free core.",
    "Normalized operations are not automatically the original physical gate; that interpretation needs transparency or a separate evaluator bridge.",
    "The wall does not forbid coherent attenuated joins. Additional sources or independently prepared references change the source budget.",
    "Native readout and source accounting are not physical energy, particle count, no-cloning, physical availability, matter applicability or actualization theorems."] }

def referenceOccurrenceCompilation : ResearchTask := {
  id := "reference_occurrence_compilation"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "An arbitrary raw two-output function T on V and the finite one-hole Context grammar; no chosen zero, algebraic mixer law, readout or probability premise is required.",
    "Recursive input ports are Ports(hole)=Unit and Ports(node)=Ports(child) sum Unit. The hole receives x and every syntactic reference occurrence receives a distinct fresh input port with its stated value."]
  conclusions := [
    "Checked arbitrary-input padding semantics retains all supplied filler values. Compilation pads the child circuit and pairs its selected cursor with the fresh reference port in the specified operand order, retaining the complete output array.",
    "compile_correct identifies the compiled selected result with Context.eval T c x for every raw T. Injective occurrence ports are disjoint from the hole, inputs preserve the hole and reference values, and card_ports counts reference occurrences plus one.",
    "compile_plug_selected establishes substitution at the selected semantic result. The two compiled sides have different resource types; no equality of complete arrays or physical composition theorem is asserted."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ReferenceOccurrenceCompilation.lean"
      declarations := [
        "IDT.QMClosure.ReferenceOccurrenceCompilation.evalRaw_padCircuit",
        "IDT.QMClosure.ReferenceOccurrenceCompilation.evalRaw_pair_select",
        "IDT.QMClosure.ReferenceOccurrenceCompilation.occurrencePort_injective",
        "IDT.QMClosure.ReferenceOccurrenceCompilation.holePort_not_occurrence",
        "IDT.QMClosure.ReferenceOccurrenceCompilation.inputs_hole",
        "IDT.QMClosure.ReferenceOccurrenceCompilation.inputs_reference",
        "IDT.QMClosure.ReferenceOccurrenceCompilation.card_ports",
        "IDT.QMClosure.ReferenceOccurrenceCompilation.compile_correct",
        "IDT.QMClosure.ReferenceOccurrenceCompilation.compile_plug_selected"] }]
  plannedArtifacts := []
  dependencies := ["weight_free_raw_probability", "response_context_probability",
    "native_single_source_reference_wall"]
  limits := [
    "The compiler needs no DecidableEq V, inhabited V, structural mixer law or probability Law. Its finite port indices supply their own decidable equality.",
    "Port count is neither source count nor statistical independence. Arbitrary T may duplicate values; distinct occurrences establish no physical no-cloning claim.",
    "Shared histories require jointly retained arrays or source certificates. Overwritten inputs are not silently reused, and the compiler supplies no input-array availability.",
    "Legal reference generation, physical composition, actualization, particle ontology and matter applicability remain open."] }

def nativeRecipeContextRealization : ResearchTask := {
  id := "native_recipe_context_realization"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Fix a finite native wire type, one marked source s and NativeGaussianResponse.Event recipes in its literal vacuum-doubling tower. Every reference occurrence of a finite one-hole Context is an actual recipe in that same tower; the hole is an event e.",
    "A structural mapRefs replaces each reference recipe by amplitude s of that recipe. Use the native scalar mixer, existing real-half event damping, common-level padding and the existing full-recipe comparison circuit; no probability Law is assumed by the amplitude core.",
    "For the separate raw transfer, fix r:WeightFreeRawProbability.RawOperationalData V and arbitrary v:r.Carrier, including null and finite-order references. Define rawEvent by prepared normalized raw evaluation at the recipe sourceAt. Map every context reference recipe by that same rawEvent; complex scalars serve only as existing coefficient certificates, not as new raw carrier structure."]
  conclusions := [
    "Checked law-free finite recipe-context realization constructs an actual event E with amplitude s E = Context.eval mixer (mapRefs (amplitude s) C) (amplitude s e) / 2^referenceCount C.",
    "Induction retains recipe provenance: if the child has k reference occurrences, damp the next reference recipe by 2^k using repeated halfEvent, pad the two full recipes to a common level, use existing comparison middle branches to place both selected amplitudes at scale 1/2 on distinct ports, then append one pair in the required operand order and select the specified output.",
    "The checked normSq readout is the ideal selected-result normSq divided by 4^referenceCount C. For one fixed context, the nonzero common attenuation factor reflects both amplitude equality/inequality and normSq equality/inequality of the corresponding ideal selected results.",
    "The checked raw transfer uses native_output_related, related_mixer context induction and iterated related_half; compiled scalar equality and related_raw_unique yield rawEvent E = halfPower (referenceCount C) (Context.eval r.normalizedOperation (mapRefs rawEvent C) (rawEvent e)). No infinite reference order, positive raw weight, Hilbert premise or probability Law is required.",
    "halfPower is injective by additive map_nsmul and halfPower_two_pow, so the same fixed context reflects raw ideal-target equality and inequality despite its accounted dyadic attenuation.",
    "The separate checked probability corollary retains the existing native Law and uses NativeProbabilityUniqueness.native_probability_eq_normSq. Existing comparison and damping theorems are prerequisites, not new results of this task."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeRecipeContextRealization.lean"
      declarations := [
        "IDT.QMClosure.NativeRecipeContextRealization.mapRefs",
        "IDT.QMClosure.NativeRecipeContextRealization.comparison_blocks",
        "IDT.QMClosure.NativeRecipeContextRealization.exists_halved_mixer",
        "IDT.QMClosure.NativeRecipeContextRealization.exists_realization",
        "IDT.QMClosure.NativeRecipeContextRealization.realization_normSq",
        "IDT.QMClosure.NativeRecipeContextRealization.realization_amplitude_eq_iff",
        "IDT.QMClosure.NativeRecipeContextRealization.realization_amplitude_ne_iff",
        "IDT.QMClosure.NativeRecipeContextRealization.realization_normSq_eq_iff",
        "IDT.QMClosure.NativeRecipeContextRealization.realization_normSq_ne_iff",
        "IDT.QMClosure.NativeRecipeContextRealization.raw_realization_of_scalar",
        "IDT.QMClosure.NativeRecipeContextRealization.exists_correlated_realization",
        "IDT.QMClosure.NativeRecipeContextRealization.halfPower_injective",
        "IDT.QMClosure.NativeRecipeContextRealization.raw_realization_eq_iff",
        "IDT.QMClosure.NativeRecipeContextRealization.raw_realization_ne_iff",
        "IDT.QMClosure.NativeRecipeContextRealization.realization_probability"] }]
  plannedArtifacts := []
  dependencies := ["reference_occurrence_compilation", "native_single_source_reference_wall",
    "native_coherent_scalar_sufficiency", "native_gaussian_probability_selection",
    "raw_native_dyadic_semantics", "weight_free_raw_probability"]
  limits := [
    "The realization is specific to the native scalar mixer and actual same-source recipes. It is not an arbitrary-T lift, amplitude-based witness search, unknown-token processor or supply of fresh unattenuated copies.",
    "Every composition retains full native circuit recipes and ancillary outputs. Syntactic port counting is distinct from the source and history budget.",
    "Raw transfer covers only the normalized operation and source-generated reference recipes. The original raw operation requires its separate evaluator bridge; arbitrary raw-T realization and all raw-reference availability are not established.",
    "Scalar recovery from raw equality is not established: a null reference can collapse distinct coefficient certificates. Algebraic halfPower injectivity supplies neither native amplification nor physical removal of attenuation, and arbitrary response signatures need not reflect raw or scalar distinctions.",
    "Every circuit is finite, but the theorem permits arbitrary finite vacuum extensions. It gives no physical capacity or efficiency bound.",
    "The amplitude, normalized raw-value and normSq equality/inequality reflections are exact; no uniform finite-resolution or noise robustness, probability sampling, actual outcomes, physical reference availability or QM closure follows."] }

def nativeReferenceSeparation : ResearchTask := {
  id := "native_reference_separation"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Fix one marked source and actual native Event recipes in its literal vacuum tower. Existing unit and i/2 preparations supply two fixed reference recipes; the core concerns scalar amplitudes and normSq, with no probability Law.",
    "For each reference amplitude t, aligned_sum_difference retains one actual same-source circuit with distinct selected outputs (z+t)/2 and i*(z-t)/2, together with every ancillary output. Define its contrast as the unrenormalized difference of the two output normSq weights."]
  conclusions := [
    "Checked scalar paired-setting separation: each paired-setting contrast equals Re(z*conj t). The fixed references t=1 and t=i/2 recover Re z and Im z/2, respectively; equality of both contrasts is equivalent to equality of the scalar amplitudes.",
    "The realization uses two settings with four selected weights in total. Each setting retains one circuit and distinct output ports; it does not assume unattenuated joint-array availability or reuse one shared history across the settings.",
    "Negative control: the unit-reference paired setting gives (5/8,1/8) for both a=(1+i)/2 and b=(1-i)/2. The quadrature-reference setting gives (5/16,1/16) for a and (1/16,5/16) for b.",
    "Exact-zero Boolean signatures do not inherit separation: all four test outputs are nonzero for each of the distinct actual amplitudes 1/2 and 1/4.",
    "The separate checked probability-profile corollary retains a supplied native Law and invokes NativeProbabilityUniqueness.native_probability_eq_normSq on the actual selected outputs. A signed contrast is a difference of event probabilities, not a negative event probability."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeReferenceSeparation.lean"
      declarations := [
        "IDT.QMClosure.NativeReferenceSeparation.contrast_identity",
        "IDT.QMClosure.NativeReferenceSeparation.profile_eq_iff",
        "IDT.QMClosure.NativeReferenceSeparation.profile_injective",
        "IDT.QMClosure.NativeReferenceSeparation.pairedSetting_exists",
        "IDT.QMClosure.NativeReferenceSeparation.experiment_weights_eq_iff",
        "IDT.QMClosure.NativeReferenceSeparation.experiment_probabilityProfile_eq_iff",
        "IDT.QMClosure.NativeReferenceSeparation.actual_unit_setting_not_separating",
        "IDT.QMClosure.NativeReferenceSeparation.control_weight_profiles",
        "IDT.QMClosure.NativeReferenceSeparation.actual_zero_profile_not_separating"] }]
  plannedArtifacts := []
  dependencies := ["native_single_source_reference_wall", "native_vacuum_probability_family"]
  limits := [
    "The selected pair is not renormalized: its total need not be 1, and conditioning on that pair would change the contrast identity. No minimality claim for the number of settings or weights is made.",
    "Separation concerns exact scalar normSq profiles of actual same-source recipes. Arbitrary coarse response signatures, physical reference availability and arbitrary-carrier tomography are not established.",
    "The construction lives in concrete scalar native semantics and permits arbitrary finite vacuum extensions. It supplies neither all raw-reference availability nor physical capacity or efficiency bounds.",
    "The recipe-context compiler is independent. Exact equality/inequality is not uniform finite-resolution or noise robustness; probability sampling, actual outcomes, actualization, full contextual completeness and QM upgrades remain outside scope."] }

def nativeRecipeSubstitution : ResearchTask := {
  id := "native_recipe_substitution"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Fix one marked source s and actual native Event recipes in its literal vacuum tower. Let C and D be finite one-hole recipe contexts, e the hole recipe, nC=referenceCount C and nD=referenceCount D; realize denotes the attenuation-accounted construction of native_recipe_context_realization.",
    "Define dampEvent k by k iterations of NativeGaussianResponse.halfEvent, retaining actual same-source circuits with amplitude divided by 2^k. The corrected outer context mapRefs (dampEvent nD) C damps every outer reference occurrence, not only the hole or a selected subset.",
    "For raw transfer use the same normalized r:WeightFreeRawProbability.RawOperationalData V, arbitrary reference v and rawEvent interpretation of all recipes; v may be null or finite order. No infinite reference order, positive weight or probability Law is supplied to the core."]
  conclusions := [
    "Checked attenuation-accounted substitution: the selected amplitudes of realize s (mapRefs (dampEvent nD) C) (realize s D e) and realize s (C.plug D) e are equal. Both equal the ideal nested context result scaled by 2^-(nC+nD).",
    "Checked supporting lemmas establish referenceCount_plug additivity, the needed mapRefs composition and plug identities, and joint context homogeneity when every reference and the hole are scaled together, using concrete mixer homogeneity.",
    "For the same arbitrary r and v, rawEvent_related for both actual recipes and related_raw_unique transfer their selected scalar equality to selected raw equality. This inference needs neither scalar recovery from raw equality nor infinite reference order.",
    "Exact negative control with an actual unit recipe: take C=D=left first hole unit and e=unit. Naive realize s C (realize s D e) has amplitude (3-i)/8 and normSq 5/32; direct plug has amplitude 1/4 and normSq 1/16. Damping the outer reference by nD gives the corrected amplitude 1/4. Both context reference counts are positive in this control; no assertion says every C and D fail.",
    "The separate checked supplied-Law corollary equates selected event probabilities through NativeProbabilityUniqueness.native_probability_eq_normSq. It uses scalar probability selection and does not assert equality of complete prepared arrays."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeRecipeSubstitution.lean"
      declarations := [
        "IDT.QMClosure.NativeRecipeSubstitution.referenceCount_plug",
        "IDT.QMClosure.NativeRecipeSubstitution.context_eval_div",
        "IDT.QMClosure.NativeRecipeSubstitution.corrected_substitution_amplitude",
        "IDT.QMClosure.NativeRecipeSubstitution.corrected_realization_amplitude",
        "IDT.QMClosure.NativeRecipeSubstitution.plugged_realization_amplitude",
        "IDT.QMClosure.NativeRecipeSubstitution.corrected_substitution_raw",
        "IDT.QMClosure.NativeRecipeSubstitution.corrected_substitution_probability",
        "IDT.QMClosure.NativeRecipeSubstitution.naive_unit_substitution_amplitude",
        "IDT.QMClosure.NativeRecipeSubstitution.naive_unit_substitution_normSq",
        "IDT.QMClosure.NativeRecipeSubstitution.plugged_unit_substitution_amplitude",
        "IDT.QMClosure.NativeRecipeSubstitution.plugged_unit_substitution_normSq",
        "IDT.QMClosure.NativeRecipeSubstitution.naive_unit_substitution_fails"] }]
  plannedArtifacts := []
  dependencies := ["native_recipe_context_realization", "reference_occurrence_compilation",
    "raw_native_dyadic_semantics", "native_gaussian_probability_selection"]
  limits := [
    "This task accounts actual recipe attenuation and differs from the existing arbitrary-array compile_plug_selected semantics. Only selected results are equated; levels, circuits, complete retained arrays and histories may differ.",
    "Scalar inequality does not imply raw inequality for all references, since a null reference can collapse distinct scalar coefficients. Arbitrary raw response signatures need not reflect attenuation or the selected scalar distinction.",
    "All recipes use the concrete native mixer and the same source-generated reference sector. Normalized raw semantics requires its separate bridge for interpretation as the original raw operation; arbitrary raw-T realization is not supplied.",
    "No native amplification, unattenuated copying, unknown-token processing, physical reference availability, legal physical-history composition, actualization or QM closure is established. Finite circuits with arbitrary finite vacuum extensions provide no capacity, efficiency, finite-resolution or noise-robustness claim."] }

def referenceProvenanceAndSubstitution : ResearchTask := {
  id := "reference_provenance_and_substitution"
  stage := .openPhysicalBridge
  review := .openObligation
  assumptions := [
    "References, apparatus, controllers and environment must ultimately obey the same native resource and history rules as the systems being modeled."]
  conclusions := []
  checkedEvidence := []
  plannedArtifacts := [
    "Distinguish individually reachable port values from jointly preparable arrays; retain source provenance and alignments on legal composition.",
    "Use the checked reference_occurrence_compilation syntax theorem, which retains reference occurrences and unused outputs; physical availability and shared-history source certificates remain obligations.",
    "Use the checked native_recipe_context_realization and native_reference_separation results for attenuation-accounted finite same-source recipes and exact scalar normSq profiles. Their full retained circuits and ancillary outputs supply no unattenuated reference availability, arbitrary-signature separation or physical controls.",
    "Generate admitted references from native input resources and retained outputs, tracking common frame, alignment and legal history composition without free copying.",
    "Use checked native_recipe_substitution for corrected attenuation-accounted composition of selected scalar and normalized raw results from actual same-source recipes, with its explicit failure of naive unit-reference composition. This is not equality of complete arrays or histories; legal physical continuation composition and native probability-law conditions with apparatus/controller/environment accounting remain open.",
    "Use checked source_local_original_semantics for full-array agreement of original and normalized source-sector evaluation under both diagonal-fixed source and chosen-zero premises, with its exact one-pair/full-array equivalence and unchanged six-field law transport. The global raw square-swap and first-channel mediality laws remain premises; no physical reference availability is supplied.",
    "Use checked response_source_local_probability for response-law/original-quotient-law equivalence without transparency and conditional normalized-law transfer under full contextual diagonal fixedness of both the chosen-zero and source classes, preserving the complete probability field. Arbitrary fixed-reference ResponseEq remains supplied; physical response provenance and availability stay open. The checked response_diagonal_signature_wall shows that bare signature invariance cannot replace these full contextual premises, with a concrete response-law nonuniqueness control.",
    "Use checked response_recipe_context_reflection to compare selected full response classes of actual original recipe-context realizations and ideal original recipe contexts at a common attenuation scale. Both full contextual fixed-class premises and the outer arbitrary-reference ResponseEq remain supplied; this does not establish bare-signature separation or physical reference availability.",
    "Use checked native_recipe_observation_boundary to distinguish reachable recipe observations from arbitrary-reference contextual equivalence: an exact Boolean point-test countermodel agrees on every reachable recipe/compiler output despite distinct full contextual classes, while a separate recipe-dependent exact-zero comparator family separates known recipe amplitudes. Supplied-law transport and canonical consistency remain distinct. No fixed finite observation battery, physical detector, arbitrary-reference availability or unknown-token processing follows.",
    "Use checked response_recipe_comparison as a structural actual-recipe zero-comparison bridge: the quotient algebraic comparison equivalence requires no Law, weight or infinite-order premise, while the individual signature-baseline correctness and sufficient whole-profile theorem retain the additional ComparatorVacuumSound condition. The physical response provenance of that soundness remains open; it is not an inevitable new primitive or a necessary condition for whole-profile completeness.",
    "Use checked native_two_point_observation_control as a nonminimality wall: a concrete exact two-point scalar signature makes the entire recipe comparison profile complete even when individual vacuum-baseline soundness fails. The packaged supplied-law transport preserves all six structural fields and the entire probability field; canonical consistency remains separate. Keep arbitrary-reference contextual equivalence, reachable comparison families and physical detector availability distinct.",
    "Distinguish fixed-context equivalence, common-transformation covariance and ray redundancy; state sector-preservation requirements separately from channel covariance."]
  dependencies := ["port_frame_alignment", "native_single_source_reference_wall",
    "reference_occurrence_compilation", "native_recipe_context_realization",
    "native_reference_separation", "native_recipe_substitution",
    "product_exchange_observation_boundary",
    "native_preparation_naturality", "source_local_original_semantics",
    "response_source_local_probability", "response_diagonal_signature_wall",
    "response_recipe_context_reflection", "native_recipe_observation_boundary",
    "response_recipe_comparison", "native_two_point_observation_control",
    "response_phase_quotient_wall", "coherent_port_ray_boundary", "product_feature_exchange",
    "standing_matter_regime_constraint"]
  limits := [
    "These are analytic physical-boundary requirements, not checked physical claims. Reference generation, alignment and admitted substitution laws remain obligations.",
    "Native wire and port labels track preparation interfaces and origin information, not particle identities or an independently owned object ontology; the single-reference amplitude-port grammar and weighted product composition remain distinct.",
    "Restriction to S-commuting effects does not select eigenstates; sector stability requires preservation and does not follow from mere channel covariance.",
    "Higher-dimensional permutation sectors for N>=3 are not excluded. All matter regimes, physical process availability, sector selection and actualization remain open."] }

def recordWindowStability : ResearchTask := {
  id := "record_window_stability"
  stage := .openPhysicalBridge
  review := .openObligation
  assumptions := [
    "Standing within-world apparatus requirement: record creation, retention and retrieval must ultimately use the same process rules, including controller and environment."]
  conclusions := []
  checkedEvidence := []
  plannedArtifacts := [
    "Specify acquisition, a finite operational retention window, allowed disturbances, retrieval operations and failure criteria with complete apparatus/controller/environment accounting.",
    "Use an explicit pending state when testing a dynamical outcome selector, rather than assuming a total single-label extraction before a record exists."]
  dependencies := ["particle_as_process_result_hypothesis", "standing_matter_regime_constraint",
    "record_marginal_actualization_wall", "equivariant_outcome_selection_wall"]
  limits := [
    "Analytic scope clarification only: on a periodic orbit of one autonomous update, an eventually constant readout was constant throughout that orbit. Finite full-state injective dynamics supplies periodicity; if the initial label differs, a consecutive window of the new label has length at most period minus one.",
    "No standalone recurrence formalization is prioritized: the accepted response law already requires an infinite contextual preparation quotient, and existing finite detector controls already leave physical stability open.",
    "Finite noninjective reset and infinite bijective integer shift separate irreversibility from carrier finiteness. A finite swap followed by identities also creates a permanent readout, showing that autonomous dynamics or explicit controller/clock inclusion is essential.",
    "Finite detector labels, finite configurations with arbitrary amplitude assignments and finite Hilbert dimension are not finite complete state spaces. An observable-quotient recurrence claim needs its own autonomous injective quotient dynamics.",
    "Exact eternal absorption is not the same as finite-window physical stability; neither duplication of record amplitudes nor a designated read-only query supplies retention.",
    "A reversible integer clock with a separately supplied distinguished label can produce and retain a label while respecting relabeling covariance; that control supplies asymmetry and does not select an outcome from a symmetric probability profile.",
    "No actual chosen history, physical persistence times, thermodynamic theorem, energy accounting or matter-regime applicability is established."] }

def normalizedEchoReadoutOrigin : ResearchTask := {
  id := "normalized_echo_readout_origin"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply the global complex carrier, topology, addition, serial multiplication and conjugate reversal, with a continuous nonnegative weight w satisfying w(0)=0, w(1)=1, multiplicativity and conjugation invariance.",
    "Supply every algebraic normalized echo context: w(a)+w(b)=1 implies w(a*conj(a)+b*conj(b))=1. Physical availability of this context coverage remains supplied."]
  conclusions := [
    "Complex inverses give faithfulness. IVT supplies a scalar of weight 1/2; its balanced echo gives w(2)=4. Powers of two and IVT supply every positive real response level.",
    "Common-scalar normalization gives universal echo and the complex star identity gives the parallelogram law. Existing polarization and continuity then select w=Complex.normSq and yield conservation for the supplied native coordinate mixer.",
    "The support indicator satisfies all normalized echoes but is discontinuous and violates the parallelogram law. The continuous quartic weight has every positive real response level and passes all explicitly admitted deterministic echoes while violating full normalized echo and the parallelogram law."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NormalizedEchoReadout.lean"
      declarations := [
        "IDT.QMClosure.NormalizedEchoReadout.WeightLaws.faithful",
        "IDT.QMClosure.NormalizedEchoReadout.WeightLaws.balanced_reference",
        "IDT.QMClosure.NormalizedEchoReadout.WeightLaws.two",
        "IDT.QMClosure.NormalizedEchoReadout.WeightLaws.positive_real_level",
        "IDT.QMClosure.NormalizedEchoReadout.WeightLaws.universal_echo",
        "IDT.QMClosure.NormalizedEchoReadout.WeightLaws.parallelogram",
        "IDT.QMClosure.NormalizedEchoReadout.WeightLaws.weight_eq_normSq",
        "IDT.QMClosure.NormalizedEchoReadout.WeightLaws.native_pair_conservation"] },
    { sourcePath := "Proofs/QMClosure/NormalizedEchoReadoutControls.lean"
      declarations := [
        "IDT.QMClosure.NormalizedEchoReadoutControls.support_normalized_echo",
        "IDT.QMClosure.NormalizedEchoReadoutControls.support_discontinuous",
        "IDT.QMClosure.NormalizedEchoReadoutControls.support_parallelogram_fails",
        "IDT.QMClosure.NormalizedEchoReadoutControls.quartic_laws",
        "IDT.QMClosure.NormalizedEchoReadoutControls.quartic_positive_real_level",
        "IDT.QMClosure.NormalizedEchoReadoutControls.deterministic_context_normalized",
        "IDT.QMClosure.NormalizedEchoReadoutControls.deterministic_context_echo",
        "IDT.QMClosure.NormalizedEchoReadoutControls.quartic_parallelogram_fails",
        "IDT.QMClosure.NormalizedEchoReadoutControls.quartic_not_normalized_echo"] }]
  plannedArtifacts := []
  dependencies := ["operational_positive_readout", "mixer_record_naturality"]
  limits := [
    "The global raw weight has w(2)=4. A mathematical scalar witness alone leaves physical context realization open. Carrier, topology, addition, serial multiplication, reversal and global context availability retain physical justification obligations. The single_echo_readout_origin theorem gives a weaker sufficient contract using continuity at one and one actual nondegenerate normalized echo. Absolute minimality and physical availability of that pair remain open.",
    "The direct IVT and algebra argument assumes normalized weight sums and derives norm-square selection. The operational sequence adapter, two-dimensional representation hypotheses and separate unitarity argument remain open under gks_operational_sequence_bridge.",
    "Independent Qraw identification, Born interpretation, detector selection, event actualization, full QM, GR and physical-scale closure remain open."] }

def gksOperationalSequenceBridge : ResearchTask := {
  id := "gks_operational_sequence_bridge"
  stage := .openPhysicalBridge
  review := .openObligation
  assumptions := [
    "Literature context only: Goyal, Knuth and Skilling, arXiv:0907.0909v3, sections II-III, equations 27-34. No operational sequence adapter has been accepted."]
  conclusions := []
  checkedEvidence := []
  plannedArtifacts := [
    "Specify the sequence carrier and composability, coherent coarsening distinct from forgetting records, last-atomic-outcome sufficiency, repeatability and operational reversal.",
    "Supply normalized-context availability, global amplitude extension and readout factorization through exact artifacts. Retrieve the precise two-dimensional Aczel-Hosszú hypotheses before using the representation theorem."]
  dependencies := ["normalized_echo_readout_origin", "operational_positive_readout",
    "mixer_record_naturality"]
  limits := [
    "A real-pair representation does not supply ordered-pair history readout; dense preparation means do not supply sequence amplitudes; raw F squared equal to swap does not supply history reversal; classical output independence does not supply temporal closure. A scalar representation theorem does not substitute for the two-dimensional hypotheses.",
    "C2 equation 31 in isolation admits dual-number reversal-identity and sign counterexamples; these are not countermodels to the full paper. A full real-pair globally continuous probability extension may repair C2, but that route is unformalized. Unitarity remains separate in section IV, page 13.",
    "Literature is not Lean proof. No public invalidity or novelty claim, Born interpretation, independently specified Qraw identity, event actualization, full QM, GR or calibrated-scale closure is recorded."] }

def internalReferenceSupportOrigin : ResearchTask := {
  id := "internal_reference_support_origin"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Order theorem: a preorder and a coordinatewise-monotone two-port F with F squared equal to swap and every raw diagonal fixed.",
    "Statistical support theorem: probability preparations, one common kernel with exact full-product covariance, raw square-swap and fixed diagonals. An internal reference K(x0) dominates every preparation; the reference-factorization adapter obtains this one-way absolute continuity from finite reference KL."]
  conclusions := [
    "Every preorder comparison reverses. On a partial order, comparable elements are equal. Common-kernel covariance preserves the preparation absolute-continuity preorder, so the internal reference connects every pair in both directions.",
    "Every common effect has responses that are all zero, all one, or pointwise strictly between zero and one.",
    "A Bool-squared fair/point-law routing control retains one common channel, full covariance, square-swap, internal reference preservation and finite reference KL while moving a diagonal and having infinite pairwise KL. A five-label control retains fixed diagonals and pair-dependent full covariance with finite internal-reference KL, but has infinite pairwise KL and admits no common channel."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/TransparentSwapRootOrderWall.lean"
      declarations := [
        "IDT.QMClosure.TransparentSwapRootOrderWall.reverse_le",
        "IDT.QMClosure.TransparentSwapRootOrderWall.eq_of_le"] },
    { sourcePath := "Proofs/QMClosure/InternalReferenceSupportBridge.lean"
      declarations := [
        "IDT.QMClosure.InternalReferenceSupportBridge.product_absolutelyContinuous_iff",
        "IDT.QMClosure.InternalReferenceSupportBridge.covariance_preserves_absolutelyContinuous",
        "IDT.QMClosure.InternalReferenceSupportBridge.reverse_absolutelyContinuous",
        "IDT.QMClosure.InternalReferenceSupportBridge.ReferenceContract.mutually_absolutelyContinuous",
        "IDT.QMClosure.InternalReferenceSupportBridge.ReferenceContract.acceptance_trichotomy"] },
    { sourcePath := "Proofs/QMClosure/InternalReferenceProcessControls.lean"
      declarations := [
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutFixedDiagonal.contract",
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutFixedDiagonal.reference_internal",
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutFixedDiagonal.diagonal_not_fixed",
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutFixedDiagonal.diagonal_law_moves",
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutFixedDiagonal.infinite_pairwiseKL",
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutCommonChannel.operation_square",
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutCommonChannel.operation_diagonal",
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutCommonChannel.reference_preserving",
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutCommonChannel.covariance",
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutCommonChannel.finite_referenceKL",
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutCommonChannel.infinite_pairwiseKL",
        "IDT.QMClosure.InternalReferenceProcessControls.WithoutCommonChannel.no_common_channel",
        "IDT.QMClosure.InternalReferenceProcessControls.GaussianWitness.pointedModel",
        "IDT.QMClosure.InternalReferenceProcessControls.GaussianWitness.preparations_distinct"] }]
  plannedArtifacts := []
  dependencies := ["reference_entropy_factorization_origin", "detector_endpoint_support_wall",
    "classical_statistical_process_bridge"]
  limits := [
    "Mutual absolute continuity alone leaves log integrability open. The full pairwise-entropy bridge is recorded separately. The endpoint conclusion is pointwise strict interiority; a uniform positive margin requires its own premise.",
    "The controls separate premises of the stronger support and pairwise-entropy result. These controls make no minimality claim for the earlier factorization theorem.",
    "Independent Qraw identification, Born interpretation, detector selection, event actualization, full QM, GR and physical-scale closure remain open."] }

def internalReferencePairwiseEntropyFrontier : ResearchTask := {
  id := "internal_reference_pairwise_entropy_frontier"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Retain the arbitrary-measurable reference-entropy factorization contract: probability preparations, one common Markov kernel, invariant reference product, finite KL(K(x)||alpha), raw square-swap and exact marginal covariance. Add alpha=K(x0) and fixed raw diagonals.",
    "The alternate PointedContract supplies full product covariance, probabilities, a chosen reference preparation, one-way finite KL to that preparation, raw square-swap, fixed diagonals and one common Markov channel. Reference-product invariance follows at the fixed reference diagonal."]
  conclusions := [
    "Mutual absolute continuity and the affinity data-processing cycle yield exact likelihood transport on the actual stationary coupling alpha squared compProd channel, whose two marginals are alpha squared.",
    "Finite almost-everywhere log relations require no L1 premise. Product-coordinate separation makes Q_x=g_(a squared x)-g_(a x)+g_x/2 constant. Combining three Q relations gives the actual fourth raw iterate g_(a to the fourth x)=-g_x/4+c, with a(x)=fst(F(x,x0)).",
    "Density normalization yields an Integrable reciprocal-quarter moment. Forward density integrability and Young's entropy inequality with supplied finite reference KL yield cross-log integrability and finite directed KL(K(x)||K(y)) for every pair.",
    "The final adapter derives every helper premise from the original data. Both interfaces construct the existing classical statistical process contract with its all-pair finiteEntropy field."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/LikelihoodTransportSaturation.lean"
      declarations := [
        "IDT.QMClosure.LikelihoodTransportSaturation.ae_eq_condExp_of_integral_sqrt_eq",
        "IDT.QMClosure.LikelihoodTransportSaturation.affinity_markov_le",
        "IDT.QMClosure.LikelihoodTransportSaturation.likelihood_markov_of_affinity_eq"] },
    { sourcePath := "Proofs/QMClosure/LogDensityProcessTransport.lean"
      declarations := [
        "IDT.QMClosure.LogDensityProcessTransport.ae_sum_eq_zero_separates",
        "IDT.QMClosure.LogDensityProcessTransport.Contract.origin_sum",
        "IDT.QMClosure.LogDensityProcessTransport.Contract.origin_quadratic_constant",
        "IDT.QMClosure.LogDensityProcessTransport.Contract.reciprocal_log_witness"] },
    { sourcePath := "Proofs/QMClosure/RelativeEntropyMomentTransfer.lean"
      declarations := [
        "IDT.QMClosure.RelativeEntropyMomentTransfer.integrable_exp_abs_llr_quarter",
        "IDT.QMClosure.RelativeEntropyMomentTransfer.integrable_llr_of_reciprocal_quarter_moment",
        "IDT.QMClosure.RelativeEntropyMomentTransfer.llr_sub_of_equivalent_reference",
        "IDT.QMClosure.RelativeEntropyMomentTransfer.klDiv_ne_top_of_reciprocal_quarter_moment"] },
    { sourcePath := "Proofs/QMClosure/InternalReferenceEntropyBridge.lean"
      declarations := [
        "IDT.QMClosure.InternalReferenceEntropyBridge.ReferenceContract.affinity_saturated",
        "IDT.QMClosure.InternalReferenceEntropyBridge.ReferenceContract.log_transport",
        "IDT.QMClosure.InternalReferenceEntropyBridge.ReferenceContract.logDensityProcess",
        "IDT.QMClosure.InternalReferenceEntropyBridge.ReferenceContract.reciprocal_quarter_moment",
        "IDT.QMClosure.InternalReferenceEntropyBridge.ReferenceContract.finite_pairwise_entropy",
        "IDT.QMClosure.InternalReferenceEntropyBridge.ReferenceContract.classicalProcess",
        "IDT.QMClosure.InternalReferenceEntropyBridge.PointedContract.referenceFactorization",
        "IDT.QMClosure.InternalReferenceEntropyBridge.PointedContract.finite_pairwise_entropy",
        "IDT.QMClosure.InternalReferenceEntropyBridge.PointedContract.classicalProcess"] }]
  plannedArtifacts := []
  dependencies := ["internal_reference_support_origin", "reference_entropy_factorization_origin",
    "classical_statistical_process_bridge"]
  limits := [
    "Helper transport and reciprocal-moment hypotheses are discharged by the final adapter. The argument uses genuine Integrable bounds and finite almost-everywhere relations. Arbitrary measurable outcome carriers are supported through the common forward kernel.",
    "The existing process interfaces retain their definitions. The new pointed interface derives their all-pair finite entropy from its supplied one-way reference entropy.",
    "At the reference preparation g_x0=0 expresses density ratio one. Detector acceptance, the echo algebra's zero input and an identification of statistical with echo readout retain separate obligations.",
    "Physical Qraw identification, Born interpretation, detector selection, event actualization, tensor structure, dynamics, physical scales, full QM and GR remain open."] }

def singleEchoReadoutOrigin : ResearchTask := {
  id := "single_echo_readout_origin"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply the global complex algebra and a raw real weight w with global multiplicativity and continuity at one.",
    "Supply one actual pair of nonzero complex inputs a,b with w(a)+w(b)=1 and w(a*conj(a)+b*conj(b))=1."]
  conclusions := [
    "The supplied laws and one nondegenerate normalized echo imply w=Complex.normSq. The zero and unit values, nonnegativity, strict positivity away from zero and conjugation invariance follow from these premises.",
    "The function z maps to log(w(exp(z))) is additive and continuous at zero, hence real-linear. The complex exponential's 2*pi*i period removes the imaginary coefficient and gives a radial character. The single nondegenerate normalized echo selects exponent two.",
    "Weight selection from one supplied balanced witness c with w(c)=1/2 and echo(c,c) is a corollary. The existing global WeightLaws and all-normalized-pairs echo package supplies such a witness through its balanced-reference lemma. Raw response conservation follows for the supplied native coordinate mixer.",
    "The norm-square control has an actual nonzero balanced witness. The continuous quartic weight passes a deterministic normalized echo while differing from norm square, and it has an actual half-response branch whose balanced echo response is four. The support indicator is continuous at one and satisfies every normalized echo, while having no nondegenerate normalized pair."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/SingleEchoReadout.lean"
      declarations := [
        "IDT.QMClosure.SingleEchoReadout.one_of_normalized_pair",
        "IDT.QMClosure.SingleEchoReadout.zero_of_normalized_pair",
        "IDT.QMClosure.SingleEchoReadout.exp_weight_pos",
        "IDT.QMClosure.SingleEchoReadout.exp_weight_character",
        "IDT.QMClosure.SingleEchoReadout.radial_weight_character",
        "IDT.QMClosure.SingleEchoReadout.weight_eq_normSq_of_pair",
        "IDT.QMClosure.SingleEchoReadout.weight_eq_normSq_of_balanced_echo",
        "IDT.QMClosure.SingleEchoReadout.weight_eq_normSq_of_normalized_echo",
        "IDT.QMClosure.SingleEchoReadout.native_pair_conservation"] },
    { sourcePath := "Proofs/QMClosure/SingleEchoReadoutControls.lean"
      declarations := [
        "IDT.QMClosure.SingleEchoReadoutControls.normSq_nondegenerate_echo",
        "IDT.QMClosure.SingleEchoReadoutControls.normSq_retained_laws",
        "IDT.QMClosure.SingleEchoReadoutControls.quartic_deterministic_control",
        "IDT.QMClosure.SingleEchoReadoutControls.quartic_balanced_echo_four",
        "IDT.QMClosure.SingleEchoReadoutControls.support_continuousAt_one",
        "IDT.QMClosure.SingleEchoReadoutControls.support_control"] }]
  plannedArtifacts := []
  dependencies := ["normalized_echo_readout_origin", "gks_operational_sequence_bridge"]
  limits := [
    "The global complex algebra, global multiplication and continuity at one remain supplied. The witness is an actual pair of mathematical carrier points with exact normalization and echo. Its physical admission remains an operational obligation. The weaker sufficient condition leaves absolute minimality open.",
    "The raw weight is global and can exceed one, with w(2)=4. The native coordinate mixer remains supplied. Standard complex analysis and real linearity establish the conditional mathematical selection theorem.",
    "A discontinuous full-complex radial Hamel construction remains analytic with empty checked evidence. The rational-carrier controls under rational_finite_readout_nonuniqueness retain their stated domain.",
    "Physical Qraw identification, Born interpretation, detector selection, event actualization, spectral and Hilbert representation, tensor structure, dynamics, physical scales, full QM and GR remain open."] }

def boundedLikelihoodProcessRigidity : ResearchTask := {
  id := "bounded_likelihood_process_rigidity"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply probability preparations on an arbitrary measurable outcome carrier, one raw operation with F squared equal to swap and every raw diagonal fixed, and one common Markov channel satisfying exact full product covariance for every raw pair. For the compared preparations supply a finite positive constant C with P(x)<=C*P(y) as measures.",
    "The finite atomic internal-reference consequence additionally supplies P(y) as a finite sum of Dirac measures with positive finite NNReal weights and absolute continuity of every preparation with respect to P(y). The upper density-bound and essential-endpoint corollaries explicitly assume absolute continuity for the compared pair."]
  conclusions := [
    "One-way bounded domination implies equality of preparation measures. Under the supplied full process contract bounded domination is equivalent to measure equality. Distinct preparation labels may still denote the same measure.",
    "Products, a common kernel and probability marginals preserve the bounded-domination preorder. Transparent square-swap reversal gives reverse domination. The component of preparations bounded by an individual finite multiple of P(y) is closed under the raw operation. Two-sided bounds derive finite relative entropy, bounded log likelihood and log integrability, then instantiate the existing pointed and log-transport contracts.",
    "Sharp finite almost-everywhere log bounds have additive widths for independent-coordinate sums. Transported log relations give equal half-widths for the two origin branches. Four actual a-iterations scale width by 1/16, while the reciprocal-log identity scales it by 1/4. Finite elimination forces zero width, and normalization identifies the probability measures.",
    "An individual finite positive upper RN density bound forces equality when absolute continuity covers the preparation measure. A positive finite lower RN density bound forces equality even when a singular part is initially allowed. Distinct absolutely continuous preparation measures have reference-essential density supremum infinity and infimum zero.",
    "An explicitly finite atomic internal reference dominating every preparation forces the family of preparation measures constant on an arbitrary measurable carrier. Its proof constructs a finite upper RN density bound for each preparation separately.",
    "Two finite omission controls exhibit a preparation bounded by four times its internal reference and distinct from it. One omits fixed raw diagonals while retaining the common-channel covariance laws. The other retains fixed diagonals and pair-dependent covariance while excluding any one common channel."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/BoundedLogProcessRigidity.lean"
      declarations := [
        "IDT.QMClosure.BoundedLogProcessRigidity.SharpBounds.exists_of_bounded",
        "IDT.QMClosure.BoundedLogProcessRigidity.SharpBounds.width_productSum",
        "IDT.QMClosure.BoundedLogProcessRigidity.Contract.ae_constant_of_individually_bounded"] },
    { sourcePath := "Proofs/QMClosure/BoundedDominationProcess.lean"
      declarations := [
        "IDT.QMClosure.BoundedDominationProcess.Contract.reverse_boundedDom",
        "IDT.QMClosure.BoundedDominationProcess.Contract.operation_closed",
        "IDT.QMClosure.BoundedDominationProcess.rnDeriv_bounds",
        "IDT.QMClosure.BoundedDominationProcess.integrable_llr_reference",
        "IDT.QMClosure.BoundedDominationProcess.integrable_llr_preparation",
        "IDT.QMClosure.BoundedDominationProcess.Contract.component_finiteReferenceEntropy",
        "IDT.QMClosure.BoundedDominationProcess.Contract.pointedComponent",
        "IDT.QMClosure.BoundedDominationProcess.Contract.logDensityProcess"] },
    { sourcePath := "Proofs/QMClosure/BoundedLikelihoodProcessRigidity.lean"
      declarations := [
        "IDT.QMClosure.BoundedLikelihoodProcessRigidity.Contract.eq_of_le_smul",
        "IDT.QMClosure.BoundedLikelihoodProcessRigidity.Contract.boundedDom_iff_eq",
        "IDT.QMClosure.BoundedLikelihoodProcessRigidity.Contract.not_boundedDom_of_ne"] },
    { sourcePath := "Proofs/QMClosure/BoundedLikelihoodProcessControls.lean"
      declarations := [
        "IDT.QMClosure.BoundedLikelihoodProcessControls.WithoutFixedDiagonal.omission_control",
        "IDT.QMClosure.BoundedLikelihoodProcessControls.WithoutCommonChannel.omission_control"] },
    { sourcePath := "Proofs/QMClosure/BoundedLikelihoodReferenceCorollaries.lean"
      declarations := [
        "IDT.QMClosure.BoundedLikelihoodReferenceCorollaries.Contract.eq_of_ae_upper_rnDeriv",
        "IDT.QMClosure.BoundedLikelihoodReferenceCorollaries.Contract.eq_of_ae_positive_lower_rnDeriv",
        "IDT.QMClosure.BoundedLikelihoodReferenceCorollaries.Contract.essential_density_endpoints_of_ne",
        "IDT.QMClosure.BoundedLikelihoodReferenceCorollaries.exists_bound_rnDeriv_of_finite_atomic",
        "IDT.QMClosure.BoundedLikelihoodReferenceCorollaries.Contract.constant_of_finite_atomic_reference"] }]
  plannedArtifacts := []
  dependencies := ["internal_reference_support_origin",
    "internal_reference_pairwise_entropy_frontier"]
  limits := [
    "The probability family, raw square-swap and fixed-diagonal operation, one common Markov channel and exact full product covariance remain supplied. Finite KL and log integrability follow inside the closed component. Bounds may depend on the pair and on the component member.",
    "The essential extrema describe almost-everywhere bounds and may be unattained. The upper-bound theorem uses absolute continuity to account for the whole preparation measure. The positive lower-bound theorem accepts an initially singular part. The finite atomic consequence includes absolute continuity of every preparation with respect to the internal reference and requires only a measurable-space structure on the carrier.",
    "The two controls isolate fixed diagonal and common-channel omissions only. Full assumption minimality remains open. The existing supplied NativeGaussianStatisticalProcess.model provides the process fields with an injective preparation family and retains its supplied Gaussian semantics.",
    "Application to physical records requires their own exact covariance and full-carrier process closure. Physical Qraw identification, Born interpretation, detector selection, event actualization, spectral and Hilbert representation, tensor structure, dynamics, physical scales, full QM and GR remain open."] }

def rationalFiniteReadoutNonuniqueness : ResearchTask := {
  id := "rational_finite_readout_nonuniqueness"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply the rational Gaussian carrier Q x Q with named multiplication, conjugation and unit, and the norm N(a,b)=a^2+b^2.",
    "Let S be any prescribed finite set of evaluated carrier points. Comparisons with N on S use exact equality."]
  conclusions := [
    "For every finite S the prime construction selects p>2 greater than the absolute norm numerators and positive norm denominators of every point in S, so those norms have zero p-adic valuation.",
    "The rational weight Wp(z)=N(z)*p^v_p(N(z)), using integer powers and then cast to real values, is globally multiplicative and nonnegative, has Wp(0)=0 and Wp(1)=1, and is invariant under conjugation. It agrees with N at every point of S.",
    "The actual nonzero balanced input c=(1/2,1/2) has Wp(c)=1/2 and Wp(c*conj(c)+c*conj(c))=1. Yet Wp((p,0))=p^4 differs from N((p,0))=p^2.",
    "The fixed prime-seven prototype has W7((7,0))=2401 while N((7,0))=49. The sequence (1+7^(-(n+1)),0) converges to the unit in the inherited Euclidean topology while its W7 values tend to zero, proving failure of continuity at the unit.",
    "For every finite set of evaluated points, one weight in this algebraic family agrees with norm square on that set and differs elsewhere. Every fixed finite list of precomputed circuit nodes can be included in that set."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RationalEchoRegularityControl.lean"
      declarations := [
        "IDT.QMClosure.RationalEchoRegularityControl.weightAt_multiplicative",
        "IDT.QMClosure.RationalEchoRegularityControl.weightAt_zero",
        "IDT.QMClosure.RationalEchoRegularityControl.weightAt_one",
        "IDT.QMClosure.RationalEchoRegularityControl.weightAt_nonnegative",
        "IDT.QMClosure.RationalEchoRegularityControl.weightAt_conjugation",
        "IDT.QMClosure.RationalEchoRegularityControl.balanced_ne_zero",
        "IDT.QMClosure.RationalEchoRegularityControl.weightAt_balanced",
        "IDT.QMClosure.RationalEchoRegularityControl.balanced_normalizationAt",
        "IDT.QMClosure.RationalEchoRegularityControl.balanced_echoAt",
        "IDT.QMClosure.RationalEchoRegularityControl.weightAt_real_prime",
        "IDT.QMClosure.RationalEchoRegularityControl.real_prime_fourth_ne_square",
        "IDT.QMClosure.RationalEchoRegularityControl.valuation_of_height_lt",
        "IDT.QMClosure.RationalEchoRegularityControl.finite_readout_wall",
        "IDT.QMClosure.RationalEchoRegularityControl.weight_real_seven",
        "IDT.QMClosure.RationalEchoRegularityControl.nearUnit_tendsto_gone",
        "IDT.QMClosure.RationalEchoRegularityControl.weight_nearUnit_tendsto_zero",
        "IDT.QMClosure.RationalEchoRegularityControl.weight_not_continuousAt_gone",
        "IDT.QMClosure.RationalEchoRegularityControl.rational_balanced_echo_control"] }]
  plannedArtifacts := []
  dependencies := ["single_echo_readout_origin", "gks_operational_sequence_bridge"]
  limits := [
    "The prime p depends on the prescribed finite S, and each selected weight has its own disagreement point. The theorem quantifies over finite sets of carrier points. Fixed finite circuit nodes can be represented by such a set.",
    "The rational Gaussian carrier is countable and retains inherited Euclidean topology with nontrivial convergent sequences. The construction gives a rational-carrier mathematical point witness. Extension to a full complex-carrier countermodel remains a separate obligation.",
    "Universally quantified law schemas, arbitrary infinite algebraic closure and adaptive testing require separate treatment. Statistical accuracy and physical readout implementation require separate evidence.",
    "Physical Qraw identification, Born interpretation, detector selection, event actualization, tensor structure, dynamics, physical scales, full QM and GR remain open."] }

def rationalCountOrderReadoutOrigin : ResearchTask := {
  id := "rational_count_order_readout_origin"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supply the rational Gaussian carrier Q x Q with named multiplication, conjugation and unit, and squared norm N(a,b)=a^2+b^2.",
    "Supply a real raw weight w that is nonnegative everywhere, satisfies w(0)=0 and w(1)=1, is globally multiplicative, and preserves conjugate reversal.",
    "Supply universal adjacent natural-count order. For every natural n, w((n,0))<=w((n+1,0)).",
    "Supply one actual pair of nonzero carrier inputs a,b with w(a)+w(b)=1 and w(a*conj(a)+b*conj(b))=1. The balanced specialization separately supplies one c with w(c)=1/2 and its normalized echo."]
  conclusions := [
    "The supplied weight laws, universal count order and actual arbitrary nondegenerate normalized echo imply w=N on the rational Gaussian carrier. The general theorem accepts unequal branch responses directly. Its assumptions contain no continuity or additional balanced-witness premise.",
    "Natural-count monotonicity and complete multiplicativity determine one logarithmic slope. Positive rational scalar weights satisfy f(q)=exp(alpha*log(q)). Reversal and nonnegativity give w(z)=exp(p*log(N(z))) away from zero with p=alpha/2. The nondegenerate normalized echo selects radial exponent p=1 and scalar exponent alpha=2.",
    "The separate direct balanced route derives f(2)=4. Common dyadic brackets bound both f(n)^k and n^(2*k) between 4^m and 4^(m+1). Uniform bounds by four on both ratio powers and real Archimedean unbounded powers force f(n)=n^2. Integer signs and rational denominators extend the scalar identity; reversal and nonnegativity then give w=N.",
    "For every finite rational Gaussian evaluation set S, there exists a prime p(S)>2 whose existing weightAt family agrees with N on S and retains its actual nondegenerate balanced normalized echo. Its response drops from Wp((p,0))=p^4 to Wp((p+1,0))=(p+1)^2, violating universal count order. The existing prime-family zero, unit, nonnegativity, multiplicativity and conjugation laws retain their original checked status.",
    "The signed norm-valuation and asymmetric Gaussian-prime controls remain analytic future proposals with no machine-checkable evidence. The signed proposal W=N*(-1)^v_5(N) targets failure of nonnegativity while retaining count order and balanced echo. The asymmetric proposal W=N*5^(v_(2+i)-v_(2-i)) targets failure of reversal while retaining positive weights, count order and balanced echo."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/RationalCountOrderReadout.lean"
      declarations := [
        "IDT.QMClosure.RationalCountOrderReadout.nat_log_character",
        "IDT.QMClosure.RationalCountOrderReadout.nat_square_character",
        "IDT.QMClosure.RationalCountOrderReadout.WeightLaws.two_of_balanced_echo",
        "IDT.QMClosure.RationalCountOrderReadout.WeightLaws.scalar_rat_eq_sq",
        "IDT.QMClosure.RationalCountOrderReadout.WeightLaws.weight_eq_normQ_of_balanced_echo",
        "IDT.QMClosure.RationalCountOrderReadout.WeightLaws.scalar_positive_character",
        "IDT.QMClosure.RationalCountOrderReadout.WeightLaws.radial_character",
        "IDT.QMClosure.RationalCountOrderReadout.WeightLaws.weight_eq_normQ_of_pair",
        "IDT.QMClosure.RationalCountOrderReadout.WeightLaws.weight_eq_normQ"] },
    { sourcePath := "Proofs/QMClosure/RationalCountOrderReadoutControls.lean"
      declarations := [
        "IDT.QMClosure.RationalCountOrderReadoutControls.weightAt_count_drop",
        "IDT.QMClosure.RationalCountOrderReadoutControls.prime_weight_not_count_order",
        "IDT.QMClosure.RationalCountOrderReadoutControls.finite_agreement_with_count_violation"] }]
  plannedArtifacts := []
  dependencies := ["single_echo_readout_origin", "rational_finite_readout_nonuniqueness",
    "gks_operational_sequence_bridge"]
  limits := [
    "The two theorem routes and prime-family count-order failure have their displayed proof artifacts. The signed norm-valuation and asymmetric Gaussian-prime controls retain analytic status, with their valuation constructions and all retained-law claims awaiting machine-checkable artifacts.",
    "The conclusion is on Q(i). Extension to the full complex carrier requires additional premises. The analytic discontinuous full-complex character proposal retains its separate unproved status.",
    "Adjacent-count order is an infinite universally quantified schema. The finite-evaluation control chooses a prime depending on the prescribed finite set. The real Archimedean codomain remains supplied in both selection routes.",
    "Physical justification of phase-aligned unit append preserving or increasing raw response and reversal preserving readout remains open. The raw weight is unbounded, and a probability interpretation requires a separate bridge.",
    "The passage from histories to the rational Gaussian carrier, coherent addition, serial multiplication and availability of an actual nondegenerate echo preparation remain open. Physical Qraw identification, Born interpretation, detector selection, event actualization, spectral and Hilbert representation, tensor structure, dynamics, physical scales, full QM and GR remain open."] }

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
  openBridge "physical_process_comparison_calibration"
    "Justify the physical comparison, calibrated coherent reference and pair-port comparison rule used by the raw process route. Classical TV data processing and independent-distribution reference invariance concern a separate supplied comparison. Under the actual native mixer whole-pair TV is preserved, while the sum of marginal Dirac TVs and the sum of squared marginal Dirac TVs each change from one to two on the checked witness. Squared TV also fails ordinary probability-weighted flagged additivity on the supplied control. These results leave the original response Q identification open. Approximate preparation identities require their own comparison-level error control before the robust comparison theorem applies. The checked pair-comparison reconstruction now derives conservation, observed mediality and full squared Hilbert distance from an arbitrary carrier and transparent square-swap gate with a symmetric nonnegative zero-diagonal real comparison satisfying exact universal summed pair nonexpansion. The pair-port sum and all-input process law remain supplied. A separately supplied positive affinity with product-affinity nondecrease under the gate implies this negative-log pair law. Ordinary classical-affinity Gram positivity alone does not supply CND of its negative logarithm or entrywise-root positivity, as the exact three-Bernoulli countercontrol shows. Identifying the original response Qraw(x) with c*delta(x,o) for a positive scale c remains open. In the negative-log specialization this requires Qraw(x)=c*(-log A(x,o)) for a physically justified affinity and scale. The separate ordinary statistical entropy route now derives summed pair comparison nonexpansion from actual KL data processing, independent-product additivity and one state-independent Markov channel with exact full-product covariance on all raw preparation pairs. All ordered preparation KL divergences must be finite. The resulting Jeffreys comparison feeds the existing full-distance reconstruction without an assumed comparison-level contraction law. This comparison is distinct from the generic positive-affinity negative-log route. The original response Qraw and its positive calibration against the new comparison readout remain open. A nonconstant preparation family on one fixed finite outcome space with positive pairwise actual affinity is excluded under the full reconstruction contract, even when the raw carrier is unrestricted. The finite common-channel affinity theorem derives the comparison inequality for that fixed-finite-outcome wall. The checked supplied unit-coordinate-variance Gaussian location family now gives a nonconstant common-channel full-product model, and the chosen soft effect gives an actual binary detector event. Native iid Gaussian characterization, arbitrary-variance and affinity formulas and general effect classification remain analytic and unformalized. Physical availability and selection of preparations, channels and detectors, original-response identification and calibration, actualization, Born, tensor/composite, Bell and physical-scale closure remain open.",
  openBridge "physical_global_residual_invariance"
    "Justify invariance of an exhaustive global no-port-record event when pair-weight conservation is required. At fixed positive exposure and unchanged outside-port contribution the checked normalization identity makes these equivalent. Spectator locality alone supplies no such invariance in the supplied power-response family. Covariance through an effect order automorphism, together with a vacuum-fixed process, makes a detector invariant when that actual detector is identified with the least vacuum-certain effect. The checked full-effect native countercontrol has a least effect, vacuum covariance and reversibility while a different chosen power residual changes. The detector identification remains an additional physical obligation.",
  openBridge "physical_fixed_resource_reference_domain"
    "Specify the physically available carrier, resource budget and reference-preparation domain. Exact half comparison attenuation and a total reference right inverse force a nonnegative comparison to vanish under one upper bound uniform along each reference orbit. Finite depth retains a terminal term, and changing resource carriers does not establish the total single-carrier hypotheses. Resource-indexed preparation domains and budget laws remain open research obligations.",
  openBridge "physical_detector_readout_availability"
    "Justify the physically available detector and exhaustive event domain, including any supplied no-port-record outcome. Normalized Option-valued readouts, basis calibration and preserved spectator ports alone do not establish detector availability, actual events or origins of the supplied complex geometry and quadratic exposure. The full mathematical effect space contains every [0,1]-valued state function, including discontinuous tests. Its least vacuum-certain effect is the exact-vacuum indicator. On the checked three-wire carrier, leastness selects k=1 only within the supplied power-residual family. Physical availability of those effects and identification of the actual detector with that least effect remain open.",
  openBridge "physical_noise_carrier_covariance"
    "Justify the physical noise carrier, admitted distributions and covariance law, including whether the law is exact and which norm and entry lower bounds control its error. On finite carriers strict positivity, row normalization, square-swap, diagonal transparency and exact full product covariance force identical rows, without a uniform-row conclusion. Identity noise retains distinguished rows and exact covariance while having zeros. Positive noisy-identity kernels can have arbitrarily small coefficient and channel-TV covariance defects while distinct rows remain almost maximally TV-distinguishable as their positivity floor tends to zero. Stability under a fixed positive floor remains open. The rational binary-noise theorem applies on any carrier but only to finite-support distributions. These finite-carrier results leave physical continuum and Gaussian-noise selection open. The checked negative-log bridge turns a supplied strictly positive product-affinity nondecrease law into summed pair-comparison nonexpansion. Together with the separate symmetric, diagonal-one and at-most-one affinity laws and transparent square-swap gate, this feeds the conditional full-distance reconstruction. These implications do not construct a physical noise carrier or prove the requisite Markov data-processing, product covariance, detector realization or affinity existence laws. Ordinary affinity PSD is insufficient, as witnessed by the actual three-Bernoulli negative-log and entrywise-square-root countercontrols. Identification of Qraw=c*(-log A(-,o)), the positive scale c and physical applicability remain open. The fixed-finite-outcome affinity wall is separate from the earlier finite-raw-carrier covariance wall. On one fixed finite outcome space, normalized nonnegative rows with all-pairs positive affinity and the full transparent square-swap negative-log reconstruction contract have identical laws for an arbitrary raw carrier. Actual finite stochastic-channel affinity data processing and product multiplicativity derive that contract's comparison law when one common channel has exact full-product covariance on every raw pair. The ordinary statistical entropy route works on arbitrary measurable outcome spaces with one common Markov channel and finite KL for every ordered preparation pair, deriving its Jeffreys comparison law from actual data processing and product additivity. Actual affinity data processing and product multiplicativity on arbitrary measurable outcome spaces remain unformalized. The finite-KL entropy route leaves the weaker positive-affinity route open, and the checked stochastic-affinity adapter covers finite outcome spaces only. Neither route justifies the physical preparation family or channel covariance. The checked supplied unit-coordinate-variance Gaussian location family now gives a nonconstant common-channel full-product model, and the chosen soft effect gives an actual binary detector event. Native iid Gaussian characterization, arbitrary-variance and affinity formulas and general effect classification remain analytic and unformalized. Physical availability and selection of preparations, channels and detectors, original-response identification and calibration, actualization, Born, composites, Bell and physical scales remain open.",
  openBridge "physical_raw_root_medial_all_input_closure"
    "Physically justify the raw root, exact medial law and closure over all inputs. The checked network equivalence identifies mediality with full row/column layer commutation under square-swap. The checked four-state control satisfies square-swap, diagonal transparency, declared-reference balance and all six raw probability kinds, yet violates that network law in an actual five-wire preparation. Mere disjoint-support locality or one balanced reference splitter cannot replace overlapping-network interchange. The checked continuous nonlinear complex mixer also retains exact native vacuum outputs, joint complex homogeneity, transparency, square-swap and squared-norm conservation while violating mediality and yielding a different probability from the native interpretation of the same actual word. These regularity and balance conditions therefore do not supply the missing interchange law.",
  openBridge "real_archimedean_readout_codomain"
    "Justify the real Archimedean readout codomain rather than silently treating it as derived.",
  openBridge "probability_actualization"
    "Actualization remains open: justify or explicitly supply actual-event complement/refinement laws on a rich shared real-weight domain, or noncontextual partially additive probabilities on an adequately rich effect domain with matched-state calibration. The accepted conditional scalar, full-effect, dyadic-domain and reconstructed-record probability theorems do not establish physical event laws, availability or calibration. Distinct bridges remain: joint accounting/additivity for physically admitted cross-context sums, and availability/order saturation supplying every operator-admissible sum and required comparison event. The checked three-context control isolates failure of joint accounting even for admitted sums. The checked generated-cone control isolates missing positive-order saturation despite global coordinate additivity, real mixing and normalization of every supplied normalized cone-valued family; its 17/16 value belongs to an excluded mathematical sum. Neither control establishes physical event availability or an actual outcome generator. The checked native-mixer finite exclusion additionally rejects the old cone assignment under its explicit real-mixture extension assumptions. The independently reviewed group/port route awaits formalization. Two-ancilla coordinate completion, abstract dyadic-midpoint linearization and nonidentity of every positive power of one exact native word are checked mathematical results. They do not close the analytic group-classification route. The native wire-effect adapters, rational span and unique rational readout under supplied zero/midpoint/domain-membership laws are checked. The checked eight-event control is nonnegative on their nonnegative finite rational combinations but assigns -1/128 to an explicit positive contraction. Those finite-span and eight-event results alone do not establish all-circuit positivity, global state positivity, a density-matrix theorem or a physically generated full event domain. The checked conditional attenuation route now supplies exact finite native circuit adapters with retained ancillary leakage, family-based rational span and basis-calibrated selection: all-depth family positivity plus normalization, nonnegative diagonals and calibration select ell(v)=v_00 on all rational coordinates, with p agreeing on its supplied domain D. This selected pure extension is mathematically positive; general mixed-state reconstruction and agreement of p outside D do not follow. The checked universal finite-cutoff countermodel passes all four family bounds through any chosen M yet fails at E_6(M+1), separating finite testing from the universal all-depth hypothesis. Physical native availability at arbitrarily large fresh-wire widths, coordinate noncontextuality, classical midpoint event/accounting laws and calibration remain supplied. The checked contextual-probability control leaves native dynamics unchanged: its normalized squared-structural-weight assignment obeys calibration, output permutations, inert vacuum padding, full-process equivalence and syntactic fair mixtures, yet the exact three-port witness has identical all-input selected amplitudes and probabilities 1/2 versus 2/3. No function of the deterministic selected-weight profile reproduces this assignment on all native circuits. It does not descend to the coordinate-domain event law. Spectator-output locality, deterministic all-input profile sufficiency and mixture-event profile sufficiency remain distinct, and probability-preserving profile descent is still a supplied bridge. The checked raw normalized-operation/scalar circuit adapter uses only the Hilbert output constructed from RawOperationalHilbert.Data: the same finite syntax preserves a supplied common-reference feature relation, and a raw basis input has selected weight normSq(scalar output)*W(reference), including null references. Relative weights require W(reference)>0. Physical normalization control, copying, arbitrary raw preparation availability and probability laws remain separate open bridges. The checked conditional native event-probability adapter supplies image factorization, the explicit zero/total/basis/attenuation/fair-mixture grammar, independent all-input structural profiles and transfer to the basis formula under supplied ProbabilityLaw. Its checked downstream canonicalProbabilityLaw at basis input establishes mathematical nonemptiness; probability functions are extensionally unique on the certified grammar and every law has [0,1] bounds. The witness is not a premise of selection and asserts no law existence on arbitrary physical event domains. The contextual control, raw scalar adapter and event-probability adapter are checked conditional results; physical justification of full-profile probability sufficiency, event availability, fair-mixture accounting and matched calibration remains open. The checked three-wire matrix classification and actual-circuit adapter transfer supplied post-T_12 spectator locality and complete evaluated-map invariance to deterministic full-input selected-profile sufficiency. The checked compressed-input real-readout control separates that conclusion from compressed-profile sufficiency for generic readouts. This result is restricted to three wires and does not replace the attenuation premise across unbounded widths, vacuum compression or classical mixtures. The checked Gaussian denominator descent now supplies actual native reduction and synthesis for every legal three-vector. The checked matrix adapter realizes a three-by-three matrix under explicit unitary, uniform-vector and fourth-root determinant invariants with a dyadic first column. Its width-four locality consequence remains a separate pending step. A checked six-wire circuit countermodel shows that sum and norm alone do not imply unrestricted vector synthesis; the wider through-five synthesis analysis remains unchecked. The checked scalar-residue three-wire law is nonnegative, normalized, basis calibrated and invariant under equal prepared states, equal selected source amplitudes, spectator outputs and source-fixing prefixes. Its actual Gaussian dyadic adapter makes it a countermodel on every finite native three-wire circuit. It differs from squared-amplitude readout and assigns fair-mixture probabilities three quarters and zero to an explicit equal all-input profile pair. This separates deterministic profile sufficiency from mixture-profile sufficiency at fixed width three. The checked finite four-wire extension contradiction excludes any extension matching three concrete padding values while retaining prepared-state equality, spectator locality, normalization and nonnegativity. Independently of residue calibration, adding output covariance bounds one explicit attenuation probability by one third; it does not select one quarter. The checked stable-spectator orbit obstruction excludes connecting two explicit equal-amplitude preparations while leaving the selected output untouched, even with arbitrary finite zero padding. It is not a probability countermodel. The checked all-width probability-family contract implies zero probability for zero amplitude and basis-state calibration. Actual binary native circuits, phase-fibre counting and an Archimedean bound now establish exact probability halving for every literal vacuum split, without probability continuity, scalar sufficiency or mixture-profile sufficiency. Finite depth alone supplies an explicit deviation bound; the theorem retains the global family contract. The checked coherent-copy adapter now establishes same-source, same-wire-type scalar-amplitude sufficiency without adding a Law field. Actual disjoint-block commutation, internal-zero halving and equal-scale four-branch comparison supply that result. Separate checked algebra classifies normalized rotation-invariant Gaussian integer responses satisfying the parallelogram identity, and a checked syntax induction gives Gaussian-dyadic numerators for every actual native output. The checked Gaussian numerator response uses actual padded, attenuated and mixed native events; its witness-independent probability satisfies the required normalization, phase and parallelogram laws. The checked final transfer selects the squared amplitude for every actual finite native basis-prepared output under the six-field all-width Law and gives extensional uniqueness of its probability field. The canonical quadratic Law is only a separate consistency witness. A checked hyperreal countermodel retains the six structural conditions but has an exact nonzero infinitesimal halving defect, excluding an unrestricted ordered-field replacement of the probability codomain. These results establish conditional uniqueness on the native grammar; they do not derive Law from IDT primitives, supply physical actual outcomes or close the original physical Born/QM obligations. The checked additive Archimedean probability-carrier adapter now transfers all six fields through a normalized additive order embedding, establishes conditional uniqueness without a field or carrier-completeness premise, and gives an intrinsic additive Gaussian-denominator identity. It does not assert Law existence for every carrier or weaken earlier real-valued raw-weight assumptions. Checked exact Gaussian-dyadic semantics on the reconstructed raw carrier now turns scalar prepared-state equality into literal raw prepared-state equality without feature injectivity or positive reference weight. Its checked RawLaw consumer selects the native probabilities, establishes their extensional uniqueness and gives absolute weight agreement, with division only for a positive reference weight. Existence of RawLaw for arbitrary references is not established by that conditional selection; the six probability fields remain supplied. Both adapters concern the reconstructed normalized operation, which may differ from the original raw gate. The checked RawLaw existence theorem now identifies its exact consistency condition: the chosen reference has infinite additive order, equivalently its Gaussian action is injective. Positive reference weight suffices; the literal zero reference is excluded. A separate checked original-gate countermodel satisfies the raw square-swap, mediality and positive-weight contracts yet admits a continuum of laws with all six analogous all-width fields. Its actual three-gate witness separates two strictly positive alternatives from the supplied weight ratio. Thus normalized-only uniqueness cannot be transferred unrestrictedly to the original gate. The checked weight-free facade now needs only a chosen zero, raw square-swap and global first-channel mediality before the unchanged probability contract: zero auxiliary weight supplies the old facade, and erasure gives an equivalence of probability laws with identical literal raw arrays. Explicit diagonal transparency identifies normalized and original semantics in that special case. The checked affine diagonal decomposition retains the null displacement, supplies a fixed null center and an additive product of orthogonal sign subgroups, and identifies the original operator with opposite normalized actions plus its displacement. It does not classify all probabilities or supply those transformations physically. The checked four-coordinate mixed-control countermodel retains nonuniqueness even with original and normalized pair gates plus unary outer-sector exchange, including strengthened locality for every supplied generator and actual use of the extra swap in the witness. Further internal multiplicity remains. These are named-control exclusions, not a no-go result for every possible additional operation. The checked native premise-independence artifact now matches the six scalar Law fields exactly and supplies, for each omitted field, an all-width assignment satisfying the other five. This is logical irredundance of that contract, not physical inevitability or a global minimality theorem. The checked raw-network control separately shows that its own six raw-semantic probability fields plus square-swap, transparency and one balanced reference do not imply mediality or the standard native process outputs. These ingredients supply no physical availability, actual probability law, universal circuit realization or probability-limit bridge.",
  openBridge "physical_state_process_completeness"
    "Justify physically available completion states and processes.",
  openBridge "continuous_dynamics"
    "Close continuous dynamics without importing the desired quantum dynamics.",
  openBridge "tensor_local_tomography_bell"
    "Close tensor/composite, local-tomography and Bell obligations.",
  openBridge "physical_scales"
    "First-principles hbar, G and alpha remain unresolved; calibrated anchors do not close them.",
  openBridge "coherent_preparation_ray_interface"
    "Native coherent preparations retain relative phase and unnormalized weight relative to the declared grammar; they are not identified with isolated physical rays. Physical port pairing requires a coherent-preparation lift carrying relative amplitude and phase beyond two independently unknown rays. Specify physical states, admissible references, context transitions and which processes/readouts descend; ray separation by available effects remains open. A named frame, independent tensor ancilla or algebraic J is not a proof of availability."]

/-- Standing regime checks. Every entry is unassessed; this is not a results list. -/
def matterRegimeObligations : List ResearchTask := [
  openBridge "matter_regime_bose_einstein_condensation"
    "UNASSESSED: test whether primitive definitions permit collective occupation and coherence; do not identify condensation with superfluidity.",
  openBridge "matter_regime_superfluidity"
    "UNASSESSED: retain a separate collective-flow obligation; a condensate analogy or finite mixer is not a derivation of superfluidity.",
  openBridge "matter_regime_superconductivity"
    "UNASSESSED: test collective coherent matter and electromagnetic response without importing a fixed independent-particle ontology or claiming superconductivity from phase arithmetic alone.",
  openBridge "matter_regime_quasiparticles"
    "UNASSESSED: permit particle-like excitations whose effective properties depend on their host system; this does not settle elementary-particle ontology.",
  openBridge "matter_regime_entanglement"
    "UNASSESSED: retain composite states and correlations that are not exhausted by separate descriptions of their parts; existing finite gates do not alone close physical composite structure.",
  openBridge "matter_regime_quantum_indistinguishability"
    "UNASSESSED: test whether labels are representational devices or physically individuating properties; do not assume distinguishable independent objects as a compulsory primitive.",
  openBridge "matter_regime_topological_phases"
    "UNASSESSED: permit physically relevant organization of the whole beyond a catalogue of individually assigned local properties; naming a global invariant does not establish a topological phase.",
  openBridge "matter_regime_decoherence"
    "UNASSESSED: model process-environment correlations and their observational effect without treating decoherence alone as a unique-outcome mechanism.",
  openBridge "matter_regime_stable_records"
    "UNASSESSED: account for durable physical records and the apparatus using the same rules; distinguish archival stability, measurement repeatability and realization of one run."]

def reversibleEchoAccountingBoundary : ResearchTask := {
  id := "reversible_echo_accounting_boundary"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Supplied rational Gaussian carrier with named multiplication, conjugation and unit, and real raw responses satisfying the complete WeightLaws contract.",
    "The positive bridge separately supplies nonzero branches, actual inverse-return coefficients, one-column conjugate reciprocity, same-scale exhaustive accounting and unit response.",
    "Finite scalar control uses ZMod 5, with its supplied commutative scalar arithmetic."]
  conclusions := [
    "The absolute-norm control has full WeightLaws, a genuine two-sided inverse and normalized nonzero raw branches, yet its conjugate echo response is 5/9.",
    "The quartic control has full WeightLaws, transparent square-swap dynamics, conjugate inverse coefficients, nonzero branches and scalar echo one. Its context-normalized detector is balanced and returns deterministically, while its raw branch sum is 1/2.",
    "The finite scalar control satisfies additive transparent square-swap and two-sided inverse laws, and instantiates the existing TransparentSwapRoot reconstruction. Its phase has square minus one, fourth power one, inverse three and a genuine half, but no additive unital map reverses the phase or swaps the coefficients.",
    "The conditional bridge derives NondegenerateEcho from the separately supplied return, reciprocity, accounting and unit-response premises."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/ReversibleEchoAccountingBoundary.lean"
      declarations := [
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.absWeight_laws",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.unequal_undo_forward",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.unequal_forward_undo",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.unequal_unit_branches",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.unequal_branches_nonzero",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.unequal_raw_normalization",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.unequal_actual_return",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.unequal_conjugate_echo",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.unequal_echo_weight",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.unequal_echo_not_normalized",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.balanced_coefficients",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.balanced_square_swap",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.balanced_diagonal",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.balanced_undo_forward",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.balanced_forward_undo",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.balanced_conjugation",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.balanced_unit_branches",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.balanced_branches_nonzero",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.balanced_scalar_echo",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.quarticWeight_laws",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.quartic_balanced_weights",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.quartic_raw_sum",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.quartic_raw_not_normalized",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.quartic_echo",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.detector_balanced",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.detector_return",
        "IDT.QMClosure.ReversibleEchoAccountingBoundary.nondegenerateEcho_of_return_accounting"] },
    { sourcePath := "Proofs/QMClosure/FiniteScalarReversalBoundary.lean"
      declarations := [
        "IDT.QMClosure.FiniteScalarReversalBoundary.coefficient_laws",
        "IDT.QMClosure.FiniteScalarReversalBoundary.square_swap",
        "IDT.QMClosure.FiniteScalarReversalBoundary.diagonal",
        "IDT.QMClosure.FiniteScalarReversalBoundary.undo_forward",
        "IDT.QMClosure.FiniteScalarReversalBoundary.forward_undo",
        "IDT.QMClosure.FiniteScalarReversalBoundary.forward_additive",
        "IDT.QMClosure.FiniteScalarReversalBoundary.reconstructed",
        "IDT.QMClosure.FiniteScalarReversalBoundary.coefficients_nonzero",
        "IDT.QMClosure.FiniteScalarReversalBoundary.coefficients_units",
        "IDT.QMClosure.FiniteScalarReversalBoundary.phase_value",
        "IDT.QMClosure.FiniteScalarReversalBoundary.phase_square",
        "IDT.QMClosure.FiniteScalarReversalBoundary.phase_fourth",
        "IDT.QMClosure.FiniteScalarReversalBoundary.phase_inverse_value",
        "IDT.QMClosure.FiniteScalarReversalBoundary.phase_inverse",
        "IDT.QMClosure.FiniteScalarReversalBoundary.half_value",
        "IDT.QMClosure.FiniteScalarReversalBoundary.half_doubles",
        "IDT.QMClosure.FiniteScalarReversalBoundary.no_additive_unital_phase_reversal",
        "IDT.QMClosure.FiniteScalarReversalBoundary.no_additive_unital_coefficient_swap"] }]
  plannedArtifacts := []
  dependencies := ["rational_count_order_readout_origin"]
  limits := [
    "Physical origin of return reciprocity and same-scale raw branch accounting remains open.",
    "The unequal reversible gate is not claimed to conserve raw response on every input.",
    "Global semantic equality must be stable under reflection for conjugation to descend on a scalar image.",
    "These mathematical controls do not prove physical Born readout, full QM, GR or physical scales."] }

def singleCalibrationScalarFaithfulnessOrigin : ResearchTask := {
  id := "single_calibration_scalar_faithfulness_origin"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A supplied commutative semiring S and coefficients a,b with a+b=1, a*a+b*b=0 and a*b+b*a=1.",
    "A real-valued response on all of S that is multiplicative, with one raw native column normalization w(a)+w(b)=1."]
  conclusions := [
    "A compatible additive group and commutative ring are reconstructed through the existing transparent swap-root theorem.",
    "Unit and zero response, native branch responses one half, w(2)=4, half response one quarter and phase response one are consequences of the supplied contract.",
    "Characteristic zero and faithful integer Gaussian and dyadic arithmetic are consequences, with the exact integer cross-denominator equality criterion.",
    "The generated arithmetic image carries canonical additive and multiplicative involutive conjugation fixing half and exchanging the native coefficients."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/SingleCalibrationScalarFaithfulness.lean"
      declarations := [
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.additiveReconstruction",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.scalarRing",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.weight_one",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.weight_zero",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.native_weights",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.weight_two",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.weight_half",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.weight_phase",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.characteristicZero",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.arithmetic_parameters",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.faithful_dyadic_arithmetic",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Contract.generated_coefficients",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Arithmetic.gaussian_injective",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Arithmetic.triple_eq_iff",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Arithmetic.dyadicEval_injective",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Arithmetic.conjugationEquiv",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Arithmetic.conjugation_involutive",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Arithmetic.conjugation_half",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Arithmetic.conjugation_phase",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Arithmetic.conjugation_a",
        "IDT.QMClosure.SingleCalibrationScalarFaithfulness.Arithmetic.conjugation_b"] }]
  plannedArtifacts := ["Proofs/QMClosure/SingleCalibrationScalarFaithfulness.lean"]
  dependencies := ["operational_positive_readout"]
  limits := [
    "The supplied commutative scalar realization and globally multiplicative scalar response belong to this companion contract. The separate operator task supplies its smaller word-response entry point.",
    "The response codomain in the checked implementation is the real numbers. Ordered-field generalization remains analytic.",
    "Conjugation is constructed on the generated image. Response conjugation invariance on arbitrary sums and quadratic readout selection remain open.",
    "Physical gate and calibration origins, detector interpretation, Born interpretation and full QM remain open."] }

def localBranchOperatorFaithfulnessOrigin : ResearchTask := {
  id := "local_branch_operator_faithfulness_origin"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "An additive commutative monoid V and a complete additive operation T on V times V, transparent on the diagonal and with T squared equal to port exchange.",
    "Real weights on finite words in the extracted native branches A and B, multiplicative under concatenation and extensional under equality of the resulting endomorphisms.",
    "One raw native column normalization W([A])+W([B])=1."]
  conclusions := [
    "The empty word has weight one, both native branches have weight one half, every word has weight two raised to minus its length, and equal word actions have equal lengths.",
    "The actual endomorphism ring has characteristic zero. Its native generated coefficient subring is commutative and contains a faithful Gaussian-dyadic arithmetic image.",
    "That arithmetic image exhausts the native generated subring and admits canonical additive and multiplicative involutive conjugation exchanging A and B.",
    "An additive real-valued extension agreeing with all calibrated word weights is impossible because coherent operator addition gives AB+BA=I.",
    "The finite five-element local gate rejects the calibrated operator-response contract, while a supplied complex norm model witnesses consistency."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/LocalBranchOperatorFaithfulness.lean"
      declarations := [
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.Gate.reconstruction",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.Gate.additiveGroup",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.Gate.generatedCommRing",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.weight_one",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.native_weights",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.weight_word",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.equal_actions_equal_lengths",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.reflection_invariant",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.half_powers_separate",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.endCharacteristicZero",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.generatedCharacteristicZero",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.dyadicOperator_injective",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.arithmeticSubring_eq_top",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.canonicalConjugation",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.canonicalConjugation_a",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.canonicalConjugation_b",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.canonicalConjugation_involutive",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.OperatorResponse.no_additive_extension",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.Controls.finite_no_operator_response",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.ConsistencyWitness.operator_contract"] }]
  plannedArtifacts := ["Proofs/QMClosure/LocalBranchOperatorFaithfulness.lean"]
  dependencies := ["single_calibration_scalar_faithfulness_origin"]
  limits := [
    "Operator response extensionality, stationary serial gains and one raw column normalization remain supplied physical bridges.",
    "The response domain consists of serial branch words. Response on arbitrary coherent additive sums remains unspecified.",
    "Commutativity belongs to the native generated coefficient subring. Ambient endomorphisms and general circuit composition retain their separate algebraic structure.",
    "Faithfulness concerns operators. The separate source task supplies a stronger extensionality premise for evaluation at one reference.",
    "The additive-extension obstruction concerns coherent operator addition. Additivity of probabilities for exclusive outcomes remains a separate statement.",
    "Norm square is supplied within the consistency witness. Quadratic readout on arbitrary coherent sums, Born interpretation and full QM remain open."] }

def sourceHistoryFaithfulnessOrigin : ResearchTask := {
  id := "source_history_faithfulness_origin"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "An additive commutative monoid V, a complete additive transparent square-swap operation T and a supplied reference v.",
    "Real weights on finite native branch words with stationary one-step gains W(c::s)=W([c])*W(s) and one raw native column normalization W([A])+W([B])=1.",
    "Equality of raw terminal states at v in the supplied additive carrier V, retaining preparation and attenuation scale, implies equality of word weights."]
  conclusions := [
    "The empty word has weight one, concatenation is multiplicative, every word has weight two raised to minus word length, and equal terminal states have equal word lengths.",
    "The supplied reference is nonzero and has infinite additive order as a consequence of serial branch response.",
    "Evaluation at the reference is injective on the native generated coefficient algebra and on the Gaussian-dyadic quotient. Triples (k,m,n) and (l,r,s) represent the same quotient element exactly when 2^l*m=2^k*r and 2^l*n=2^k*s.",
    "The finite five-element local gate rejects the calibrated source-response contract, while the supplied complex norm witness at reference one gives a consistent instance."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/LocalBranchOperatorFaithfulness.lean"
      declarations := [
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.operatorResponse",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.weight_one",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.weight_append",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.native_weights",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.weight_word",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.equal_terminal_states_equal_lengths",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.reference_nat_torsion_free",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.reference_int_torsion_free",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.reference_nonzero",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.gaussian_evaluation_injective",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.generatedEvaluation_injective",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.SourceResponse.dyadicReference_injective",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.Controls.finite_no_source_response",
        "IDT.QMClosure.LocalBranchOperatorFaithfulness.ConsistencyWitness.nontrivial_contract"] }]
  plannedArtifacts := ["Proofs/QMClosure/LocalBranchOperatorFaithfulness.lean"]
  dependencies := ["local_branch_operator_faithfulness_origin"]
  limits := [
    "Terminal-state response extensionality is a stronger supplied premise than operator-response extensionality. Its physical origin remains open.",
    "Infinite additive order is specific to the supplied reference. The theorem imposes no global torsion-free condition on the ambient carrier.",
    "Physical preparability of all additive combinations in the generated cyclic image remains an additional bridge.",
    "The response is specified on serial branch histories. Readout of arbitrary coherent sums, Born interpretation and full QM remain open."] }

def nativeInitialHistoryPresentationOrigin : ResearchTask := {
  id := "native_initial_history_presentation_origin"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The free unital possibly noncommutative semiring on two generators a,b, quotiented by the least semiring congruence generated by only a+b=1 and a*a+b*b=0."]
  conclusions := [
    "The cross relation a*b+b*a=1 is a consequence. The initial quotient has compatible ring structure, commutative multiplication, half, phase and characteristic zero.",
    "Every initial quotient element has a Gaussian-dyadic presentation H^k*(m+n*U). Equality is exactly the integer cross-denominator criterion 2^l*m=2^k*r and 2^l*n=2^k*s.",
    "The presentation is equivalent to the Gaussian integers with inverse two adjoined. Every semiring target with a supplied pair obeying the two local coefficient laws has a unique unital semiring map from that algebra sending the two native generators to the supplied pair.",
    "Swapping the syntactic generators gives an involution which corresponds to Gaussian conjugation under the equivalence.",
    "The finite five-element evaluation is noninjective and syntactic reflection fails to descend through that semantic quotient."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeInitialHistoryPresentation.lean"
      declarations := [
        "IDT.QMClosure.NativeInitialHistoryPresentation.ExactPair.Laws.reconstruction",
        "IDT.QMClosure.NativeInitialHistoryPresentation.ExactPair.Laws.scalarRing",
        "IDT.QMClosure.NativeInitialHistoryPresentation.eval",
        "IDT.QMClosure.NativeInitialHistoryPresentation.eval_unique",
        "IDT.QMClosure.NativeInitialHistoryPresentation.hom_ext",
        "IDT.QMClosure.NativeInitialHistoryPresentation.presentationCharZero",
        "IDT.QMClosure.NativeInitialHistoryPresentation.NormalForm.exists_value",
        "IDT.QMClosure.NativeInitialHistoryPresentation.NormalForm.cross_denominator",
        "IDT.QMClosure.NativeInitialHistoryPresentation.NormalForm.complexEval_injective",
        "IDT.QMClosure.NativeInitialHistoryPresentation.NormalForm.syntactic_completeness",
        "IDT.QMClosure.NativeInitialHistoryPresentation.NormalForm.equivalence",
        "IDT.QMClosure.NativeInitialHistoryPresentation.NormalForm.universalMap",
        "IDT.QMClosure.NativeInitialHistoryPresentation.NormalForm.universalMap_unique",
        "IDT.QMClosure.NativeInitialHistoryPresentation.reflection",
        "IDT.QMClosure.NativeInitialHistoryPresentation.reflection_involutive",
        "IDT.QMClosure.NativeInitialHistoryPresentation.NormalForm.reflection_is_gaussian_conjugation",
        "IDT.QMClosure.NativeInitialHistoryPresentation.Controls.finiteEval_not_injective",
        "IDT.QMClosure.NativeInitialHistoryPresentation.Controls.reflection_does_not_descend",
        "IDT.QMClosure.NativeInitialHistoryPresentation.quotient_eq_iff",
        "IDT.QMClosure.NativeInitialHistoryPresentation.ExactPair.Laws.cross",
        "IDT.QMClosure.NativeInitialHistoryPresentation.multiplication_commutes"] }]
  plannedArtifacts := ["Proofs/QMClosure/NativeInitialHistoryPresentation.lean"]
  dependencies := ["reversible_echo_accounting_boundary"]
  limits := [
    "The grammar and the destructive-composition relator a*a+b*b=0 are supplied. Their physical origin and physical cancellation remain open.",
    "The universal target signature is Semiring with the supplied local coefficient laws. It permits noncommutative ambient operations, finite-characteristic models and the zero model whenever those laws hold.",
    "Coefficient commutativity belongs to the generated image. General target operations and circuit composition retain their separate algebraic structure.",
    "Initial syntactic equality gives the least congruence of the supplied grammar. Actual semantic interpretations can impose additional identifications and can lose reflection descent.",
    "The complex model enters after the grammar as a mathematical consistency and separation model. Its natural-cast interpretation proves initial characteristic zero before injectivity.",
    "Normal-form existence and the exact cross-denominator criterion are checked. An executable canonical normalization algorithm remains a separate implementation task.",
    "The small calibrated word-response contract of the preceding faithfulness cluster supplies a separate semantic bridge. This presentation theorem has no response or calibration premise.",
    "Physical grammar, detector readout, Born interpretation and full QM remain open."] }

def localBranchFiniteWindowBoundary : ResearchTask := {
  id := "local_branch_finite_window_boundary"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "A finite word-window length L at least one and an odd prime p greater than 2^(L+1).",
    "The raw additive carrier V=(ZMod p)^2 with J(x,y)=(-y,x), native branches A=(I+J)/2 and B=(I-J)/2, and reference v=(1,0).",
    "The word window consists of terminal states obtained from branch words of length at most L."]
  conclusions := [
    "Analytic construction gives an additive two-port operation that is transparent on the diagonal and whose square is port exchange on all of V.",
    "Within the window, equality of finite terminal states forces equality of the corresponding rational Gaussian values and equality of word lengths.",
    "The window response W=2^(-word length) is well defined. Concatenation multiplicativity holds when the concatenated length is at most L, including stationary one-step gains on those window transitions.",
    "Extending the response by zero outside the window gives a nonnegative response bounded by one, with W(0)=0 and W(v)=1.",
    "The source satisfies p-fold additive torsion. A calibrated extension with stationary gains and raw terminal-state extensionality on all words is therefore impossible.",
    "After clearing denominators by 2^L, the integer word coordinates have magnitude at most 2^L, so coordinate differences have magnitude less than p. A finite-field norm argument checks the boundary transition."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/LocalBranchFiniteWindowBoundary.lean"]
  dependencies := ["source_history_faithfulness_origin"]
  limits := [
    "Every stated construction, estimate and consequence remains analytic until the planned artifact is compiled and reviewed.",
    "Agreement on a bounded word window leaves the universal all-word response contract open.",
    "The global source-history theorem retains its all-word hypotheses. This finite-window construction addresses inference from bounded evidence to that contract.",
    "The response extension outside the window preserves the stated bounds and normalization. Its stationary gain law is confined to the specified window transitions.",
    "Physical availability of arbitrarily long histories, physical readout origins, Born interpretation and full QM remain open."] }

def finiteHistoryReadoutRegularityFrontier : ResearchTask := {
  id := "finite_history_readout_regularity_frontier"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "A real-valued response on the generated Gaussian-dyadic algebra that is multiplicative on the full algebra and satisfies one native column calibration.",
    ("At least one of two alternative sufficient regularity packages is supplied. " ++
      "EITHER (a) w(m+n*u) is a joint finite-degree polynomial for natural m,n, " ++
      "equivalently a fixed-K context-independent exchangeable subset kernel over the original history tokens on that two-phase input family. " ++
      "OR (b) the real span of Gaussian-integer translations of the restriction of w to Gaussian integers is finite dimensional, " ++
      "together with nonzero response at every positive integer count. " ++
      "Within package (b), the latter count premise may instead be nonzero response " ++
      "at the single count N_d=2^lcm(1,...,d)-1 when an explicit global translation-rank bound d at least one is supplied.")]
  conclusions := [
    "Analytic proposal makes each alternative regularity package sufficient to select norm square on the generated Gaussian-dyadic algebra.",
    "In the joint-polynomial route, doubling calibration removes every degree except two, and two multiplicative product identities force the mixed quadratic coefficient to vanish and fix the remaining coefficients.",
    "In the finite-linear-rank route, spectral finite characters under chi mapped to chi squared isolate odd-torsion periodicity. The nonzero count condition removes the periodic branches and reduces the problem to the joint-polynomial route.",
    "Analytic asymmetric Gaussian-prime valuation responses show that raywise quadratic scaling alone leaves additional response freedom.",
    "Analytic finite-rank controls take norm square Q times a residue indicator. Reduction modulo a Gaussian prime above five gives Q(z)*1[z mod pi is nonzero], with translation rank at most twenty and w(5)=0.",
    "A conjugation-invariant Gaussian zero filter modulo three gives another native-calibrated control, with translation rank at most thirty-six and w(3)=0."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/FiniteHistoryReadoutRegularity.lean"]
  dependencies := [
    "single_calibration_scalar_faithfulness_origin",
    "native_initial_history_presentation_origin"]
  limits := [
    "Both complete sufficiency routes and their relationship to original-token kernels remain analytic. Individual spectral, difference, extraction, dilation, quadratic-algebra and countercontrol contracts are tracked separately in the finite-translation and readout tasks below.",
    "The universal 4/20 gap, degree-two selection, residue reconstruction, coset-to-polynomial identity, support classification and real-to-complex rank transfer retain separate proof obligations.",
    "The regularity packages are alternatives. Their conjunction is unnecessary for the proposed sufficiency result.",
    "The proposed premises add neither positivity, count order nor response conjugation invariance. The response codomain is the real numbers.",
    "Finite translation rank alone permits the stated calibrated residue filters. The nonzero count condition is a separate part of the finite-rank package.",
    "Microscopic binary locality, finite code and finite-dimensional nonlinear registers leave a uniform bound on original-history arity or finite LINEAR translation rank unresolved.",
    "A genuinely finite discrete automaton with stationary token updates has finite translation rank after linearization. Finite polynomial history arity remains a separate requirement, as parity illustrates, and residue filters retain the need for the nonannihilation premise.",
    "Finite history arity and finite linear translation rank remain regularity premises whose physical origins are open.",
    "Physical readout selection, Born interpretation and full QM remain open."] }

def finiteTranslationSpectralExtraction : ResearchTask := {
  id := "finite_translation_spectral_extraction"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A complex-valued function on the full integer lattice has a finite-dimensional complex span of all translations."]
  conclusions := [
    "Checked spectral declarations decompose the actual translate space into joint generalized eigenspaces and provide translation-compatible projections.",
    "Checked difference declarations give a unique bivariate complex polynomial from two global coordinate annihilators.",
    "The extraction bridge identifies each actual supported component with a nonzero polynomial times its coordinate character and reconstructs the function by their finite sum."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FiniteTranslationSpectrum.lean"
      declarations := [
        "FiniteTranslationSpectrum.jointBlock_isInternal",
        "FiniteTranslationSpectrum.jointProjection_translationEnd",
        "FiniteTranslationSpectrum.sum_readoutComponents",
        "FiniteTranslationSpectrum.readoutComponents_coordinate_ne_zero"] },
    { sourcePath := "Proofs/QMClosure/FiniteDifferencePolynomial.lean"
      declarations := [
        "IDT.TranslationRankGap.existsUnique_polynomial_of_coordinate_fwdDiff_eq_zero"] },
    { sourcePath := "Proofs/QMClosure/FiniteTranslationExponentialPolynomial.lean"
      declarations := [
        "IDT.TranslationRankGap.exists_polynomial_of_jointBlock_mem",
        "IDT.TranslationRankGap.exists_finite_exponentialPolynomial"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "The hypotheses use complex translation dimension. Transfer from a supplied real translation space remains a separate obligation.",
    "Degree-two selection, residue reconstruction and universal rank classification remain open formalization obligations."] }

def finiteTranslationDilationSupport : ResearchTask := {
  id := "finite_translation_dilation_support"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A complex-valued function on the full integer lattice has finite-dimensional complex global translate space.",
    "The global dilation law f(z+z)=4*f(z) is supplied."]
  conclusions := [
    "Coordinatewise character squaring is a permutation of the actual finite readout support.",
    "Components satisfy exact dilation, and one common positive odd exponent M has chi(i)^M=1 for every supported character coordinate."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FiniteTranslationDilationSupport.lean"
      declarations := [
        "FiniteTranslationDilationSupport.support_square_eq",
        "FiniteTranslationDilationSupport.square_injective_on_support",
        "FiniteTranslationDilationSupport.dilate_component",
        "FiniteTranslationDilationSupport.exists_common_odd_period"] }]
  plannedArtifacts := []
  dependencies := ["finite_translation_spectral_extraction"]
  limits := [
    "Polynomial degree, residue polynomial reconstruction, support counts and rank bounds require further arguments.",
    "The supplied global dilation and finite-dimensionality contracts require a physical origin."] }

def multiplicativeResidueQuadraticAlgebra : ResearchTask := {
  id := "multiplicative_residue_quadratic_algebra"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A monoid-indexed family Q_r of homogeneous real quadratics is calibrated by Q_1(1,0)=1.",
    "Q_(r*s)(z*t)=Q_r(z)*Q_s(t) is supplied universally for independent monoid indices and arbitrary real coordinate pairs with Gaussian multiplication."]
  conclusions := [
    "Every family member is Q_r(z)=c(r)*N(z), with c(1)=1 and c(r*s)=c(r)*c(s).",
    "The coefficient map is a monoid homomorphism to the multiplicative reals.",
    "Every such real multiplicative coefficient map supplies a calibrated family satisfying the universal polynomial identity."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/MultiplicativeResidueQuadratics.lean"
      declarations := [
        "IDT.MultiplicativeResidueQuadratics.classify",
        "IDT.MultiplicativeResidueQuadratics.coefficientHom",
        "IDT.MultiplicativeResidueQuadratics.diagonal_calibrated",
        "IDT.MultiplicativeResidueQuadratics.diagonal_multiplicative"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "The full real-coordinate polynomial identity is a supplied premise. Its derivation from multiplicativity on residue cosets remains open.",
    "Residue reconstruction, coefficient support classification and universal rank conclusions require separate artifacts."] }

def finiteRankModFiveReadoutControl : ResearchTask := {
  id := "finite_rank_mod_five_readout_control"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The source carrier is integer pairs with explicit Gaussian multiplication and N(m,n)=m^2+n^2.",
    "The fixed response is f(m,n)=N(m,n) when m-2*n is nonzero modulo five, and zero otherwise."]
  conclusions := [
    "The response is nonnegative and globally multiplicative, with f(1)=1, f(2)=4, f(i)=1 and f(1+i)=2.",
    "The response has f(5)=0 and fails conjugation invariance at an explicit pair.",
    "The global real translate span has dimension exactly twenty, from a twenty-feature upper bound and an explicit invertible twenty-by-twenty sample matrix."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FiniteRankReadoutFilter.lean"
      declarations := [
        "IDT.QMClosure.FiniteRankReadoutFilter.mod5_filter_control",
        "IDT.QMClosure.FiniteRankReadoutFilter.readout_five",
        "IDT.QMClosure.FiniteRankReadoutFilter.conjugation_failure",
        "IDT.QMClosure.FiniteRankReadoutFilter.translateSpan_finrank_eq_twenty"] }]
  plannedArtifacts := []
  dependencies := []
  limits := [
    "This artifact concerns the full integer carrier. Dyadic extension and the universal 4/20 rank gap remain separate formalization obligations."] }

def fourProbeTomographyMixtureWall : ResearchTask := {
  id := "four_probe_tomography_mixture_wall"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the fixed modulo-five response on integer pairs and P(z)=(f(z),f(z+1),f(z+i),f(z+1+i)).",
    "A two-source mean is the componentwise arithmetic average of its two probe vectors."]
  conclusions := [
    "P is injective and its actual image is equivalent to the entire source carrier.",
    "Every source operation transports to that actual image, and every source equivalence transports reversibly.",
    "Equal-half ensembles {0,-1-i} and {-1,-i} both have mean vector (1,1,1,1).",
    "After translation by +1 their mean vectors are (1,3,1,1/2) and (1,3,1,3).",
    "Consequently no function on four real mean coordinates reproduces this translation for every equal-half source pair."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FiniteReadoutTomographyWall.lean"
      declarations := [
        "IDT.QMClosure.FiniteReadoutTomographyWall.probe_injective",
        "IDT.QMClosure.FiniteReadoutTomographyWall.observableEquiv",
        "IDT.QMClosure.FiniteReadoutTomographyWall.inducedUpdate_observe",
        "IDT.QMClosure.FiniteReadoutTomographyWall.inducedEquiv",
        "IDT.QMClosure.FiniteReadoutTomographyWall.four_probe_translate_rank_separation",
        "IDT.QMClosure.FiniteReadoutTomographyWall.equal_meanProbes",
        "IDT.QMClosure.FiniteReadoutTomographyWall.shifted_meanProbe_first_pair",
        "IDT.QMClosure.FiniteReadoutTomographyWall.shifted_meanProbe_second_pair",
        "IDT.QMClosure.FiniteReadoutTomographyWall.no_meanProbe_translation_update"] }]
  plannedArtifacts := []
  dependencies := ["finite_rank_mod_five_readout_control"]
  limits := [
    "Reconstruction uses exact realized probe vectors. Continuity and noise-stable inference require additional hypotheses.",
    "Ordinary averaging has a mathematical definition here. Its interpretation as physically realizable exclusive preparation mixtures remains supplied."] }

def finiteTranslationUniversalRankGap : ResearchTask := {
  id := "finite_translation_universal_rank_gap"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "A real readout on Gaussian integers is globally multiplicative, has f(2)=4, and has finite global real translate rank d."]
  conclusions := [
    "The analytic proposal gives f=N with d=4, or f different from N with d at least twenty.",
    "Its proposed equality classification at rank twenty consists of the two modulo-five filters N(m,n)*1[m+2*n nonzero modulo five] and N(m,n)*1[m-2*n nonzero modulo five]."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/FiniteTranslationRankGap.lean"]
  dependencies := [
    "finite_translation_spectral_extraction", "finite_translation_dilation_support",
    "multiplicative_residue_quadratic_algebra", "finite_rank_mod_five_readout_control"]
  limits := [
    "The universal gap and equality classification await formalization.",
    "Remaining obligations include real-to-complex rank transfer, degree-two selection, real residue polynomial reconstruction, extension of coset multiplicativity to a universal polynomial identity, exact character-block rank, support counting and equality classification.",
    "Acceptance of individual dependencies supplies only their stated contracts."] }

def finiteGateLocalizationReadoutWall : ResearchTask := {
  id := "finite_gate_localization_readout_wall"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "A finite Gaussian-rational generator alphabet, optionally including finitely many inverse gates, and finitely many tested inputs are specified.",
    "Choose an odd prime avoiding denominators and numerator norms of the selected nonzero values."]
  conclusions := [
    "The analytic construction W(z)=N(z)*1[reduction(N(z)) is nonzero modulo p] is nonnegative, multiplicative and conjugation invariant on the associated localization.",
    "It agrees with N on the finite tests and serial products of the selected generators, and annihilates the nonzero integer p.",
    "Residue indicators times N, the two coordinates and the constant function give global real translate rank at most 4*p^2 on the translation domain of that localization."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/FiniteGateLocalizationReadoutWall.lean"]
  dependencies := []
  limits := [
    "This wall remains analytic awaiting formalization.",
    "Serial-product agreement has the stated multiplicative scope. Coherent circuits producing additional sums require their own argument."] }

def localMixtureCongruenceReadoutOrigin : ResearchTask := {
  id := "local_mixture_congruence_readout_origin"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "P is an arbitrary vector of four real probe functions on the full integer lattice.",
    "The congruence quantifies over every finite probability ensemble with arbitrary nonnegative real weights summing to one.",
    "For each elementary translation +1,-1,+i,-i, equality of entire expected P vectors implies equality of entire expected P vectors after that translation."]
  conclusions := [
    "For any source update U and k probes, all-real finite-mixture congruence is equivalent to each updated probe coordinate lying in the real span of the constant function and the k original probes.",
    "Generator closure propagates to finite continuation words; on the integer lattice every translate of each probe lies in that augmented probe span, giving real translate dimension at most k+1 and at most five for four probes.",
    "Casting the same augmented probes into complex-valued functions gives complex translate dimension at most k+1, hence at most five for four probes.",
    "The concrete shifted-norm probes satisfy mixture congruence under every integer translation; the existing modulo-five equal-half witness supplies an obstruction for its distinct filtered probes."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FiniteMixtureContinuationRank.lean"
      declarations := [
        "FiniteMixtureContinuationRank.mixtureCongruent_iff_updated_coordinates_mem",
        "FiniteMixtureContinuationRank.word_coordinate_mem",
        "FiniteMixtureContinuationRank.finrank_translationSpan_le",
        "FiniteMixtureContinuationRank.four_probe_translation_rank_le_five",
        "FiniteMixtureContinuationRank.normProbes_mixtureCongruent",
        "FiniteMixtureContinuationRank.normReadout_finite_translation_rank"] },
    { sourcePath := "Proofs/QMClosure/MixtureProbeComplexRank.lean"
      declarations := [
        "MixtureProbeComplexRank.cast_mem_complexProbeSpace",
        "MixtureProbeComplexRank.finrank_translationSpanC_le",
        "MixtureProbeComplexRank.four_probe_complex_translation_rank_le_five"] }]
  plannedArtifacts := []
  dependencies := ["four_probe_tomography_mixture_wall"]
  limits := [
    "All finite real probability weights are quantified. Selection under rational or dyadic weights requires a separate argument.",
    "The complex bound uses the explicit cast augmented-probe family. A generic equality of real and complex translate ranks remains outside this contract.",
    "The entire expected probe vector remains congruent under each generator so that the rule can be iterated.",
    "Physical realization of ordinary mixtures, accessibility of all real weights and sufficiency of bounded probe means under local continuation remain open primitive-origin obligations.",
    "Norm selection follows with the additional checked symmetry/doubling contract or the three-premise multiplicative mixture contract recorded separately."] }

def smallRankSymmetryReadoutSelection : ResearchTask := {
  id := "small_rank_symmetry_readout_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A complex-valued function f on the full integer lattice has an explicitly finite-dimensional complex span of all integer translations.",
    "The complex translate-space finrank is strictly less than eight.",
    "For every lattice source z, f(z+z)=4*f(z), and for every integer m,n, f(-n,m)=f(m,n)."]
  conclusions := [
    "Dilation cycles force zero origin values for the actual supported readout components.",
    "A nontrivial supported character has a common positive odd period and generates four distinct rotated character blocks, each containing two independent vectors; rank below eight forces every supported character to be trivial.",
    "Trivial supported characters give a global polynomial representation on the integer lattice; doubling selects homogeneous degree two and quarter rotation gives f(m,n)=f(1,0)*(m^2+n^2).",
    "The scalar theorem includes the zero readout. Calibration f(1,0)=1 selects the squared norm.",
    "Four arbitrary real probes with all-real finite-mixture continuation congruence provide complex translate rank at most five, so their first coordinate is selected under the supplied doubling and rotation laws."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FiniteTranslationSmallRankSupport.lean"
      declarations := [
        "FiniteTranslationSmallRankSupport.component_zero",
        "FiniteTranslationSmallRankSupport.eight_le_finrank_of_supported_nontrivial",
        "FiniteTranslationSmallRankSupport.supported_eq_one_of_finrank_lt_eight"] },
    { sourcePath := "Proofs/QMClosure/QuadraticPolynomialDyadicSelection.lean"
      declarations := [
        "IDT.TranslationRankGap.polynomial_eq_scalar_norm_of_dyadic_rotation",
        "IDT.TranslationRankGap.polynomial_readout_eq_scalar_norm_of_dyadic_rotation"] },
    { sourcePath := "Proofs/QMClosure/MixtureProbeComplexRank.lean"
      declarations := ["MixtureProbeComplexRank.four_probe_complex_translation_rank_le_five"] },
    { sourcePath := "Proofs/QMClosure/FiniteTranslationNormSelection.lean"
      declarations := [
        "IDT.TranslationRankGap.original_mem_trivial_jointBlock_of_finrank_lt_eight",
        "IDT.TranslationRankGap.exists_polynomial_of_finrank_lt_eight_dyadic_rotation",
        "IDT.TranslationRankGap.readout_eq_scalar_norm_of_finrank_lt_eight_dyadic_rotation",
        "IDT.TranslationRankGap.readout_eq_norm_of_finrank_lt_eight_dyadic_rotation_of_calibrated",
        "IDT.TranslationRankGap.four_probe_readout_eq_scalar_norm",
        "IDT.TranslationRankGap.four_probe_readout_eq_norm_of_calibrated"] }]
  plannedArtifacts := []
  dependencies := [
    "finite_translation_spectral_extraction", "finite_translation_dilation_support",
    "local_mixture_congruence_readout_origin"]
  limits := [
    "The strict bound below eight is sufficient. Sharpness remains unproved.",
    "Finite dimension, global doubling and quarter-turn invariance are supplied for the complex small-rank theorem; their physical origin remains open.",
    "The real four-probe application uses the explicit augmented-probe complex-span bound and all finite real probability ensembles.",
    "The universal multiplicative rank-four versus rank-twenty classification, physical readout origin, normalized event interpretation and full QM closure remain open."] }

def multiplicativeMixtureReadoutSelection : ResearchTask := {
  id := "multiplicative_mixture_readout_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "P is an arbitrary vector of four real probe functions on the full integer lattice; for every finite real probability ensemble, equality of the entire expected vector is preserved under each translation +1,-1,+i,-i.",
    "The first response f(z)=P(z,0) is globally Gaussian-multiplicative on every pair of integer lattice sources using Gaussian multiplication with its cross terms.",
    "The sole supplied calibration is f(2,0)=4."]
  conclusions := [
    "Global multiplicativity and the calibration derive f(1,0)=f(-1,0)=f(0,1)=1, quarter-turn invariance and quadratic doubling.",
    "The first probe equals the squared Gaussian norm on every integer pair: P((m,n),0)=m^2+n^2.",
    "Nonnegativity, conjugation invariance, monotonicity on nonnegative integer counts, the raw parallelogram identity and vanishing raw third-order inclusion-exclusion follow from selection.",
    "The shifted-norm probes satisfy exactly these three contracts, and an existential theorem records a concrete inhabitant."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/MultiplicativeMixtureReadout.lean"
      declarations := [
        "IDT.MultiplicativeMixtureReadout.unit_readout_eq_one",
        "IDT.MultiplicativeMixtureReadout.negative_unit_readout_eq_one",
        "IDT.MultiplicativeMixtureReadout.imaginary_unit_readout_eq_one",
        "IDT.MultiplicativeMixtureReadout.quarter_turn_invariant",
        "IDT.MultiplicativeMixtureReadout.doubling_readout",
        "IDT.MultiplicativeMixtureReadout.four_probe_readout_eq_norm",
        "IDT.MultiplicativeMixtureReadout.readout_nonnegative",
        "IDT.MultiplicativeMixtureReadout.conjugation_invariant",
        "IDT.MultiplicativeMixtureReadout.natural_count_readout_mono",
        "IDT.MultiplicativeMixtureReadout.readout_parallelogram",
        "IDT.MultiplicativeMixtureReadout.readout_three_way_inclusion_exclusion",
        "IDT.MultiplicativeMixtureReadout.normProbes_contract",
        "IDT.MultiplicativeMixtureReadout.exists_four_probe_contract"] }]
  plannedArtifacts := []
  dependencies := [
    "local_mixture_congruence_readout_origin", "small_rank_symmetry_readout_selection"]
  limits := [
    "The physical origins of real-valued probes, global Gaussian multiplicativity, the calibration, all-real mixture accessibility and local sufficiency remain open.",
    "Global Gaussian multiplicativity ranges over arbitrary integer pairs, including sources represented by coherent sums. Extending serial-word multiplication to this full law requires a separate argument.",
    "The conclusions concern raw algebraic readouts. Normalized event probabilities, Born actualization, Hilbert representation, full QM closure and physical scales remain open.",
    "A nondegenerate normalized echo requires a carrier extension beyond the integer lattice.",
    "The next research stage is selection under rational or dyadic mixture weights together with robustness under approximate mean equality and continuation laws, followed by transport to the initial dyadic history quotient.",
    "The sufficient complex rank bound below eight leaves sharpness and the universal rank-four versus rank-twenty classification open."] }

def fixedCornerHalfMixtureReadoutSelection : ResearchTask := {
  id := "fixed_corner_half_mixture_readout_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "A real-valued response f on the full integer lattice is Gaussian-multiplicative on every pair of sources.",
    "The supplied calibration is f(2,0)=4, and the supplied diagonal sign is f(1,1)>=0.",
    "The probe geometry is fixed as P(z)=(f(z),f(z+1),f(z+i),f(z+1+i)).",
    "For each elementary translation s in +1,-1,+i,-i and every four sources a,b,c,d, equality of entire vectors P(a)+P(b)=P(c)+P(d) implies P(a+s)+P(b+s)=P(c+s)+P(d+s). This congruence quantifies only equal-half two-source mixtures."]
  conclusions := [
    "Multiplicative calibration derives the unit values and f(0,0)=0; the supplied sign selects f(1,1)=2.",
    "The corner seed propagates under the four signed continuation rules to the global rectangle identity, which separates coordinates and yields the integer quadratic recurrence, hence f(m,n)=m^2+n^2.",
    "The generator-law core selects the same norm from zero/unit values, quarter-turn invariance, diagonal generator scaling and the four fixed-corner pair laws.",
    "The concrete norm satisfies the stated pair congruence under every lattice translation and inhabits the standalone multiplicative selection contract."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/FixedCornerHalfMixtureReadout.lean"
      declarations := [
        "IDT.FixedCornerHalfMixtureReadout.rectangle_packet_of_seed",
        "IDT.FixedCornerHalfMixtureReadout.integer_rectangle_separates",
        "IDT.FixedCornerHalfMixtureReadout.corner_seed_iff_diagonal_eq_two",
        "IDT.FixedCornerHalfMixtureReadout.integer_quadratic_recurrence",
        "IDT.FixedCornerHalfMixtureReadout.fixed_corner_readout_eq_norm_of_generator_laws",
        "IDT.FixedCornerHalfMixtureReadout.fixed_corner_readout_eq_norm",
        "IDT.FixedCornerHalfMixtureReadout.normReadout_pairCongruent_translation",
        "IDT.FixedCornerHalfMixtureReadout.exists_fixed_corner_contract"] }]
  plannedArtifacts := []
  dependencies := ["multiplicative_mixture_readout_selection"]
  limits := [
    "The dependency supplies reusable multiplicative calibration lemmas; the selection proof uses rectangle propagation and the integer recurrence.",
    "Only equal-half two-source mixtures are quantified. The fixed translated-readout corner geometry and pair congruence remain supplied premises.",
    "The signed alternative f(1,1)=-2 remains unresolved for the standalone scalar contract.",
    "The native history selector derives its generator laws from a distinct transfer contract on the already supplied initial presentation.",
    "Physical origins of the real response, global multiplicativity, calibration, diagonal sign, prescribed probe geometry and pair congruence remain open; Born actualization and full QM closure remain open."] }

def nativeGeneratorMixtureReadoutSelection : ResearchTask := {
  id := "native_generator_mixture_readout_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The carrier is the existing initial free unital semiring presentation with the relations a+b=1 and a*a+b*b=0, with its ring, half, phase, reflection, Gaussian-dyadic normal forms and faithful algebraic representation supplied by the existing initial-presentation theorems.",
    "W is an arbitrary real readout with W(a)+W(b)=1.",
    "Two fixed native contexts factor at every input: for every presentation element p, W(a*p)=W(a)*W(p) and W(b*p)=W(b)*W(p).",
    "On f(m,n)=W(m+n*phase), the four fixed corner probes preserve equality of entire two-source pair sums under every signed elementary translation +1,-1,+i,-i."]
  conclusions := [
    "The checked source derives W(1)=1 from normalized transfer at one. Equal fourth histories a^4=b^4 and real normalized factorization derive W(a)=W(b)=1/2.",
    "The resulting native transfer contract derives zero, half/doubling, phase and diagonal laws. It gives a canonical nondegenerate normalized raw echo before fixed-corner pair sufficiency is introduced.",
    "The fixed-corner generator-law selector gives the integer norm; native half scaling and the existing normal forms give W(half^k*(m+n*phase))=(m^2+n^2)/4^k for every presented history.",
    "The global conclusion is W(p)=Complex.normSq(complexEval(p)), with the faithful algebraic representation used in the conclusion.",
    "The checked source derives full readout multiplicativity, syntactic-reflection invariance, nonnegativity, zero iff p=0, natural-count order iff, the dyadic-count formula, all-input mixer conservation, the parallelogram identity and vanishing raw I3.",
    "A concrete norm-model witness inhabits the complete native-transfer and fixed-corner pair contract."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeGeneratorMixtureReadout.lean"
      declarations := [
        "IDT.QMClosure.NativeGeneratorMixtureReadout.generator_fourth_history",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.nativeTransfer_of_normalized_generator_transfer",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.normalized_raw_echo",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.integer_readout_eq_norm",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.readout_normal_form",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.readout_eq_complex_norm",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.readout_multiplicative",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.readout_reflection",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.readout_nonnegative",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.readout_zero_iff",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.readout_nat_order_iff",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.readout_dyadic_count",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.mixer_conservation",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.readout_parallelogram",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.raw_I3_zero",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.readout_eq_complex_norm_of_normalized_generator_transfer",
        "IDT.QMClosure.NativeGeneratorMixtureReadout.exists_native_pair_contract"] }]
  plannedArtifacts := []
  dependencies := [
    "native_initial_history_presentation_origin", "fixed_corner_half_mixture_readout_selection"]
  limits := [
    "Native transfer quantifies every presentation element; the two fixed generator contexts are universal input laws.",
    "Pair sufficiency quantifies every source quadruple for four prescribed translated responses and equal-half two-source ensembles.",
    "External arithmetic averaging of readout pairs and coherent composition a*x+b*y are distinct operations whose physical relationship remains open.",
    "The dyadic-count conclusion is an exact value formula; the cited order-equivalence theorem concerns natural counts.",
    "The supplied grammar/destructive relation, real normalized readout, all-context native factorization and fixed-probe sufficiency retain open physical-origin obligations.",
    "Event frequencies, Born actualization, Hilbert representation, full QM closure and physical scales remain open."] }

def nativeSingleContinuationReadoutSelection : ResearchTask := {
  id := "native_single_continuation_readout_selection"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "The carrier is the existing initial two-relator presentation; W is an arbitrary real readout with W(a)+W(b)=1.",
    "For every presentation element p, W(a*p)=W(a)*W(p) and W(b*p)=W(b)*W(p).",
    "For the prescribed probes P(z)=(f(z),f(z+1),f(z+i),f(z+1+i)) of f(m,n)=W(m+n*phase), every equality P(x)+P(y)=P(v)+P(w) is preserved after translating all four integer sources by +1."]
  conclusions := [
    "The checked source derives the native half-transfer contract and quarter-turn invariance from normalized universal generator transfer.",
    "The affine map K(z)=i*z-1 permutes the four fixed corners by [2,0,3,1], has fourth iterate identity, and transports the single +1 pair law to all four signed elementary translation laws.",
    "The resulting contract gives W(p)=Complex.normSq(complexEval(p)) and W(half^k*(m+n*phase))=(m^2+n^2)/4^k for every presentation element and normal form.",
    "Global multiplicativity, syntactic-reflection invariance, nonnegativity, zero iff p=0 and all-input mixer conservation follow through the native and pair contracts obtained by native_contract_of_single_continuation.",
    "The concrete norm model inhabits the exact normalization, two universal generator transfers and single universal pair-continuation contract."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeSingleContinuationReadout.lean"
      declarations := [
        "IDT.QMClosure.NativeSingleContinuationReadout.fixedCornerProbes_cornerTurn",
        "IDT.QMClosure.NativeSingleContinuationReadout.fixedCornerPairLaws_of_single_translation",
        "IDT.QMClosure.NativeSingleContinuationReadout.native_contract_of_single_continuation",
        "IDT.QMClosure.NativeSingleContinuationReadout.readout_eq_complex_norm_of_single_continuation",
        "IDT.QMClosure.NativeSingleContinuationReadout.readout_normal_form_of_single_continuation",
        "IDT.QMClosure.NativeSingleContinuationReadout.global_readout_laws_of_single_continuation",
        "IDT.QMClosure.NativeSingleContinuationReadout.modelReadout_reduced_contract"] }]
  plannedArtifacts := []
  dependencies := ["native_generator_mixture_readout_selection"]
  limits := [
    "The single continuation law quantifies every source quadruple with equal entire prescribed probe vectors.",
    "The corner geometry is fixed by translated values of the same integer restriction; its completeness under continuation remains supplied.",
    "This premise reduction leaves the physical origins of the grammar/destructive relation, real normalized readout, universal native transfer and fixed-probe pair sufficiency open.",
    "Independence of the remaining premises and stability under finite precision remain open research obligations.",
    "Raw readout selection leaves event-frequency interpretation, Born actualization, Hilbert representation and full QM closure open."] }

def nativeGeneratorReadoutCountercontrol : ResearchTask := {
  id := "native_generator_readout_countercontrol"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the same existing initial destructive two-generator presentation, its faithful complex evaluation, syntactic reflection and finite evaluation E into ZMod 5.",
    "Define the concrete counterWeight to be zero when E(p*reflection(p))=0 and Complex.normSq(complexEval(p)) otherwise."]
  conclusions := [
    "The checked countercontrol source gives nonnegativity, unit value one, reflection invariance and global multiplicativity.",
    "Both universal native generator transfers divide the readout by two, and the canonical raw echo has normalized total weight one.",
    "The nonzero history five has weight zero; natural-count monotonicity fails since 1<=5 while the weights are one and zero.",
    "Both prescribed corner seed pair sums are [2,2,2,2]; after the +1 continuation they are [2,6,2,1] and [2,1,2,6], yielding an explicit failure of pair congruence.",
    "At coherent mixer input (1,2), total input weight is five and total output weight is zero; raw I3 at (1,1,i) is minus five.",
    "The control supplies an independence witness for fixed-probe pair sufficiency from normalized native transfer and the canonical echo, even with supplied nonnegativity, reflection invariance and global multiplicativity."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeGeneratorReadoutCountercontrol.lean"
      declarations := [
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.counterWeight_nonnegative",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.counterWeight_one",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.counterWeight_reflection",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.counterWeight_mul",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.native_transfer_a",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.native_transfer_b",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.canonical_raw_echo_normalized",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.nonzero_null",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.not_count_monotone",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.corner_seed_values",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.shifted_corner_packet_left",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.shifted_corner_packet_right",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.not_pairCongruent_unit_shift",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.conservation_counterexample",
        "IDT.QMClosure.NativeGeneratorReadoutCountercontrol.latticeRawI3_counterexample"] }]
  plannedArtifacts := []
  dependencies := [
    "native_initial_history_presentation_origin", "fixed_corner_half_mixture_readout_selection"]
  limits := [
    "This concrete control is defined by a finite-field zero mask of the algebraic norm on the existing carrier.",
    "Its nonzero null history violates faithfulness and strict positivity; the explicit pair-congruence and conservation failures mark the scope of its canonical echo.",
    "The control isolates one independence boundary. Independence of the other remaining selection premises remains open.",
    "Physical realization, event-frequency interpretation, Born actualization and full QM closure remain open."] }

def nativeTransferPairSufficiencyOrigin : ResearchTask := {
  id := "native_transfer_pair_sufficiency_origin"
  stage := .openPhysicalBridge
  review := .openObligation
  assumptions := [
    "The exact native readout route supplies the initial two-generator grammar/destructive relation, a real normalized readout, two all-input native transfer laws and fixed-corner equal-half pair sufficiency under one continuation.",
    "The finite-field mask countercontrol identifies a pair-sufficiency obstruction compatible with normalized native transfer and the canonical raw echo."]
  conclusions := [
    "Seek a physically justified operational origin for the normalized native transfer laws and completeness of the prescribed probe-pair means under continuation.",
    "Test independence of the remaining supplied premises individually using explicit controls.",
    "Formulate and test finite-precision versions of generator transfer and fixed-probe pair sufficiency, including stability of the selected readout under approximate hypotheses.",
    "Connect external equal-half preparation averaging with a justified operational mixture contract while retaining its distinction from coherent composition."]
  checkedEvidence := []
  plannedArtifacts := []
  dependencies := [
    "native_single_continuation_readout_selection", "native_generator_readout_countercontrol"]
  limits := [
    "This entry records the open physical and robust operational-origin research obligations.",
    "The grammar/destructive relation, real normalization and universal contexts retain their stated supplied status until independently justified.",
    "Exact algebraic readout selection alone leaves event frequencies, Born actualization, Hilbert representation, full QM closure and physical scales open."] }

def nativeRegularReadoutCountercontrol : ResearchTask := {
  id := "native_regular_readout_countercontrol"
  stage := .conditionalKernelTheorem
  review := .parentAccepted
  assumptions := [
    "Use the existing initial history presentation and its faithful complex evaluation. For every real c define N(z)=normSq(z), H(z)=Im(z^4), Q(z)=H(z)^2/N(z)^3 with total division giving Q(0)=0, F_c=N+c*Q, and W_c(p)=F_c(complexEval(p))."]
  conclusions := [
    "For every real c, F_c is globally continuous and is an explicit ambient extension of W_c through complexEval; the theorem states an extension property on the ambient complex plane.",
    "For every real c, W_c has zero/unit values, normalized generator readings one half, both all-input native transfer laws, reflection invariance and the canonical nondegenerate normalized raw echo.",
    "For every real c, F_c(t)=t^2 on the real axis, W_c(n)=n^2 on natural counts, natural-count readout order is equivalent to natural order, and W_c(half^k*p)=W_c(p)/4^k for every k and p.",
    "For c>=0, the checked bounds N<=F_c<=(1+c)*N give nonnegative W_c with W_c(p)=0 iff p=0.",
    "For c>0, W_c differs from the ordinary squared norm. Both fixed-corner seed pair sums are [2,2,2,2], while their +1 packets are [2,6,2,6+alpha] and [2,6+alpha,2,6], where alpha=576*c/125>0, so the universal single-continuation pair law fails.",
    "For every real c, coherent mixer input (1,2) has input total five and output total 5+alpha, raw I3 at (1,1,phase) equals alpha, and the multiplication defect at (2+phase)^2 equals 1152*c*(527+288*c)/15625. For c>0 these witness failures of general conservation, vanishing raw I3 and global multiplicativity."]
  checkedEvidence := [
    { sourcePath := "Proofs/QMClosure/NativeRegularReadoutCountercontrol.lean"
      declarations := [
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.norm_fourth_decomposition",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.angularCorrection_le_norm",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.ambientWeight_bounds",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.ambientWeight_continuous",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.ambientWeight_real",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_normalized_generator_transfer",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_normalized_raw_echo",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_reflection",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_nonnegative",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_zero_iff",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_nat_order_iff",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_has_continuous_extension",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_dyadic_scale",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_not_norm",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.corner_seed_values",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.shifted_corner_packet_left",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.shifted_corner_packet_right",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_not_single_continuation",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.mixer_conservation_counterexample",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.rawI3_counterexample",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_multiplication_defect",
        "IDT.QMClosure.NativeRegularReadoutCountercontrol.counterWeight_not_multiplicative"] }]
  plannedArtifacts := []
  dependencies := ["native_single_continuation_readout_selection"]
  limits := [
    "Continuity is an ambient extension property; an intrinsic topology on the abstract presentation remains an additional contract.",
    "Differentiability, Lipschitz-gradient, convexity and Banach-norm claims remain in separate analytic tasks with empty checked evidence.",
    "The checked order-equivalence theorem concerns natural counts; the ambient real-axis formula and presentation dyadic-scaling formula retain their own domains.",
    "The targeted dependency audit uses a named exclusion list of seventeen prior modules with explicit permitted definitions and native-transfer/echo lemmas.",
    "The positive alpha-valued controls belong to this family; the finite-field mask retains its own packets and raw I3 value minus five.",
    "The raw echo leaves outcome frequencies, physical readout origins, Born actualization, Hilbert representation, full QM closure and physical scales open."] }

def nativeRegularReadoutRegularity : ResearchTask := {
  id := "native_regular_readout_regularity"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Use the ambient real-plane family F_c=N+c*Q, where Q=r^2*sin(4*theta)^2 away from zero and Q(0)=0, with real parameter c."]
  conclusions := [
    "The parent-reviewed analytic argument gives global C1,1 regularity, gradient Lipschitz bound 2+32*abs(c), and real analyticity away from zero. For c nonzero, twice Frechet differentiability at zero fails despite the existence of every directional second derivative.",
    "In an orthonormal polar frame, the analytic Hessian of Q is [[1-u,4*v],[4*v,1+31*u]], with u=cos(8*theta), v=sin(8*theta), and bounds -30*I<=Hessian(Q)<=32*I.",
    "At c=1/32 the analytic off-origin lower Hessian bound is 17/16, giving global strong convexity. The function sqrt(F_c) is a Banach norm over the real vector space R^2, with squared-norm parallelogram defect 36/125 at 1 and 2*i."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/NativeRegularReadoutRegularity.lean"]
  dependencies := ["native_regular_readout_countercontrol"]
  limits := [
    "Every claim in this entry awaits a Lean artifact. The checked countercontrol supplies ambient continuity and exact finite witnesses.",
    "The Hessian comparison uses determinant identities 15*(1+u)*(63-u) and 15*(1-u)*(63+u) for the shifted matrices.",
    "The Banach-norm claim concerns the ambient real plane and real scalar homogeneity. The presentation restriction has its Gaussian-dyadic carrier.",
    "Directional second derivatives alone do not supply the common quadratic expansion, even with exact dyadic scaling and native calibration.",
    "Physical regularity origins, outcome frequencies, Born actualization and full QM closure remain open."] }

def nativeVacuumQuadraticReadoutSelection : ResearchTask := {
  id := "native_vacuum_quadratic_readout_selection"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Supply an ambient real-plane readout R and one common homogeneous real quadratic form q with R(z)-q(z)=o(norm(z)^2) at the vacuum z=0.",
    "Supply exact dyadic scaling R(z/2)=R(z)/4 for every z.",
    "Supply the native values R(1)=R(i)=1 and R(1+i)=2."]
  conclusions := [
    "The parent-reviewed analytic contraction argument gives R=q at every ambient point by following exact dyadic contractions into the common quadratic vacuum expansion.",
    "The three supplied native values select q(x,y)=x^2+y^2.",
    "The analytic regular family at c=1/32 has every directional second derivative with nonbilinear dependence. Directional second derivatives alone do not supply the common quadratic expansion, even with exact dyadic scaling and native calibration."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/NativeVacuumQuadraticReadoutSelection.lean"]
  dependencies := ["native_regular_readout_countercontrol", "native_regular_readout_regularity"]
  limits := [
    "The selector and its directional-regularity comparison await Lean artifacts.",
    "The common homogeneous quadratic tangent is a supplied structural premise; its physical derivation remains open.",
    "Transport to the abstract presentation requires an explicit ambient extension contract with the corresponding scaling and native values.",
    "Physical readout origins, outcome frequencies, Born actualization, Hilbert representation and full QM closure remain open."] }

def nativeCircuitPassivityReadoutWall : ResearchTask := {
  id := "native_circuit_passivity_readout_wall"
  stage := .analyticAwaitingFormalization
  review := .notYetKernelChecked
  assumptions := [
    "Proposed odd-prime downward valuation response W=N*p^(-v_p(N)) on Gaussian-dyadic coefficients.",
    "Finite native basis-input circuits with source-normalized total passivity and perfect closed return."]
  conclusions := [
    "Analytic proposal bounds this response by N on Gaussian-dyadic coefficients.",
    "Analytic proposal passes every finite native basis-source total bound and closed return while violating count order and allowing raw deficits.",
    "Stronger state-relative passivity of an operation and its inverse on all reachable states implies conservation."]
  checkedEvidence := []
  plannedArtifacts := ["Proofs/QMClosure/NativeCircuitPassivityReadoutWall.lean"]
  dependencies := ["rational_count_order_readout_origin"]
  limits := [
    "Basis-source bounds and state-relative passivity are distinct quantified contracts.",
    "All conclusions remain analytic until formalized.",
    "Physical readout origin, Born interpretation and full QM remain open."] }

def researchTasks : List ResearchTask := [
  operationalPositiveReadout, mixerRecordNaturality, positiveQuadraticPolarization,
  nonadditiveClassicalControl, jointReadoutFrontier, positiveGramKernel,
  rawMedialAddition, diagonalNormalization, canonicalHilbertCompletion,
  rawOperationalHilbertFacade, normalizedMixerGeneratedProcessWall,
  canonicalHilbertUniqueness, compositeProductKernel, compositeProductControls,
  operationalContextQuotient, operationalContextControls, recordEffects,
  readoutEffectControls, normalizedRecordEffects, coherentPortRayBoundary,
  scalarActualizationRefinement, calibratedEffectActualization,
  dyadicEffectDomainActualization, contextualActualizationControl,
  generatedEventConeControl, conditionalRecordProbabilities,
  nativeMixerEventConeExclusion, nativeMixerGroupPortGeometry,
  dyadicMixtureLinearization, vacuumPortEffectCompletion, nativeMixerInfiniteOrder,
  nativeWireEffectSpan, nativeAttenuationCalibratedSelection,
  nativeContextualProbabilityControl, rawNativeScalarCircuitBridge,
  nativeEventProbabilityBridge, nativeThreeWireSpectatorLocality, nativeDyadicSynthesis,
  nativeDyadicThreeMatrixSynthesis, nativeDyadicWiderFrontier, nativeDyadicSixWireObstruction,
  nativeThreeWireResidueProbability, nativeThreeWireProbabilityExtensionWall,
  nativeStableAmplitudeOrbitWall, nativeBinaryPhaseCountMass, nativeVacuumProbabilityFamily,
  nativeBinaryRefinementSelection, nativeCoherentScalarSufficiency,
  gaussianIntegerQuadraticSelection, nativeGaussianDyadicClosure,
  nativeGaussianProbabilitySelection, nativeHyperrealProbabilityWall,
  nativeArchimedeanProbability, rawNativeDyadicSemantics, rawNativeProbabilitySelection,
  rawNativeProbabilityExistence, originalGateProbabilityWall,
  weightFreeRawProbability, sourceLocalOriginalSemantics,
  mixedControlProbabilityWall, rawDiagonalDecomposition,
  nativeProbabilityPremiseIndependence, rawNetworkMedialWall,
  continuousBalancedNonmedialWall, rawObservableMedialWall,
  observedRawProbabilitySelection, responseContextProbability, responseSourceLocalProbability,
  responseDiagonalSignatureWall,
  responseRecipeContextReflection, nativeRecipeObservationBoundary,
  responseRecipeComparison, nativeTwoPointObservationControl,
  allocatedPreparationContexts, nativeAllocatedSourceArithmetic, allocatedGeneratedContexts,
  denseReferenceContextEquivalence, responseAllocatedFaithfulness,
  nativeAllocatedBallObservation, nativeAllocatedSignatureLaw,
  nativeAllocatedStableObservation,
  nativeAllocatedContextIdeals,
  nativeReferenceSettling, responseAllocatedStableBridge,
  nativeReferenceRecurrenceWall,
  nativeReferenceSettlingScopeExtensions,
  nativeBinaryValuationNonsettling,
  nativeBinaryValuationDensity,
  nativeFiniteObservationUnderdetermination, nativeReferenceSettlingRegularityScope,
  nativeContextAttenuationRecordBoundary,
  nativeSingleTraceProbabilityCriterion, rawSingleTraceProbabilityBridge,
  nativeOpenPatchSingleTrace,
  nativePointwisePeriodicSeparatingReadout, nativeUniformPeriodProbabilityCriterion,
  rawUniformPeriodProbabilityBridge, fixedThreeWireFiniteMemoryFrequencyWall,
  nativeFiniteStochasticPreparationWall, nativeFixedStateFiniteWindow,
  nativeFixedStateRobustWindow, nativeUnboundedEndpointRobustWindow,
  rawFixedReferencePreparation, rawDoubledNormalizationCompiler, rawRailVacuumExtensionWall,
  rawRailReadoutBridge, sourceRichnessVacuumFixed, nativeSignedVariationSelection,
  responseClassPreparationCompiler, signedRawRailVariationSelection,
  signedRawRailBoundedNegativeControl, globalDirectionReversibilityBoundary,
  reversibleResetEnvironmentCapacity, crossScalePrimitiveComparison,
  homogeneousProductInterchange, vacuumRecordUncomputeControl, generatedNonmedialAxisProbe,
  sparseMarginalMedialCriterion, rawSparseMarginalReconstruction, rawSparseSignedControl,
  rawSparseConservationSelection, rawSparseInsertionOrigin, rawSparseConservationTests,
  rawSparseSelfReferenceSelector, rawPairPlaneAmalgamWall,
  rawContinuousPlanePhaseWall, rawContinuousPlaneLocalTheory,
  rawVacuumRegularityBridge, rawMidpointConvexityBridge,
  rawMetricGramArity, rawFourPointGramBridge, rawPlanePhaseGramControl,
  rawMidpointGramCompatibility, rawPlanePhaseMidpointControl, rawRealPlaneMetricControl,
  rawDyadicMidpointCompatibility, rawTripodMidpointControl, rawPlanePhaseParameterWall,
  rawLocalMidpointCompatibility, rawPlanePhaseLocalMidpointControl,
  threeSourceDistributiveSwapRoot, threeSourceExchangeReadoutBoundary,
  oneSidedDistributiveSwapControl, rawProcessComparisonBridge,
  pairComparisonReconstruction, classicalAffinityLogWall,
  finiteOutcomeAffinityRigidity, relativeEntropyDataProcessing,
  classicalStatisticalProcessBridge, finiteOutcomeChannelWall,
  nativeGaussianIndependenceCharacterization, nativeStationaryNoiseClassification,
  nativeMarginalStationarityNoiseOrigin, nativeMarginalMeanDensity,
  countableHistoryNativeNoiseWall,
  referenceEntropyFactorizationOrigin, detectorEndpointSupportWall,
  detectorConservationClosureWall, gaussianDetectorRandomizationFront,
  gaussianStatisticalRealizationAndDetectorBoundary,
  unitVarianceGaussianStatisticalWitness, invariantEffectReadoutBridge,
  gaussianSoftDetectorBoundary,
  rawPlanePhaseProcessComparisonControl, rawClassicalProcessEnvelopeOmissionRoute,
  rawPowerLossReadoutControl, boundedComparisonReferenceWall,
  classicalMarginalComparisonWall, vacuumSupportEffectBoundary,
  finiteCovariantNoiseWall, binaryNoiseMixingWall,
  covariantNoiseApproximationControl,
  equivariantOutcomeSelectionWall, primitivePresentationAlternatives,
  particleAsProcessResultHypothesis, standingMatterRegimeConstraint,
  recordMarginalActualizationWall, compositionExchangeScope,
  pairExchangeCombinations, productFeatureExchange, productExchangeObservationBoundary,
  nativePreparationNaturality, responsePhaseQuotientWall,
  portFrameAlignment, nativeSingleSourceReferenceWall, referenceOccurrenceCompilation,
  nativeRecipeContextRealization, nativeReferenceSeparation, nativeRecipeSubstitution,
  referenceProvenanceAndSubstitution, recordWindowStability,
  normalizedEchoReadoutOrigin, gksOperationalSequenceBridge,
  internalReferenceSupportOrigin, internalReferencePairwiseEntropyFrontier,
  boundedLikelihoodProcessRigidity, singleEchoReadoutOrigin,
  rationalFiniteReadoutNonuniqueness, rationalCountOrderReadoutOrigin,
  reversibleEchoAccountingBoundary, singleCalibrationScalarFaithfulnessOrigin,
  localBranchOperatorFaithfulnessOrigin, sourceHistoryFaithfulnessOrigin,
  nativeInitialHistoryPresentationOrigin, localBranchFiniteWindowBoundary,
  finiteHistoryReadoutRegularityFrontier,
  finiteTranslationSpectralExtraction, finiteTranslationDilationSupport,
  multiplicativeResidueQuadraticAlgebra, finiteRankModFiveReadoutControl,
  fourProbeTomographyMixtureWall, finiteTranslationUniversalRankGap,
  finiteGateLocalizationReadoutWall, localMixtureCongruenceReadoutOrigin,
  smallRankSymmetryReadoutSelection, multiplicativeMixtureReadoutSelection,
  fixedCornerHalfMixtureReadoutSelection, nativeGeneratorMixtureReadoutSelection,
  nativeSingleContinuationReadoutSelection, nativeGeneratorReadoutCountercontrol,
  nativeTransferPairSufficiencyOrigin, nativeRegularReadoutCountercontrol,
  nativeRegularReadoutRegularity, nativeVacuumQuadraticReadoutSelection,
  nativeCircuitPassivityReadoutWall]

def ledger : List ResearchTask := researchTasks ++ globalBridges ++ matterRegimeObligations

end IDT.MetaLang.V8OperationalPrimitiveResearchLedger
