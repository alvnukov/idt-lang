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
  stage := .inFormalization
  review := .notYetKernelChecked
  assumptions := [
    "The analytic route uses D=Z[i,1/2], pi=1+i and the native symmetric pair matrix T=pi^(-1)*[[i,1],[1,i]].",
    "For the three-coordinate descent, v=u/pi^k has Gaussian-integer numerators, sum(u)=pi^k and sum(norm(u_j))=2^k.",
    "The proposed matrix consequence concerns unitary three-by-three matrices over D fixing the ones vector. The proposed width-four readout consequence assumes complete evaluated-map invariance and locality under every spectator pair generator."]
  conclusions := [
    "Independently reviewed analytic descent, not checked: at positive exponent the number of pi-odd numerators is zero or two. The zero case divides every numerator by pi. In the two-odd case the odd classes modulo pi squared differ, permitting one native pair gate and a lower denominator exponent.",
    "The exponent-one two-odd branch is handled separately; the all-divisible branch includes pi times a basis vector. At exponent zero the sum and norm conditions force a basis vector.",
    "Independently reviewed analytic matrix route, not checked: right-multiplication row reduction and native inverses reduce a three-by-three matrix to a two-by-two stabilizer. Norm-one elements of D are Gaussian units, so this block is a native pair power.",
    "The proposed width-four consequence uses the synthesized three-by-three spectator block of V*U_conjTranspose after full selected-profile equality identifies the selected rows.",
    "Exact enumeration through denominator exponents zero to six corroborated the descent on 3,9,21,45,93,189,381 legal triples. These finite checks are not a universal proof."]
  checkedEvidence := []
  plannedArtifacts := [
    "Gaussian parity/divisibility and terminating three-coordinate descent with actual native-word witnesses.",
    "Three-by-three dyadic matrix synthesis and the separate actual width-four circuit/profile adapter, after the descent artifact is checked."]
  dependencies := ["native_three_wire_spectator_locality"]
  limits := [
    "The analytic descent, matrix synthesis and width-four readout consequence have no new checked artifacts yet.",
    "Four or more odd numerators require additional analysis; arbitrary-width synthesis is unresolved and is not implied by the three-coordinate argument.",
    "No compressed-profile descent, classical-mixture profile law, physical preparation or normalization control, actual-event generation, probability continuity or full-QM closure follows."] }

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
    "Actualization remains open: justify or explicitly supply actual-event complement/refinement laws on a rich shared real-weight domain, or noncontextual partially additive probabilities on an adequately rich effect domain with matched-state calibration. The accepted conditional scalar, full-effect, dyadic-domain and reconstructed-record probability theorems do not establish physical event laws, availability or calibration. Distinct bridges remain: joint accounting/additivity for physically admitted cross-context sums, and availability/order saturation supplying every operator-admissible sum and required comparison event. The checked three-context control isolates failure of joint accounting even for admitted sums. The checked generated-cone control isolates missing positive-order saturation despite global coordinate additivity, real mixing and normalization of every supplied normalized cone-valued family; its 17/16 value belongs to an excluded mathematical sum. Neither control establishes physical event availability or an actual outcome generator. The checked native-mixer finite exclusion additionally rejects the old cone assignment under its explicit real-mixture extension assumptions. The independently reviewed group/port route awaits formalization. Two-ancilla coordinate completion, abstract dyadic-midpoint linearization and nonidentity of every positive power of one exact native word are checked mathematical results. They do not close the analytic group-classification route. The native wire-effect adapters, rational span and unique rational readout under supplied zero/midpoint/domain-membership laws are checked. The checked eight-event control is nonnegative on their nonnegative finite rational combinations but assigns -1/128 to an explicit positive contraction. Those finite-span and eight-event results alone do not establish all-circuit positivity, global state positivity, a density-matrix theorem or a physically generated full event domain. The checked conditional attenuation route now supplies exact finite native circuit adapters with retained ancillary leakage, family-based rational span and basis-calibrated selection: all-depth family positivity plus normalization, nonnegative diagonals and calibration select ell(v)=v_00 on all rational coordinates, with p agreeing on its supplied domain D. This selected pure extension is mathematically positive; general mixed-state reconstruction and agreement of p outside D do not follow. The checked universal finite-cutoff countermodel passes all four family bounds through any chosen M yet fails at E_6(M+1), separating finite testing from the universal all-depth hypothesis. Physical native availability at arbitrarily large fresh-wire widths, coordinate noncontextuality, classical midpoint event/accounting laws and calibration remain supplied. The checked contextual-probability control leaves native dynamics unchanged: its normalized squared-structural-weight assignment obeys calibration, output permutations, inert vacuum padding, full-process equivalence and syntactic fair mixtures, yet the exact three-port witness has identical all-input selected amplitudes and probabilities 1/2 versus 2/3. No function of the deterministic selected-weight profile reproduces this assignment on all native circuits. It does not descend to the coordinate-domain event law. Spectator-output locality, deterministic all-input profile sufficiency and mixture-event profile sufficiency remain distinct, and probability-preserving profile descent is still a supplied bridge. The checked raw normalized-operation/scalar circuit adapter uses only the Hilbert output constructed from RawOperationalHilbert.Data: the same finite syntax preserves a supplied common-reference feature relation, and a raw basis input has selected weight normSq(scalar output)*W(reference), including null references. Relative weights require W(reference)>0. Physical normalization control, copying, arbitrary raw preparation availability and probability laws remain separate open bridges. The checked conditional native event-probability adapter supplies image factorization, the explicit zero/total/basis/attenuation/fair-mixture grammar, independent all-input structural profiles and transfer to the basis formula under supplied ProbabilityLaw. Its checked downstream canonicalProbabilityLaw at basis input establishes mathematical nonemptiness; probability functions are extensionally unique on the certified grammar and every law has [0,1] bounds. The witness is not a premise of selection and asserts no law existence on arbitrary physical event domains. The contextual control, raw scalar adapter and event-probability adapter are checked conditional results; physical justification of full-profile probability sufficiency, event availability, fair-mixture accounting and matched calibration remains open. The checked three-wire matrix classification and actual-circuit adapter transfer supplied post-T_12 spectator locality and complete evaluated-map invariance to deterministic full-input selected-profile sufficiency. The checked compressed-input real-readout control separates that conclusion from compressed-profile sufficiency for generic readouts. This result is restricted to three wires and does not replace the attenuation premise across unbounded widths, vacuum compression or classical mixtures. A separately recorded analytic dyadic denominator-descent route aims at three-by-three exact synthesis and a width-four locality consequence; its Gaussian arithmetic, native-word witnesses and matrix adapters remain unchecked. These ingredients supply no physical availability, actual probability law, universal circuit realization or probability-limit bridge.",
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
  nativeEventProbabilityBridge, nativeThreeWireSpectatorLocality, nativeDyadicSynthesis]

def ledger : List ResearchTask := researchTasks ++ globalBridges

end IDT.MetaLang.V8OperationalPrimitiveResearchLedger
