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
    "Distinguish fixed-context equivalence, common-transformation covariance and ray redundancy; state sector-preservation requirements separately from channel covariance."]
  dependencies := ["port_frame_alignment", "native_single_source_reference_wall",
    "reference_occurrence_compilation", "native_recipe_context_realization",
    "native_reference_separation", "native_recipe_substitution",
    "product_exchange_observation_boundary",
    "native_preparation_naturality", "source_local_original_semantics",
    "response_source_local_probability", "response_diagonal_signature_wall",
    "response_recipe_context_reflection", "native_recipe_observation_boundary",
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
  equivariantOutcomeSelectionWall, primitivePresentationAlternatives,
  particleAsProcessResultHypothesis, standingMatterRegimeConstraint,
  recordMarginalActualizationWall, compositionExchangeScope,
  pairExchangeCombinations, productFeatureExchange, productExchangeObservationBoundary,
  nativePreparationNaturality, responsePhaseQuotientWall,
  portFrameAlignment, nativeSingleSourceReferenceWall, referenceOccurrenceCompilation,
  nativeRecipeContextRealization, nativeReferenceSeparation, nativeRecipeSubstitution,
  referenceProvenanceAndSubstitution, recordWindowStability]

def ledger : List ResearchTask := researchTasks ++ globalBridges ++ matterRegimeObligations

end IDT.MetaLang.V8OperationalPrimitiveResearchLedger
