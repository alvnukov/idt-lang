import Proofs.QMClosure.ResponseAllocatedFaithfulness
import Proofs.QMClosure.NativeAllocatedStableObservation

/-!
# A sufficient allocated-reference bridge for an ambient response law

The induced signature observes actual allocated raw preparations. Its scalar
index is well-defined under full ambient contextual diagonal fixedness at the
chosen zero and supplied reference. Equal scalar coordinates already imply
ambient response equivalence without a probability law.

Literal one-hole context compilation identifies the generated-reference
response relation with the scalar generated-carrier response relation. If that
restricted relation separates scalar values, any supplied scalar six-field
single-basis law transports to the ambient data with its entire probability
field unchanged. A nonconstant induced signature with a supplied relatively
open constant patch is one sufficient separation criterion.

This is only sufficiency for an ambient law. Ambient contexts may distinguish
values which generated references cannot distinguish. No ambient converse,
literal raw equality, physical topology on the raw carrier or signature codomain,
probability provenance, multi-source law extension, unknown cloning,
actualization, or QM closure is asserted.
-/

namespace IDT.QMClosure.ResponseAllocatedStableBridge

noncomputable section

open OperationalContextQuotient ResponseContextQuotient
open ResponseSourceLocalProbability ResponseAllocatedFaithfulness
open NativeAllocatedSourceArithmetic NativeAllocatedObservationBoundary
open NativeRecipeContextRealization (mapRefs)
open AllocatedPreparation (Program realize)
open NativeVacuumProbabilityFamily MixerGeneratedProcessWall

variable {V Ω : Type*}

/-- A selected actual scalar program, without asserting canonical history. -/
def chosenProgram (x : G) : ScalarProgram := Classical.choose x.property

theorem scalarValue_chosenProgram (x : G) :
    scalarValue (chosenProgram x) = x.val := Classical.choose_spec x.property

/-- Observe the original raw evaluation of a selected actual program. -/
def inducedSignature (d : Data V Ω) (v : V) (x : G) : Ω :=
  d.signature (rawValue d v (chosenProgram x))

/-- Independence of the selected scalar recipe uses the law-free ambient
response theorem and retains both full contextual fixedness hypotheses. -/
theorem inducedSignature_ofProgram (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (p : ScalarProgram) :
    inducedSignature d v (ofProgram p) = d.signature (rawValue d v p) := by
  unfold inducedSignature
  exact signature_eq (scalar_eq_implies_responseEq d v hz hv
    (chosenProgram (ofProgram p)) p (scalarValue_chosenProgram (ofProgram p)))

/-- Raw generated references retain their complete allocated witnesses. -/
abbrev RawG (d : Data V Ω) (v : V) :=
  AllocatedGeneratedContexts.G d.operation d.chosenZero (fun _ : Unit => v)

def rawOfProgram (d : Data V Ω) (v : V) (p : ScalarProgram) : RawG d v :=
  AllocatedGeneratedContexts.value d.operation d.chosenZero (fun _ : Unit => v) p

def rawOperationG (d : Data V Ω) (v : V) : RawG d v × RawG d v → RawG d v × RawG d v :=
  AllocatedGeneratedContexts.operationG d.operation d.chosenZero (fun _ : Unit => v)

def rawSignatureG (d : Data V Ω) (v : V) : RawG d v → Ω :=
  AllocatedGeneratedContexts.signatureG d.operation d.chosenZero (fun _ : Unit => v)
    d.signature

/-- Scalar generated-context evaluation is literal allocated compilation. -/
theorem scalar_eval_mapped_program (C : Context ScalarProgram) (p : ScalarProgram) :
    Context.eval operationG (mapRefs ofProgram C) (ofProgram p) =
      ofProgram (realize C p) := by
  apply Subtype.ext
  exact AllocatedGeneratedContexts.eval_mapped_value
    NativeMixerEventConeExclusion.mixer (0 : ℂ) (fun _ : Unit => (1 : ℂ)) C p

/-- Every scalar generated context lifts to the same finite program shape. -/
theorem scalar_context_lift (C : Context G) :
    ∃ D : Context ScalarProgram, mapRefs ofProgram D = C :=
  AllocatedGeneratedContexts.mapRefs_surjective ofProgram ofProgram_surjective C

/-- The literal raw compiled tests characterize the scalar generated relation.
No probability law or literal raw/scalar representation map is a premise. -/
theorem compiled_tests_iff_scalar_responseEq (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (p q : ScalarProgram) :
    (∀ C : Context ScalarProgram,
      d.signature (rawValue d v (realize C p)) =
        d.signature (rawValue d v (realize C q))) ↔
      ResponseEq operationG (inducedSignature d v) (ofProgram p) (ofProgram q) := by
  constructor
  · intro h C
    obtain ⟨D, hD⟩ := scalar_context_lift C
    rw [← hD, scalar_eval_mapped_program, scalar_eval_mapped_program,
      inducedSignature_ofProgram d v hz hv, inducedSignature_ofProgram d v hz hv]
    exact h D
  · intro h C
    have hc := h (mapRefs ofProgram C)
    rw [scalar_eval_mapped_program, scalar_eval_mapped_program,
      inducedSignature_ofProgram d v hz hv, inducedSignature_ofProgram d v hz hv] at hc
    exact hc

/-- Restricted raw response and scalar response agree for actual programs.
The relation is deliberately quantified over witnesses, not arbitrary raw
values with an assumed scalar coordinate. -/
theorem generated_responseEq_iff_scalar_responseEq (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (p q : ScalarProgram) :
    ResponseEq (rawOperationG d v) (rawSignatureG d v)
      (rawOfProgram d v p) (rawOfProgram d v q) ↔
        ResponseEq operationG (inducedSignature d v) (ofProgram p) (ofProgram q) := by
  exact (AllocatedGeneratedContexts.compiled_tests_iff_responseEq
    d.operation d.chosenZero (fun _ : Unit => v) d.signature p q).symm.trans
      (compiled_tests_iff_scalar_responseEq d v hz hv p q)

/-- Ambient contexts restrict to the generated-reference contexts. -/
theorem ambient_responseEq_implies_scalar_responseEq (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (p q : ScalarProgram)
    (h : ResponseEq d.operation d.signature (rawValue d v p) (rawValue d v q)) :
    ResponseEq operationG (inducedSignature d v) (ofProgram p) (ofProgram q) := by
  apply (generated_responseEq_iff_scalar_responseEq d v hz hv p q).mp
  exact AllocatedGeneratedContexts.ambient_responseEq_restrict
    d.operation d.chosenZero (fun _ : Unit => v) d.signature h

/-- Separation of generated-reference tests is sufficient for ambient
classification; the reverse direction is the existing law-free result. -/
theorem ambient_responseEq_iff_scalar_eq_of_separates (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (hsep : NativeAllocatedSignatureLaw.Separates (inducedSignature d v))
    (p q : ScalarProgram) :
    ResponseEq d.operation d.signature (rawValue d v p) (rawValue d v q) ↔
      scalarValue p = scalarValue q := by
  constructor
  · intro h
    exact congrArg Subtype.val (hsep _ _
      (ambient_responseEq_implies_scalar_responseEq d v hz hv p q h))
  · exact scalar_eq_implies_responseEq d v hz hv p q

/-- An original single-basis preparation, with all wires retained. -/
def preparedProgram {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i : ι) : ScalarProgram where
  Wires := ι
  wireFintype := inferInstance
  wireDecidableEq := inferInstance
  input := fun j => if j = s then some () else none
  circuit := c
  cursor := i

theorem rawValue_preparedProgram (d : Data V Ω) (v : V)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    rawValue d v (preparedProgram s c i) =
      ResponseNativeProbabilitySelection.prepared d v s c i := by
  have hin : AllocatedPreparation.inputState d.chosenZero (fun _ : Unit => v)
      (preparedProgram s c i) = ResponseNativeProbabilitySelection.basisInput d v s := by
    funext j
    change (if j = s then some () else none).elim d.chosenZero (fun _ : Unit => v) =
      if j = s then v else d.chosenZero
    split_ifs <;> rfl
  change WeightFreeRawProbability.evalRaw d.operation c
      (AllocatedPreparation.inputState d.chosenZero (fun _ : Unit => v)
        (preparedProgram s c i)) i =
    WeightFreeRawProbability.evalRaw d.operation c
      (ResponseNativeProbabilitySelection.basisInput d v s) i
  rw [hin]

theorem scalarValue_preparedProgram {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i : ι) :
    scalarValue (preparedProgram s c i) = c.eval (source s) i := by
  change WeightFreeRawProbability.evalRaw NativeMixerEventConeExclusion.mixer c
    (AllocatedPreparation.inputState (0 : ℂ) (fun _ : Unit => (1 : ℂ))
      (preparedProgram s c i)) i = _
  rw [NativeAllocatedSourceArithmetic.evalRaw_eq_native]
  have hin : AllocatedPreparation.inputState (0 : ℂ) (fun _ : Unit => (1 : ℂ))
      (preparedProgram s c i) = source s := by
    funext j
    change (if j = s then some () else none).elim (0 : ℂ) (fun _ : Unit => (1 : ℂ)) =
      if j = s then 1 else 0
    split_ifs <;> rfl
  rw [hin]

/-- Transport an arbitrary supplied scalar law, with unchanged probability
field. Only its prepared consistency proof needs the sufficient bridge. -/
def lawOfScalarOfSeparates (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (hsep : NativeAllocatedSignatureLaw.Separates (inducedSignature d v))
    (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law d v where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h := by
    apply L.prepared_eq s c e
    funext i
    have hi : ResponseEq d.operation d.signature
        (rawValue d v (preparedProgram s c i))
        (rawValue d v (preparedProgram s e i)) := by
      rw [rawValue_preparedProgram, rawValue_preparedProgram]
      exact h i
    have hs := (ambient_responseEq_iff_scalar_eq_of_separates
      d v hz hv hsep (preparedProgram s c i) (preparedProgram s e i)).mp hi
    simpa only [scalarValue_preparedProgram] using hs
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

theorem lawOfScalarOfSeparates_probability (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (hsep : NativeAllocatedSignatureLaw.Separates (inducedSignature d v))
    (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω d v
      (lawOfScalarOfSeparates d v hz hv hsep L) =
        @NativeVacuumProbabilityFamily.Law.prob L := rfl

theorem separates_of_patch_nonconstant (d : Data V Ω) (v : V)
    (hpatch : NativeAllocatedStableObservation.HasOpenConstantPatch (inducedSignature d v))
    (hnonconstant : ∃ x y : G, inducedSignature d v x ≠ inducedSignature d v y) :
    NativeAllocatedSignatureLaw.Separates (inducedSignature d v) :=
  (NativeAllocatedStableObservation.separates_iff_nonconstant_of_open_constant_patch
    (inducedSignature d v) hpatch).mpr hnonconstant

def lawOfScalarOfPatchNonconstant (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (hpatch : NativeAllocatedStableObservation.HasOpenConstantPatch (inducedSignature d v))
    (hnonconstant : ∃ x y : G, inducedSignature d v x ≠ inducedSignature d v y)
    (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law d v :=
  lawOfScalarOfSeparates d v hz hv (separates_of_patch_nonconstant d v hpatch hnonconstant) L

theorem lawOfScalarOfPatchNonconstant_probability (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (hpatch : NativeAllocatedStableObservation.HasOpenConstantPatch (inducedSignature d v))
    (hnonconstant : ∃ x y : G, inducedSignature d v x ≠ inducedSignature d v y)
    (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω d v
      (lawOfScalarOfPatchNonconstant d v hz hv hpatch hnonconstant L) =
        @NativeVacuumProbabilityFamily.Law.prob L := rfl

theorem law_nonempty_of_patch_nonconstant (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (hpatch : NativeAllocatedStableObservation.HasOpenConstantPatch (inducedSignature d v))
    (hnonconstant : ∃ x y : G, inducedSignature d v x ≠ inducedSignature d v y) :
    Nonempty (ResponseNativeProbabilitySelection.Law d v) :=
  ⟨lawOfScalarOfPatchNonconstant d v hz hv hpatch hnonconstant
    NativeVacuumProbabilityFamily.canonicalLaw⟩

/-- For the concrete scalar raw data, the induced signature is exactly the
restriction of the ambient point test. No probability family is used. -/
theorem inducedSignature_pointData (q : ℂ) (x : G) :
    inducedSignature (NativeRecipeObservationBoundary.pointData q) (1 : ℂ) x =
      NativeAllocatedObservationBoundary.pointSignature q x := by
  change NativeRecipeObservationBoundary.pointTest q
      (scalarValue (chosenProgram x)) =
    NativeRecipeObservationBoundary.pointTest q x.val
  rw [scalarValue_chosenProgram]

/-- The ambient point 1/3 is absent from every generated finite preparation. -/
theorem third_inducedSignature_false (x : G) :
    inducedSignature (NativeRecipeObservationBoundary.pointData (1 / 3 : ℂ))
      (1 : ℂ) x = false := by
  rw [inducedSignature_pointData]
  exact NativeAllocatedObservationBoundary.pointSignature_false_of_not_reachable
    (1 / 3 : ℂ) NativeAllocatedSourceArithmetic.third_not_reachable x

/-- Ambient probability-law existence does not imply that the induced
generated-reference signature is nonconstant: ambient contexts can use the
missing point's separating references, while generated contexts never hit it. -/
theorem third_ambient_law_generated_signature_control :
    DiagonalFixed (NativeRecipeObservationBoundary.pointData (1 / 3 : ℂ))
      (NativeRecipeObservationBoundary.pointData (1 / 3 : ℂ)).chosenZero ∧
    DiagonalFixed (NativeRecipeObservationBoundary.pointData (1 / 3 : ℂ)) (1 : ℂ) ∧
    Nonempty (ResponseNativeProbabilitySelection.Law
      (NativeRecipeObservationBoundary.pointData (1 / 3 : ℂ)) (1 : ℂ)) ∧
    (∀ x : G, inducedSignature
      (NativeRecipeObservationBoundary.pointData (1 / 3 : ℂ)) (1 : ℂ) x = false) := by
  have hfixed := observedTransparent_source_local
    (NativeRecipeObservationBoundary.pointData (1 / 3 : ℂ)) (1 : ℂ)
    (NativeRecipeObservationBoundary.point_observedTransparent (1 / 3 : ℂ))
  exact ⟨hfixed.1, hfixed.2,
    NativeRecipeObservationBoundary.point_law_nonempty (1 / 3 : ℂ),
    third_inducedSignature_false⟩

/-- One original-gate first-output step toward a supplied known recipe. -/
def rawReferenceStep (d : Data V Ω) (v : V) (r : ScalarProgram) (x : V) : V :=
  (d.operation (x, rawValue d v r)).1

/-- A supplied exact eventual observation property, expressed solely through
the original operation, original signature, and actual allocated programs.
Neither literal state convergence nor physical settling provenance is asserted. -/
def RawReferenceSettles (d : Data V Ω) (v : V) : Prop :=
  ∃ r : ScalarProgram, ∀ p : ScalarProgram, ∃ N : ℕ, ∀ n ≥ N,
    d.signature ((rawReferenceStep d v r)^[n] (rawValue d v p)) =
      d.signature (rawValue d v r)

def RawProgramNonconstant (d : Data V Ω) (v : V) : Prop :=
  ∃ p q : ScalarProgram, d.signature (rawValue d v p) ≠ d.signature (rawValue d v q)

/-- Every iterate has one unknown hole; each fixed reference occurrence
allocates the entire known preparation again. -/
def referenceContext (r : ScalarProgram) : ℕ → Context ScalarProgram
  | 0 => .hole
  | n + 1 => .left .first (referenceContext r n) r

theorem rawValue_referenceContext (d : Data V Ω) (v : V)
    (r p : ScalarProgram) (n : ℕ) :
    rawValue d v (realize (referenceContext r n) p) =
      (rawReferenceStep d v r)^[n] (rawValue d v p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change AllocatedPreparation.eval d.operation d.chosenZero (fun _ : Unit => v)
      (AllocatedPreparation.pair .first (realize (referenceContext r n) p) r) = _
    rw [AllocatedPreparation.eval_pair]
    change (d.operation (rawValue d v (realize (referenceContext r n) p),
      rawValue d v r)).1 = _
    rw [ih, Function.iterate_succ_apply']
    rfl

theorem scalar_referenceContext_iterate (r p : ScalarProgram) (n : ℕ) :
    Context.eval operationG (mapRefs ofProgram (referenceContext r n)) (ofProgram p) =
      (NativeAllocatedStableObservation.referenceStep (ofProgram r))^[n] (ofProgram p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (operationG (Context.eval operationG
      (mapRefs ofProgram (referenceContext r n)) (ofProgram p), ofProgram r)).1 = _
    rw [ih, Function.iterate_succ_apply']
    rfl

/-- Counts allocated source occurrences; this is not a wire, gate, or general
resource count. -/
theorem referenceContext_budget (r p : ScalarProgram) (n : ℕ) :
    AllocatedPreparation.budget (realize (referenceContext r n) p) =
      AllocatedPreparation.budget p + n * AllocatedPreparation.budget r := by
  rw [AllocatedPreparation.budget_realize]
  have h : AllocatedPreparation.referenceBudget (referenceContext r n) =
      n * AllocatedPreparation.budget r := by
    induction n with
    | zero => simp only [referenceContext, AllocatedPreparation.referenceBudget, Nat.zero_mul]
    | succ n ih =>
      simp only [referenceContext, AllocatedPreparation.referenceBudget, ih, Nat.succ_mul]
  rw [h]

/-- Signature correspondence carries an actual one-hole compilation witness
through every step. It does not identify the raw and scalar states. -/
theorem signature_reference_iterate (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (r p : ScalarProgram) (n : ℕ) :
    inducedSignature d v
      ((NativeAllocatedStableObservation.referenceStep (ofProgram r))^[n] (ofProgram p)) =
        d.signature ((rawReferenceStep d v r)^[n] (rawValue d v p)) := by
  rw [← scalar_referenceContext_iterate, scalar_eval_mapped_program,
    inducedSignature_ofProgram d v hz hv, rawValue_referenceContext]

/-- This equivalence only changes the grammar of the supplied settling
property; it does not derive settling from structural fixedness. -/
theorem rawReferenceSettles_iff_induced_referenceSettles (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v) :
    RawReferenceSettles d v ↔
      NativeAllocatedStableObservation.ReferenceSettles (inducedSignature d v) := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨ofProgram r, ?_⟩
    intro x
    obtain ⟨p, rfl⟩ := ofProgram_surjective x
    obtain ⟨N, hN⟩ := hr p
    refine ⟨N, ?_⟩
    intro n hn
    rw [signature_reference_iterate d v hz hv,
      inducedSignature_ofProgram d v hz hv]
    exact hN n hn
  · rintro ⟨z, hzsettles⟩
    obtain ⟨r, rfl⟩ := ofProgram_surjective z
    refine ⟨r, ?_⟩
    intro p
    obtain ⟨N, hN⟩ := hzsettles (ofProgram p)
    refine ⟨N, ?_⟩
    intro n hn
    have h := hN n hn
    rw [signature_reference_iterate d v hz hv,
      inducedSignature_ofProgram d v hz hv] at h
    exact h

theorem rawProgramNonconstant_iff_induced_nonconstant (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v) :
    RawProgramNonconstant d v ↔
      ∃ x y : G, inducedSignature d v x ≠ inducedSignature d v y := by
  constructor
  · rintro ⟨p, q, hpq⟩
    refine ⟨ofProgram p, ofProgram q, ?_⟩
    simpa only [inducedSignature_ofProgram d v hz hv] using hpq
  · rintro ⟨x, y, hxy⟩
    obtain ⟨p, rfl⟩ := ofProgram_surjective x
    obtain ⟨q, rfl⟩ := ofProgram_surjective y
    refine ⟨p, q, ?_⟩
    simpa only [inducedSignature_ofProgram d v hz hv] using hxy

theorem separates_of_rawReferenceSettles (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (hsettles : RawReferenceSettles d v) (hnonconstant : RawProgramNonconstant d v) :
    NativeAllocatedSignatureLaw.Separates (inducedSignature d v) :=
  (NativeAllocatedStableObservation.separates_iff_nonconstant_of_reference_settles
    (inducedSignature d v)
    ((rawReferenceSettles_iff_induced_referenceSettles d v hz hv).mp hsettles)).mpr
      ((rawProgramNonconstant_iff_induced_nonconstant d v hz hv).mp hnonconstant)

/-- Both raw observation properties are supplied. This construction preserves
any scalar family's whole probability field and unchanged six-field contract;
it does not derive probability provenance or extend a law to joint arrays. -/
def lawOfScalarOfRawReferenceSettles (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (hsettles : RawReferenceSettles d v) (hnonconstant : RawProgramNonconstant d v)
    (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law d v :=
  lawOfScalarOfSeparates d v hz hv
    (separates_of_rawReferenceSettles d v hz hv hsettles hnonconstant) L

theorem lawOfScalarOfRawReferenceSettles_probability (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (hsettles : RawReferenceSettles d v) (hnonconstant : RawProgramNonconstant d v)
    (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω d v
      (lawOfScalarOfRawReferenceSettles d v hz hv hsettles hnonconstant L) =
        @NativeVacuumProbabilityFamily.Law.prob L := rfl

theorem law_nonempty_of_rawReferenceSettles (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (hsettles : RawReferenceSettles d v) (hnonconstant : RawProgramNonconstant d v) :
    Nonempty (ResponseNativeProbabilitySelection.Law d v) :=
  ⟨lawOfScalarOfRawReferenceSettles d v hz hv hsettles hnonconstant
    NativeVacuumProbabilityFamily.canonicalLaw⟩

end
end IDT.QMClosure.ResponseAllocatedStableBridge
