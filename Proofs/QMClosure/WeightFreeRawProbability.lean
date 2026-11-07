import Proofs.QMClosure.RawNativeProbabilityExistence

/-!
# Weight-free raw operational probability selection

The input consists only of a chosen zero, a complete raw operation, its exact
square-swap law, and first-channel mediality. A constant-zero weight completes
this input to the existing checked facade. It supplies no readout information;
the exact generated raw semantics and six-field probability contract suffice
for conditional selection, uniqueness, and the reference-orbit existence test.

A separate evaluator interprets the native words using arbitrary raw functions,
without supplying addition or scalar multiplication on the raw type. Its
normalized semantics agrees literally with the checked raw adapter. Erasing
any supplied conserved weight preserves those arrays and transports the laws
in both directions while retaining the identical probability field.

The original operation has the same semantics only under an explicit diagonal
transparency hypothesis. Normalization is a mathematical construction, not a
physical control. No raw norm, feature observability, outcome actualization,
arbitrary preparation availability, or full QM closure is established.
-/

namespace IDT.QMClosure.WeightFreeRawProbability

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open MedialSwapRoot RawOperationalHilbert RawNativeScalarCircuitBridge
open RawNativeProbabilitySelection MixerGeneratedProcessWall NativeVacuumProbabilityFamily

/-- The entire raw input contract: no readout, algebra, topology, or probability. -/
structure RawOperationalData (V : Type*) where
  chosenZero : V
  operation : (V × V) → (V × V)
  square : ∀ p, operation (operation p) = p.swap
  medial : ∀ a b c d,
    firstChannel operation (firstChannel operation a b) (firstChannel operation c d) =
      firstChannel operation (firstChannel operation a c) (firstChannel operation b d)

namespace RawOperationalData

variable {V : Type*}

/-- A proof adapter with no nonzero readout information. -/
def zeroWeightData (r : RawOperationalData V) : Data V where
  chosenZero := r.chosenZero
  operation := r.operation
  square := r.square
  medial := r.medial
  weight := fun _ => 0
  vacuum := rfl
  nonnegative _ := le_rfl
  conserved _ _ := rfl

theorem zeroWeightData_weight (r : RawOperationalData V) (x : V) :
    r.zeroWeightData.weight x = 0 := rfl

/-- The canonical algebra is reconstructed only when needed by the proofs. -/
abbrev Carrier (r : RawOperationalData V) := Data.Carrier r.zeroWeightData

/-- Diagonal normalization expressed directly as a raw function. -/
def normalizedOperation (r : RawOperationalData V) (p : V × V) : V × V :=
  (DiagonalNormalization.normalized (firstChannel r.operation) p.1 p.2,
    DiagonalNormalization.normalized (firstChannel r.operation) p.2 p.1)

theorem zeroWeightData_normalizedOperation (r : RawOperationalData V) (p : V × V) :
    r.zeroWeightData.normalizedOperation p = r.normalizedOperation p := rfl

/-- Forget only the supplied weight and its laws. -/
def ofWeighted (d : Data V) : RawOperationalData V where
  chosenZero := d.chosenZero
  operation := d.operation
  square := d.square
  medial := d.medial

end RawOperationalData

variable {V : Type*}

/-- Native words serve only as syntax here; `V` has no supplied algebra. -/
def evalRaw {ι : Type} [DecidableEq ι] (T : (V × V) → (V × V)) :
    Native ι → (ι → V) → (ι → V)
  | .identity, x => x
  | .pair i j _, x => fun k =>
      if k = i then (T (x i, x j)).1
      else if k = j then (T (x i, x j)).2 else x k
  | .permute e, x => fun k => x (e k)
  | .seq c e, x => evalRaw T e (evalRaw T c x)

/-- A raw basis reference uses only the explicitly chosen zero. -/
def basisInput (r : RawOperationalData V) (v : V) {ι : Type} [DecidableEq ι]
    (s : ι) : ι → V := fun i => if i = s then v else r.chosenZero

def prepared (r : RawOperationalData V) (v : V) {ι : Type} [DecidableEq ι]
    (s : ι) (c : Native ι) : ι → V :=
  evalRaw r.normalizedOperation c (basisInput r v s)

def originalPrepared (r : RawOperationalData V) (v : V) {ι : Type} [DecidableEq ι]
    (s : ι) (c : Native ι) : ι → V :=
  evalRaw r.operation c (basisInput r v s)

/-- Constructorwise agreement with the checked additive facade; the evaluator
itself requires no raw additive structure. -/
theorem evalRaw_eq_lift (d : Data V) {ι : Type} [DecidableEq ι]
    (c : Native ι) (x : ι → Data.Carrier d) :
    evalRaw (fun p => d.normalizedOperation p) c x = (liftCircuit d c).eval x := by
  induction c generalizing x with
  | identity => rfl
  | pair => rfl
  | permute => rfl
  | seq c e hc he =>
    simp only [evalRaw, liftCircuit, Circuit.eval, AddMonoidHom.comp_apply, hc, he]

/-- Literal array equality, with no Hilbert-feature or readout quotient. -/
theorem rawPrepared_eq_prepared (r : RawOperationalData V) (v : V)
    {ι : Type} [DecidableEq ι] (s : ι) (c : Native ι) :
    rawPrepared r.zeroWeightData v s c = prepared r v s c :=
  (evalRaw_eq_lift r.zeroWeightData c
    (single (V := Data.Carrier r.zeroWeightData) s v)).symm

/-- The existing six-field law, unchanged; only its raw data adapter is weight-free. -/
abbrev Law (r : RawOperationalData V) (v : V) := RawLaw r.zeroWeightData v

theorem prepared_eq_probabilities (r : RawOperationalData V) (v : V) (L : Law r v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c e : Native ι)
    (h : prepared r v s c = prepared r v s e) : L.prob s c = L.prob s e := by
  apply L.prepared_eq s c e
  simpa only [rawPrepared_eq_prepared] using h

/-- Conditional selection requires no supplied weight or faithful feature map. -/
theorem probability_eq_normSq (r : RawOperationalData V) (v : V) (L : Law r v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = Complex.normSq (c.eval (source s) i) :=
  raw_probability_eq_normSq L s c i

theorem probability_fields_equal (r : RawOperationalData V) (v : V) (L M : Law r v) :
    @RawLaw.prob V r.zeroWeightData v L = @RawLaw.prob V r.zeroWeightData v M :=
  RawNativeProbabilitySelection.probability_fields_equal L M

/-- Infinite order concerns one reference in the reconstructed group, not the
whole carrier. No such property is added to the selection theorem. -/
abbrev ReferenceInfiniteOrder (r : RawOperationalData V) (v : r.Carrier) : Prop :=
  RawNativeProbabilityExistence.ReferenceInfiniteOrder r.zeroWeightData v

theorem law_nonempty_iff_reference_infiniteOrder (r : RawOperationalData V) (v : r.Carrier) :
    Nonempty (Law r v) ↔ ReferenceInfiniteOrder r v :=
  RawNativeProbabilityExistence.rawLaw_nonempty_iff_referenceInfiniteOrder r.zeroWeightData v

/-- The reconstructed group itself does not use the erased weight. -/
theorem erase_weight_group (d : Data V) :
    (RawOperationalData.ofWeighted d).zeroWeightData.derivedGroup = d.derivedGroup := rfl

theorem erase_weight_normalizedOperation (d : Data V) (p : V × V) :
    (RawOperationalData.ofWeighted d).zeroWeightData.normalizedOperation p =
      d.normalizedOperation p := rfl

/-- Exact raw arrays are unchanged when an arbitrary conserved weight is erased. -/
theorem erase_weight_rawPrepared (d : Data V) (v : V)
    {ι : Type} [DecidableEq ι] (s : ι) (c : Native ι) :
    rawPrepared (RawOperationalData.ofWeighted d).zeroWeightData v s c =
      rawPrepared d v s c := by
  rw [rawPrepared_eq_prepared]
  exact evalRaw_eq_lift d c (single (V := Data.Carrier d) s v)

/-- Weight erasure retains every probability value and all six law fields. -/
def eraseWeightLaw (d : Data V) (v : V) (L : RawLaw d v) :
    Law (RawOperationalData.ofWeighted d) v where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h :=
    L.prepared_eq s c e (by simpa only [erase_weight_rawPrepared] using h)
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

/-- Conversely, an arbitrary compatible weight adds no probability-law constraint. -/
def restoreWeightLaw (d : Data V) (v : V) (L : Law (RawOperationalData.ofWeighted d) v) :
    RawLaw d v where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h :=
    L.prepared_eq s c e (by simpa only [erase_weight_rawPrepared] using h)
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

def weightErasureEquiv (d : Data V) (v : V) :
    RawLaw d v ≃ Law (RawOperationalData.ofWeighted d) v where
  toFun := eraseWeightLaw d v
  invFun := restoreWeightLaw d v
  left_inv L := by cases L; rfl
  right_inv L := by cases L; rfl

theorem eraseWeightLaw_probability (d : Data V) (v : V) (L : RawLaw d v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    (eraseWeightLaw d v L).prob s c i = L.prob s c i := rfl

/-- Transparency is explicit: without it the original gate may retain a decoration. -/
theorem normalizedOperation_eq_original (r : RawOperationalData V)
    (transparent : ∀ x, r.operation (x, x) = (x, x)) :
    r.normalizedOperation = r.operation := by
  have hd (x : V) : DiagonalNormalization.diagonal (firstChannel r.operation) x = x :=
    congrArg Prod.fst (transparent x)
  funext p
  change (DiagonalNormalization.diagonal (firstChannel r.operation)
      (firstChannel r.operation p.1 p.2),
    DiagonalNormalization.diagonal (firstChannel r.operation)
      (firstChannel r.operation p.2 p.1)) = r.operation p
  rw [hd, hd]
  exact (raw_operation_eq_symmetric r.operation r.square p).symm

/-- Under transparency, the literal original-gate evaluator gives the same arrays. -/
theorem prepared_eq_original (r : RawOperationalData V) (v : V)
    (transparent : ∀ x, r.operation (x, x) = (x, x))
    {ι : Type} [DecidableEq ι] (s : ι) (c : Native ι) :
    prepared r v s c = originalPrepared r v s c := by
  unfold prepared originalPrepared
  rw [normalizedOperation_eq_original r transparent]

theorem original_prepared_eq_probabilities (r : RawOperationalData V) (v : V) (L : Law r v)
    (transparent : ∀ x, r.operation (x, x) = (x, x))
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c e : Native ι)
    (h : originalPrepared r v s c = originalPrepared r v s e) :
    L.prob s c = L.prob s e := by
  apply prepared_eq_probabilities r v L s c e
  simpa only [prepared_eq_original r v transparent] using h

end

end IDT.QMClosure.WeightFreeRawProbability
