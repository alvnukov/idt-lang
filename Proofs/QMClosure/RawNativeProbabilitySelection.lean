import Proofs.QMClosure.RawNativeDyadicSemantics
import Proofs.QMClosure.NativeProbabilityUniqueness

/-!
# Conditional probability selection for normalized raw native circuits

`Native` words are syntax labels here. Their semantics is `rawPrepared`, which
uses the normalized operation reconstructed from `RawOperationalHilbert.Data`
and a single raw reference with the chosen raw zero on all other wires.
Complex amplitudes are derived coordinate computations used by the proof;
they are not supplied raw preparation primitives.

`RawLaw` supplies the same six probability conditions as the scalar `Law`,
with prepared-state equivalence stated using literal raw arrays. Exact
Gaussian-dyadic semantics transfers scalar prepared-state equality to that
raw equality, so the established native selection theorem applies without
feature injectivity, probability descent through feature equality, or a new
scalar-sufficiency premise.

The result is conditional on `RawLaw`. No generic witness or nonemptiness is
asserted. Absolute weight agreement includes null references; only division
by the reference weight requires its strict positivity. The normalized raw
operation may differ from the original raw gate. Physical normalization
control, gate or preparation availability, actual outcomes, and full QM
closure remain outside this adapter.
-/

namespace IDT.QMClosure.RawNativeProbabilitySelection

noncomputable section
open RawOperationalHilbert RawNativeScalarCircuitBridge
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open scoped BigOperators

variable {V : Type*}

/-- Actual raw-array semantics for the unchanged finite circuit syntax. -/
def rawPrepared (d : Data V) (v : V) {ι : Type} [DecidableEq ι]
    (s : ι) (c : Native ι) : ι → Data.Carrier d :=
  (liftCircuit d c).eval (single (V := Data.Carrier d) s v)

/-- Only prepared-state equivalence changes its semantics. All six probability
conditions remain supplied, including their compatibility at every finite width. -/
structure RawLaw (d : Data V) (v : V) where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Native ι → ι → ℝ
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) i,
    0 ≤ prob s c i
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι),
    ∑ i, prob s c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c e : Native ι),
    rawPrepared d v s c = rawPrepared d v s e → prob s c = prob s e
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (e : Equiv.Perm ι) i,
    prob s (.seq c (.permute e)) i = prob s c (e i)
  spectator_pair : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i j k : ι) (hij : i ≠ j),
    k ≠ i → k ≠ j → prob s (.seq c (.pair i j hij)) k = prob s c k
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Native ι) i,
    prob (.inl s) (padCircuit κ c) (.inl i) = prob s c i

variable {d : Data V} {v : V}

/-- The raw-state equality field supplies the scalar one through the checked
exact raw adapter. No equality of Hilbert features is used as a probability law. -/
def RawLaw.toScalarLaw (L : RawLaw d v) : Law where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h :=
    L.prepared_eq s c e (RawNativeDyadicSemantics.scalar_prepared_eq_raw d v s c e h)
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Conditional selection on actual basis-reference native words. -/
theorem raw_probability_eq_normSq (L : RawLaw d v) (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = Complex.normSq (c.eval (source s) i) :=
  NativeProbabilityUniqueness.native_probability_eq_normSq L.toScalarLaw s c i

/-- Absolute raw weights agree without dividing by the reference weight.
In particular this statement includes null references and all-null data. -/
theorem raw_probability_weight_identity (L : RawLaw d v)
    (s : ι) (c : Native ι) (i : ι) :
    d.weight (rawPrepared d v s c i) = L.prob s c i * d.weight v := by
  rw [raw_probability_eq_normSq L s c i]
  exact RawNativeScalarCircuitBridge.single_circuit_weight d c s v i

/-- The normalized weight ratio is asserted only for a positive reference weight. -/
theorem raw_probability_eq_weight_ratio (L : RawLaw d v)
    (s : ι) (c : Native ι) (i : ι) (positive : 0 < d.weight v) :
    L.prob s c i = d.weight (rawPrepared d v s c i) / d.weight v := by
  rw [raw_probability_weight_identity L s c i]
  exact (mul_div_cancel_right₀ _ (ne_of_gt positive)).symm

/-- Any two supplied raw laws agree; existence of either remains a premise. -/
theorem raw_probabilities_equal (L M : RawLaw d v) (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = M.prob s c i :=
  (raw_probability_eq_normSq L s c i).trans (raw_probability_eq_normSq M s c i).symm

/-- Extensional uniqueness is restricted to the supplied circuit-indexed field. -/
theorem probability_fields_equal (L M : RawLaw d v) :
    @RawLaw.prob V d v L = @RawLaw.prob V d v M := by
  funext α instF instD s c i
  exact raw_probabilities_equal L M s c i

end

end IDT.QMClosure.RawNativeProbabilitySelection
