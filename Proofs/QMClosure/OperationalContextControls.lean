import Proofs.QMClosure.OperationalContextQuotient
import Proofs.QMClosure.CompositeProductControls

namespace IDT.QMClosure.OperationalContextControls

noncomputable section

open OperationalContextQuotient

/-!
Supplied complex amplitudes are mathematical controls, not reconstructed
physical preparations. An unobserved Boolean label obeys NAND while amplitudes
obey the fixed standard mixer. The universal context statements below quantify
over every finite one-hole experiment and every reference in this carrier.
No algebraic structure on the whole raw carrier is required by ObservedData.
-/

abbrev V := ℂ × Bool

def nand (b c : Bool) : Bool := !(b && c)

def operation (p : V × V) : V × V :=
  ((CompositeProductControls.RawSign.n p.1.1 p.2.1, nand p.1.2 p.2.2),
    (CompositeProductControls.RawSign.n p.2.1 p.1.1, nand p.1.2 p.2.2))

def weight (x : V) : ℝ := Complex.normSq x.1

/-- Equality of amplitudes is stable under both outputs in both slots,
so hidden labels are invisible to every allowed future context. -/
theorem same_amplitude_observational {x y : V} (h : x.1 = y.1) :
    ObservationalEq operation weight x y := by
  apply relation_le_observationalEq operation weight (fun x y => x.1 = y.1)
    (fun _ _ h => congrArg Complex.normSq h) ?_ ?_ h
  · intro s x y r hxy
    cases s <;> simp only [select, operation] <;> rw [hxy]
  · intro s x y r hxy
    cases s <;> simp only [select, operation] <;> rw [hxy]

theorem vacuum : weight (0, false) = 0 := by simp [weight]

theorem nonnegative (x : V) : 0 ≤ weight x := Complex.normSq_nonneg _

theorem conserved (x y : V) :
    weight (operation (x, y)).1 + weight (operation (x, y)).2 =
      weight x + weight y :=
  CompositeProductControls.RawSign.norm_conservation (x.1, y.1)

theorem observed_square (p : V × V) :
    ObservationalEq operation weight (operation (operation p)).1 p.2 ∧
    ObservationalEq operation weight (operation (operation p)).2 p.1 := by
  constructor
  · apply same_amplitude_observational
    exact congrArg (fun q : ℂ × ℂ => q.1)
      (CompositeProductControls.RawSign.N_square (p.1.1, p.2.1))
  · apply same_amplitude_observational
    exact congrArg (fun q : ℂ × ℂ => q.2)
      (CompositeProductControls.RawSign.N_square (p.1.1, p.2.1))

theorem observed_medial (a b c d : V) :
    ObservationalEq operation weight
      (MedialSwapRoot.firstChannel operation
        (MedialSwapRoot.firstChannel operation a b)
        (MedialSwapRoot.firstChannel operation c d))
      (MedialSwapRoot.firstChannel operation
        (MedialSwapRoot.firstChannel operation a c)
        (MedialSwapRoot.firstChannel operation b d)) := by
  apply same_amplitude_observational
  exact CompositeProductControls.RawSign.first_channel_medial a.1 b.1 c.1 d.1

/-- The quotient construction applies to this actual observed-law package. -/
def observedData : ObservedData V where
  chosenZero := (0, false)
  operation := operation
  weight := weight
  vacuum := vacuum
  nonnegative := nonnegative
  conserved := conserved
  square := observed_square
  medial := observed_medial

/-- The exact raw square-swap law fails even though its observed version holds. -/
theorem exact_square_fails :
    operation (operation ((0, true), (0, false))) ≠
      (((0, true), (0, false)) : V × V).swap := by
  intro h
  have hb := congrArg (fun q : V × V => q.2.2) h
  simp [operation, nand] at hb

theorem not_exact_square : ¬ ∀ p : V × V, operation (operation p) = p.swap := by
  intro h
  exact exact_square_fails (h ((0, true), (0, false)))

/-- NAND also witnesses that observed mediality is strictly weaker than raw
first-channel equality. -/
theorem exact_medial_fails :
    MedialSwapRoot.firstChannel operation
      (MedialSwapRoot.firstChannel operation (0, true) (0, true))
      (MedialSwapRoot.firstChannel operation (0, false) (0, false)) ≠
    MedialSwapRoot.firstChannel operation
      (MedialSwapRoot.firstChannel operation (0, true) (0, false))
      (MedialSwapRoot.firstChannel operation (0, true) (0, false)) := by
  intro h
  have hb := congrArg Prod.snd h
  simp [MedialSwapRoot.firstChannel, operation, nand] at hb

theorem not_exact_medial :
    ¬ ∀ a b c d : V,
      MedialSwapRoot.firstChannel operation
        (MedialSwapRoot.firstChannel operation a b)
        (MedialSwapRoot.firstChannel operation c d) =
      MedialSwapRoot.firstChannel operation
        (MedialSwapRoot.firstChannel operation a c)
        (MedialSwapRoot.firstChannel operation b d) := by
  intro h
  exact exact_medial_fails (h (0, true) (0, true) (0, false) (0, false))

/-- Bare present weight equality forgets phase information that an allowed
single-use reference experiment can reveal. -/
theorem same_present_weight : weight (1, false) = weight (Complex.I, false) := by
  simp [weight]

def referenceProbe : Context V := .left .first .hole (1, false)

theorem referenceProbe_one : weight (referenceProbe.eval operation (1, false)) = 1 := by
  simp [referenceProbe, Context.eval, select, operation, weight,
    CompositeProductControls.RawSign.n_diagonal]

theorem referenceProbe_I : weight (referenceProbe.eval operation (Complex.I, false)) = 0 := by
  have hn : CompositeProductControls.RawSign.n Complex.I 1 = 0 := by
    apply Complex.ext <;>
      norm_num [CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im]
  simp [referenceProbe, Context.eval, select, operation, weight, hn]

theorem same_weight_not_observational :
    ¬ ObservationalEq operation weight (1, false) (Complex.I, false) := by
  intro h
  have hp := h referenceProbe
  rw [referenceProbe_one, referenceProbe_I] at hp
  norm_num at hp

theorem bare_weight_equality_not_congruent :
    ¬ ∀ x y r : V, weight x = weight y →
      weight (operation (x, r)).1 = weight (operation (y, r)).1 := by
  intro h
  have hp := h (1, false) (Complex.I, false) (1, false) same_present_weight
  change weight (referenceProbe.eval operation (1, false)) =
    weight (referenceProbe.eval operation (Complex.I, false)) at hp
  rw [referenceProbe_one, referenceProbe_I] at hp
  norm_num at hp

/-- No result here establishes physical availability, actualization, primitive
closure, or full QM. -/
inductive BoundaryRole where
  | suppliedComplexAmplitudeControl
  | universalOneHoleContextsAndFullCarrierReferences
  | observedLawsStrictlyWeakerThanExactRawLaws
  | bareWeightEqualityInsufficientForCongruence
  | noClaimOfQuotientEquivalenceToComplex
  | noPhysicalActualizationOrFullQM
  | noManifestStatusUpgrade
  deriving DecidableEq, Repr

end

end IDT.QMClosure.OperationalContextControls
