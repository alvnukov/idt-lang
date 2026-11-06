import Proofs.QMClosure.SequentialUndoCancellationBoundary

namespace IDT.QMClosure.PhaseMixerCancellation

/-!
# A selected two-channel routing forces antipodal cancellation

This is an exact conditional theorem about the supplied routing below, not a
derivation of that routing from current IDT primitives. Its operational use
assumes additive sum/phase correspondence, uniform routing on the relevant
inputs, closure under the tested sums, and that these two output channels
contain all information needed for reversal. Microscopic invertibility with a
retained path record or environment does not supply this injectivity.

The forward implication permits an arbitrary common refinement function. The
converse separately assumes a genuine additive refinement halving every input.
No Gaussian amplitudes, real completion, positive probabilities, serial
multiplication, calibration, Born rule, or QM closure is used. Independent
operational justification of this exact routing, genuine refinement, and later
complete raw-response conservation remain separate obligations. The represented
raw map need not be injective, and its residual factor need not be faithful.
-/

section Core
variable {V : Type*} [AddCommMonoid V]

def coefficientA (G : V →+ V) (h : V → V) (x : V) : V := h (x + G x)
def coefficientB (G : V →+ V) (h : V → V) (x : V) : V := h (x + G (G (G x)))
def mixer (G : V →+ V) (h : V → V) (p : V × V) : V × V :=
  (coefficientA G h p.1 + coefficientB G h p.2,
   coefficientB G h p.1 + coefficientA G h p.2)

/-- No zero, additivity, halving, readout, or calibration assumption on `h`. -/
theorem injective_mixer_forces_cancellation (G : V →+ V)
    (fourth : ∀ x, G (G (G (G x))) = x) (h : V → V)
    (hinj : Function.Injective (mixer G h)) : ∀ x, x + G (G x) = 0 := by
  intro x
  let z := x + G (G x)
  have hphase : G z = G (G (G z)) := by
    simp only [z, map_add, fourth]
    exact add_comm _ _
  have hab : coefficientA G h z = coefficientB G h z := by
    exact congrArg (fun w => h (z + w)) hphase
  have hzero : coefficientA G h 0 = coefficientB G h 0 := by
    simp [coefficientA, coefficientB]
  have heq : mixer G h (z, 0) = mixer G h (0, z) := by
    apply Prod.ext <;> simp only [mixer, hab, hzero] <;> exact add_comm _ _
  exact congrArg Prod.fst (hinj heq)

section GenuineRefinement
variable (G : V →+ V) (h : V →+ V) (halves : ∀ x, h x + h x = x)

include halves in
theorem refinement_of_double (x : V) : h (x + x) = x := by
  rw [map_add, halves]

include h halves in
theorem doubling_injective : Function.Injective (fun x : V => x + x) := by
  intro x y heq
  simpa only [refinement_of_double h halves] using congrArg h heq

include h halves in
theorem doubling_bijective : Function.Bijective (fun x : V => x + x) :=
  ⟨doubling_injective h halves, fun x => ⟨h x, halves x⟩⟩

include halves in
/-- A genuine additive refinement commutes with every additive endomorphism. -/
theorem refinement_commutes (K : V →+ V) (x : V) : h (K x) = K (h x) := by
  apply doubling_injective h halves
  change h (K x) + h (K x) = K (h x) + K (h x)
  rw [halves, ← map_add, halves]

theorem coefficientA_add (x y : V) :
    coefficientA G h (x + y) = coefficientA G h x + coefficientA G h y := by
  dsimp [coefficientA]
  rw [G.map_add]
  have heq : x + y + (G x + G y) = (x + G x) + (y + G y) := by ac_rfl
  rw [heq, map_add]

theorem coefficientB_add (x y : V) :
    coefficientB G h (x + y) = coefficientB G h x + coefficientB G h y := by
  dsimp [coefficientB]
  simp only [map_add]
  ac_rfl

include halves in
theorem doubled_coefficientA (x : V) :
    coefficientA G h x + coefficientA G h x = x + G x := halves _

include halves in
theorem doubled_coefficientB (x : V) :
    coefficientB G h x + coefficientB G h x = x + G (G (G x)) := halves _

private def doubleMap : V →+ V := AddMonoidHom.id V + AddMonoidHom.id V

private theorem doubleMap_phase (x : V) : doubleMap (G x) = G (doubleMap x) :=
  (G.map_add x x).symm

include halves in
private theorem doubleMap_A (x : V) :
    doubleMap (coefficientA G h x) = x + G x := halves _

include halves in
private theorem doubleMap_B (x : V) :
    doubleMap (coefficientB G h x) = x + G (G (G x)) := halves _

include halves in
theorem same_coefficients_cancel
    (fourth : ∀ x, G (G (G (G x))) = x)
    (cancel : ∀ x, x + G (G x) = 0) (x : V) :
    coefficientA G h (coefficientA G h x) +
      coefficientB G h (coefficientB G h x) = 0 := by
  apply doubling_injective h halves
  apply doubling_injective h halves
  change doubleMap (doubleMap (_ + _)) = doubleMap (doubleMap (0 : V))
  simp only [map_add, doubleMap_A G h halves, doubleMap_B G h halves,
    doubleMap_phase, map_zero, fourth]
  have heq : (x + G x + (G x + G (G x))) +
      (x + G (G (G x)) + (G (G (G x)) + G (G x))) =
      (x + G (G x)) + (x + G (G x)) +
        (G x + G (G (G x))) + (G x + G (G (G x))) := by ac_rfl
  rw [heq, cancel x, cancel (G x)]
  simp

include halves in
theorem crossed_coefficients_recover
    (fourth : ∀ x, G (G (G (G x))) = x)
    (cancel : ∀ x, x + G (G x) = 0) (x : V) :
    coefficientA G h (coefficientB G h x) +
      coefficientB G h (coefficientA G h x) = x := by
  apply doubling_injective h halves
  apply doubling_injective h halves
  change doubleMap (doubleMap (_ + _)) = doubleMap (doubleMap x)
  simp only [map_add, doubleMap_A G h halves, doubleMap_B G h halves,
    doubleMap_phase, fourth]
  change _ = (x + x) + (x + x)
  have heq : (x + G (G (G x)) + (G x + x)) +
      (x + G x + (G (G (G x)) + x)) =
      ((x + x) + (x + x)) +
        (G x + G (G (G x))) + (G x + G (G (G x))) := by ac_rfl
  rw [heq, cancel (G x)]
  simp

include halves in
theorem mixer_squared_swap
    (fourth : ∀ x, G (G (G (G x))) = x)
    (cancel : ∀ x, x + G (G x) = 0) (p : V × V) :
    mixer G h (mixer G h p) = (p.2, p.1) := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · change coefficientA G h (coefficientA G h x + coefficientB G h y) +
      coefficientB G h (coefficientB G h x + coefficientA G h y) = y
    rw [coefficientA_add, coefficientB_add]
    have heq : (coefficientA G h (coefficientA G h x) +
        coefficientA G h (coefficientB G h y)) +
        (coefficientB G h (coefficientB G h x) +
          coefficientB G h (coefficientA G h y)) =
        (coefficientA G h (coefficientA G h x) +
          coefficientB G h (coefficientB G h x)) +
        (coefficientA G h (coefficientB G h y) +
          coefficientB G h (coefficientA G h y)) := by ac_rfl
    rw [heq, same_coefficients_cancel G h halves fourth cancel,
      crossed_coefficients_recover G h halves fourth cancel, zero_add]
  · change coefficientB G h (coefficientA G h x + coefficientB G h y) +
      coefficientA G h (coefficientB G h x + coefficientA G h y) = x
    rw [coefficientB_add, coefficientA_add]
    have heq : (coefficientB G h (coefficientA G h x) +
        coefficientB G h (coefficientB G h y)) +
        (coefficientA G h (coefficientB G h x) +
          coefficientA G h (coefficientA G h y)) =
        (coefficientA G h (coefficientB G h x) +
          coefficientB G h (coefficientA G h x)) +
        (coefficientA G h (coefficientA G h y) +
          coefficientB G h (coefficientB G h y)) := by ac_rfl
    rw [heq, same_coefficients_cancel G h halves fourth cancel,
      crossed_coefficients_recover G h halves fourth cancel, add_zero]

include halves in
theorem mixer_fourth_identity
    (fourth : ∀ x, G (G (G (G x))) = x)
    (cancel : ∀ x, x + G (G x) = 0) (p : V × V) :
    mixer G h (mixer G h (mixer G h (mixer G h p))) = p := by
  rw [mixer_squared_swap G h halves fourth cancel,
    mixer_squared_swap G h halves fourth cancel]

def inverseMixer (p : V × V) : V × V := mixer G h (mixer G h (mixer G h p))

include halves in
theorem inverse_mixer_both_sides
    (fourth : ∀ x, G (G (G (G x))) = x)
    (cancel : ∀ x, x + G (G x) = 0) (p : V × V) :
    inverseMixer G h (mixer G h p) = p ∧
      mixer G h (inverseMixer G h p) = p :=
  ⟨mixer_fourth_identity G h halves fourth cancel p,
    mixer_fourth_identity G h halves fourth cancel p⟩

include halves in
theorem mixer_bijective_of_cancellation
    (fourth : ∀ x, G (G (G (G x))) = x)
    (cancel : ∀ x, x + G (G x) = 0) : Function.Bijective (mixer G h) := by
  constructor
  · intro p q hpq
    have heq := congrArg (inverseMixer G h) hpq
    simpa only [(inverse_mixer_both_sides G h halves fourth cancel _).1] using heq
  · intro p
    exact ⟨inverseMixer G h p, (inverse_mixer_both_sides G h halves fourth cancel p).2⟩

include halves in
theorem injective_iff_cancellation
    (fourth : ∀ x, G (G (G (G x))) = x) :
    Function.Injective (mixer G h) ↔ ∀ x, x + G (G x) = 0 :=
  ⟨injective_mixer_forces_cancellation G fourth h,
    fun hc => (mixer_bijective_of_cancellation G h halves fourth hc).1⟩

include halves in
theorem bijective_iff_cancellation
    (fourth : ∀ x, G (G (G (G x))) = x) :
    Function.Bijective (mixer G h) ↔ ∀ x, x + G (G x) = 0 :=
  ⟨fun hb => injective_mixer_forces_cancellation G fourth h hb.1,
    mixer_bijective_of_cancellation G h halves fourth⟩

include halves in
theorem square_swap_iff_cancellation
    (fourth : ∀ x, G (G (G (G x))) = x) :
    (∀ p : V × V, mixer G h (mixer G h p) = (p.2, p.1)) ↔
      ∀ x, x + G (G x) = 0 := by
  constructor
  · intro hs
    apply injective_mixer_forces_cancellation G fourth h
    intro p q hpq
    have heq := congrArg (mixer G h) hpq
    rw [hs, hs] at heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  · exact fun hc => mixer_squared_swap G h halves fourth hc
end GenuineRefinement
end Core

section RawDescent
open SequentialUndoCancellationBoundary
variable {V : Type*} [AddCommMonoid V]
variable (G : V →+ V) (fourth : ∀ x, G (G (G (G x))) = x)
variable (h : V → V) (hinj : Function.Injective (mixer G h))
variable (E : Raw → V) (Eempty : E empty = 0)
variable (Emerge : ∀ n m, E (merge n m) = E n + E m)
variable (Ephase : ∀ n, E (phaseRotate n) = G (E n))

include fourth hinj Emerge Ephase

theorem represented_antipodal_pairs_zero : E c0 = 0 ∧ E c1 = 0 := by
  have hc := injective_mixer_forces_cancellation G fourth h hinj
  have he2 : e2 = phaseRotate (phaseRotate e0) := rfl
  have he3 : e3 = phaseRotate (phaseRotate e1) := rfl
  constructor
  · rw [c0, Emerge, he2, Ephase, Ephase]
    exact hc _
  · rw [c1, Emerge, he3, Ephase, Ephase]
    exact hc _

theorem represented_pair_erasure : PairErasure E := by
  have hz := represented_antipodal_pairs_zero G fourth h hinj E Emerge Ephase
  constructor <;> intro n
  · rw [Emerge, hz.1, add_zero]
  · rw [Emerge, hz.2, add_zero]

/-- Further quotients, including a trivial represented sector, are allowed. -/
theorem represented_unique_residual_factor :
    ∃! Ebar : Residual → V, ∀ n, E n = Ebar (gamma n) :=
  (pair_erasure_iff_unique_factor E).mp
    (represented_pair_erasure G fourth h hinj E Emerge Ephase)

theorem readout_pair_erasure {B : Type*} (f : V → B) : PairErasure (f ∘ E) := by
  have he := represented_pair_erasure G fourth h hinj E Emerge Ephase
  exact ⟨fun n => congrArg f (he.1 n), fun n => congrArg f (he.2 n)⟩

theorem readout_unique_residual_factor {B : Type*} (f : V → B) :
    ∃! Fbar : Residual → B, ∀ n, (f ∘ E) n = Fbar (gamma n) :=
  (pair_erasure_iff_unique_factor (f ∘ E)).mp
    (readout_pair_erasure G fourth h hinj E Emerge Ephase f)

theorem readout_erasure_in_every_coherent_context {B : Type*} (f : V → B)
    (C : CoherentContext) (n : Raw) :
    (f ∘ E) (C.eval (merge n c0)) = (f ∘ E) (C.eval n) ∧
      (f ∘ E) (C.eval (merge n c1)) = (f ∘ E) (C.eval n) :=
  pair_erasure_in_coherent_context (f ∘ E)
    (readout_pair_erasure G fourth h hinj E Emerge Ephase f) C n

include Eempty in
/-- The operational empty correspondence is explicit, though pair descent
already follows from additive merge and the selected routing. -/
theorem represented_empty_and_descent : E empty = 0 ∧ PairErasure E :=
  ⟨Eempty, represented_pair_erasure G fourth h hinj E Emerge Ephase⟩
end RawDescent

inductive BoundaryRole where
  | supplied | proved | openBridge | excludedInference
  deriving DecidableEq

def boundaryLedger : List (BoundaryRole × String) :=
  [ (.supplied, "Selected uniform two-channel routing with a common refinement function, additive sum/phase correspondence, and closure under tested sums."),
    (.supplied, "Injectivity concerns both complete output channels; no retained path record or environment supplies reversal."),
    (.proved, "Injectivity of this routing forces antipodal cancellation without assumptions on the common refinement function."),
    (.proved, "With genuine additive halving, injectivity, bijectivity, cancellation, and mixer-square channel swap are equivalent; mixer cubed is inverse."),
    (.proved, "Represented raw bags and every subsequent readout erase both antipodal pairs, uniquely factor through gamma, and erase pairs in the supplied coherent-context grammar."),
    (.openBridge, "Independent operational reason selecting this exact routing from current primitives."),
    (.openBridge, "Genuine refinement and later complete raw-response conservation require separate justification."),
    (.excludedInference, "No injectivity of the raw representation or faithfulness of its residual factor is inferred."),
    (.excludedInference, "No Gaussian amplitudes, real completion, positive probabilities, Born rule, QM derivation, or scientific status upgrade.") ]

end IDT.QMClosure.PhaseMixerCancellation
