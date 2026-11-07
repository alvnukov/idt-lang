import Proofs.QMClosure.ResponseNativeProbabilitySelection

/-!
# A reference-sign boundary for supplied response laws

The ambient response Data still supplies its structural square and medial laws.
The zero-reference contradiction uses only normalization, prepared consistency,
output permutation and vacuum padding, with identity/permutation semantics. It
uses neither observed transparency nor the other two probability fields.

Separately, the reconstructed additive half makes doubling injective, so a
negative-fixed contextual class is zero. Combining the two facts distinguishes
a law's reference class from its negative without observed transparency.

This concerns full response-context equivalence, not equality of one signature
value. Signature phase-blindness alone does not identify contextual classes.
The result does not exclude ordinary rays or a common sign on a complete
prepared array and its reference. It supplies no physical reference availability,
independent wire quotient, outcome interpretation or full QM closure. Existing
selection and infinite-order results retain their transparency premises.
-/

namespace IDT.QMClosure.ResponsePhaseQuotientWall

noncomputable section

open ResponseContextQuotient ResponseNativeProbabilitySelection
open NativeVacuumProbabilityFamily (Native padCircuit)
open scoped BigOperators

variable {V Ω : Type*} {d : Data V Ω} {v : V}

/-- Only prepared consistency and permutation covariance are needed here. -/
theorem response_equal_coordinate_probabilities (L : Law d v)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (source : ι) (c : Native ι) (i j : ι)
    (hcoord : ResponseEq d.operation d.signature
      (prepared d v source c i) (prepared d v source c j)) :
    L.prob source c i = L.prob source c j := by
  have he : ∀ k, ResponseEq d.operation d.signature
      (prepared d v source (.seq c (.permute (Equiv.swap i j))) k)
      (prepared d v source c k) := by
    intro k
    change ResponseEq d.operation d.signature
      (prepared d v source c (Equiv.swap i j k)) (prepared d v source c k)
    by_cases hki : k = i
    · subst k
      intro context
      simpa only [Equiv.swap_apply_left] using (hcoord context).symm
    by_cases hkj : k = j
    · subst k
      intro context
      simpa only [Equiv.swap_apply_right] using hcoord context
    · intro context
      simp only [Equiv.swap_apply_def, if_neg hki, if_neg hkj]
  have hs := congrFun (L.prepared_eq source (.seq c (.permute (Equiv.swap i j))) c he) i
  have hp := L.output_perm source c (Equiv.swap i j) i
  rw [Equiv.swap_apply_left] at hp
  exact hs.symm.trans hp

/-- Four supplied law fields contradict a contextually zero reference.
Only identity, permutation and vacuum semantics are used in the contradiction. -/
theorem no_law_of_reference_response_zero (d : Data V Ω) (v : V)
    (reference_zero : ResponseEq d.operation d.signature v d.chosenZero) :
    ¬ Nonempty (Law d v) := by
  rintro ⟨L⟩
  let source : Unit ⊕ Unit := .inl ()
  let other : Unit ⊕ Unit := .inr ()
  have hone : L.prob (() : Unit) .identity () = 1 := by
    simpa using L.normalized (() : Unit) .identity
  have hleft : L.prob source .identity source = 1 := by
    have hv := L.vacuum (κ := Unit) (() : Unit) .identity ()
    simpa only [source, padCircuit] using hv.trans hone
  have hequal : L.prob source .identity source = L.prob source .identity other :=
    response_equal_coordinate_probabilities L source .identity source other (by
      simpa [source, other, prepared, WeightFreeRawProbability.evalRaw, basisInput]
        using reference_zero)
  have htotal : L.prob source .identity source + L.prob source .identity other = 1 := by
    simpa [source, other, Fintype.sum_sum_type] using L.normalized source .identity
  linarith

/-- Genuine reconstructed halving excludes nonzero negative-fixed elements. -/
theorem neg_fixed_iff_zero {U : Type*}
    (r : WeightFreeRawProbability.RawOperationalData U) (x : r.Carrier) :
    x = -x ↔ x = 0 := by
  constructor
  · intro hx
    apply PhaseMixerCancellation.doubling_injective
      (OperationalQuadraticReconstruction.half r.zeroWeightData.normalizedOperation)
      r.zeroWeightData.reconstruction.halves
    change x + x = (0 : r.Carrier) + (0 : r.Carrier)
    calc
      x + x = x + (-x) := congrArg (fun y : r.Carrier => x + y) hx
      _ = 0 := add_neg_cancel x
      _ = 0 + 0 := (zero_add (0 : r.Carrier)).symm
  · rintro rfl
    simp only [neg_zero]

/-- The contextual reference zero is the reconstructed quotient group's zero. -/
theorem classOf_eq_zero_iff_response_zero (d : Data V Ω) (v : V) :
    d.classOf v = (0 : d.quotientData.Carrier) ↔
      ResponseEq d.operation d.signature v d.chosenZero := by
  change d.classOf v = d.classOf d.chosenZero ↔
    ResponseEq d.operation d.signature v d.chosenZero
  exact d.classOf_eq_iff_responseEq v d.chosenZero

theorem reference_class_ne_zero (L : Law d v) :
    d.classOf v ≠ (0 : d.quotientData.Carrier) := by
  intro hzero
  exact no_law_of_reference_response_zero d v
    ((classOf_eq_zero_iff_response_zero d v).mp hzero) ⟨L⟩

/-- The reference and its negative are distinct full contextual classes.
Negation belongs to the reconstructed quotient group, not a supplied raw group. -/
theorem reference_class_ne_neg (L : Law d v) :
    d.classOf v ≠ @Neg.neg d.quotientData.Carrier inferInstance (d.classOf v) := by
  intro hneg
  exact reference_class_ne_zero L ((neg_fixed_iff_zero d.quotientData (d.classOf v)).mp hneg)

/-- Any raw representative of the negative class is contextually distinguishable. -/
theorem negative_representative_distinguishable (L : Law d v) (w : V)
    (hw : d.classOf w = @Neg.neg d.quotientData.Carrier inferInstance (d.classOf v)) :
    ¬ ResponseEq d.operation d.signature v w := by
  intro hcontext
  exact reference_class_ne_neg L
    (((d.classOf_eq_iff_responseEq v w).mpr hcontext).trans hw)

end

end IDT.QMClosure.ResponsePhaseQuotientWall
