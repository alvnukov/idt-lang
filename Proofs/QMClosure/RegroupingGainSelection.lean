import Proofs.QMClosure.DuplicationGainDestructiveCore
import Proofs.QMClosure.FourthRejoinIdempotentCore

/-!
# Gain selection from two supplied regrouping columns

The input is an arbitrary semiring, two transparent fourth-rejoining coefficients,
and real readout laws. The second regrouping column is supplied independently.
All readout conclusions retain an arbitrary right preparation. The argument uses
finitely many local column and gain contexts for each preparation.
-/

namespace IDT.RegroupingGainSelection

section Algebra

variable {S : Type*} [Semiring S] {a b : S}

/-- The destructive coefficient is readout-null in every right context. -/
theorem null_defect_contexts
    (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4)
    (W : S → ℝ) (k : ℝ) (hunit : W 1 = 1)
    (hcolumn : ∀ p, W (a * p) + W (b * p) = W p)
    (hgain : ∀ p, W ((2 : S) * p) = k * W p)
    (hcontrast : W (2 : S) ≠ 2) :
    ∀ p, W ((a ^ 2 + b ^ 2) * p) = 0 := by
  have hcomm :=
    (IDT.FourthRejoinIdempotent.contract_of_transparent_fourth hsum hfour).commute
  have hk := IDT.DuplicationGainDestructive.gain_ne_two W k hunit (hgain 1) hcontrast
  obtain ⟨ha, hb⟩ :=
    IDT.DuplicationGainDestructive.destructive_duplication_identities hcomm hsum hfour
  intro p
  have hpa : (a ^ 2 + b ^ 2) * p =
      (2 : S) * (a * ((a ^ 2 + b ^ 2) * p)) := by
    calc
      (a ^ 2 + b ^ 2) * p = ((2 : S) * (a * (a ^ 2 + b ^ 2))) * p :=
        congrArg (fun x : S => x * p) ha
      _ = (2 : S) * (a * ((a ^ 2 + b ^ 2) * p)) := by simp only [mul_assoc]
  have hpb : (a ^ 2 + b ^ 2) * p =
      (2 : S) * (b * ((a ^ 2 + b ^ 2) * p)) := by
    calc
      (a ^ 2 + b ^ 2) * p = ((2 : S) * (b * (a ^ 2 + b ^ 2))) * p :=
        congrArg (fun x : S => x * p) hb
      _ = (2 : S) * (b * ((a ^ 2 + b ^ 2) * p)) := by simp only [mul_assoc]
  have hga : W ((a ^ 2 + b ^ 2) * p) =
      k * W (a * ((a ^ 2 + b ^ 2) * p)) := by
    calc
      W ((a ^ 2 + b ^ 2) * p) =
          W ((2 : S) * (a * ((a ^ 2 + b ^ 2) * p))) := congrArg W hpa
      _ = k * W (a * ((a ^ 2 + b ^ 2) * p)) := hgain _
  have hgb : W ((a ^ 2 + b ^ 2) * p) =
      k * W (b * ((a ^ 2 + b ^ 2) * p)) := by
    calc
      W ((a ^ 2 + b ^ 2) * p) =
          W ((2 : S) * (b * ((a ^ 2 + b ^ 2) * p))) := congrArg W hpb
      _ = k * W (b * ((a ^ 2 + b ^ 2) * p)) := hgain _
  have hscaled := congrArg (fun r : ℝ => k * r) (hcolumn ((a ^ 2 + b ^ 2) * p))
  have hproduct : (k - 2) * W ((a ^ 2 + b ^ 2) * p) = 0 := by
    nlinarith [hscaled]
  rcases mul_eq_zero.mp hproduct with h | h
  · exact False.elim (hk (by linarith))
  · exact h

/-- The second supplied regrouping turns destructive nullity into readout transparency. -/
theorem readout_transparency
    (W : S → ℝ)
    (hnull : ∀ p, W ((a ^ 2 + b ^ 2) * p) = 0)
    (hregroup : ∀ p, W ((a ^ 2 + b ^ 2) * p) +
      W (((2 : S) * (a * b)) * p) = W p) :
    ∀ p, W (((2 : S) * (a * b)) * p) = W p := by
  intro p
  simpa only [hnull p, zero_add] using hregroup p

/-- Readout transparency suffices for equal column halves. -/
theorem half_laws
    (hcomm : Commute a b) (hfour : a ^ 4 = b ^ 4)
    (W : S → ℝ) (k : ℝ) (hk : k ≠ 2)
    (hcolumn : ∀ p, W (a * p) + W (b * p) = W p)
    (hgain : ∀ p, W ((2 : S) * p) = k * W p)
    (htransparent : ∀ p, W (((2 : S) * (a * b)) * p) = W p) :
    (∀ p, W (a * p) = W p / 2) ∧
      (∀ p, W (b * p) = W p / 2) := by
  have hequal : ∀ p, W (a * p) = W (b * p) := by
    intro p
    have hsort := IDT.DuplicationGainDestructive.commute_context hcomm
    have hinput_a : ((2 : S) * (a * b)) * (a * p) =
        (2 : S) * (a * ((a * b) * p)) := by
      noncomm_ring [hcomm.symm.eq, hsort]
    have hinput_b : ((2 : S) * (a * b)) * (b * p) =
        (2 : S) * (b * ((a * b) * p)) := by
      noncomm_ring [hcomm.symm.eq, hsort]
    have hga : W (a * p) = k * W (a * ((a * b) * p)) := by
      calc
        W (a * p) = W (((2 : S) * (a * b)) * (a * p)) := (htransparent _).symm
        _ = W ((2 : S) * (a * ((a * b) * p))) := congrArg W hinput_a
        _ = k * W (a * ((a * b) * p)) := hgain _
    have hgb : W (b * p) = k * W (b * ((a * b) * p)) := by
      calc
        W (b * p) = W (((2 : S) * (a * b)) * (b * p)) := (htransparent _).symm
        _ = W ((2 : S) * (b * ((a * b) * p))) := congrArg W hinput_b
        _ = k * W (b * ((a * b) * p)) := hgain _
    have hfinite := IDT.DuplicationGainDestructive.finite_fourth_difference hcomm W hcolumn p
    rw [hfour] at hfinite
    have hproduct : (k - 2) *
        (W (a * ((a * b) * p)) - W (b * ((a * b) * p))) = 0 := by
      nlinarith [hga, hgb, hfinite]
    have hab : W (a * ((a * b) * p)) = W (b * ((a * b) * p)) := by
      rcases mul_eq_zero.mp hproduct with h | h
      · exact False.elim (hk (by linarith))
      · linarith
    nlinarith [hga, hgb]
  constructor
  · intro p
    linarith [hcolumn p, hequal p]
  · intro p
    linarith [hcolumn p, hequal p]

/-- The complete supplied readout contract. -/
structure Contract (a b : S) (W : S → ℝ) (k : ℝ) : Prop where
  sum : a + b = 1
  fourthRejoin : a ^ 4 = b ^ 4
  unit : W 1 = 1
  column : ∀ p, W (a * p) + W (b * p) = W p
  duplicationGain : ∀ p, W ((2 : S) * p) = k * W p
  unitDuplicationContrast : W (2 : S) ≠ 2
  regroupingColumn : ∀ p, W ((a ^ 2 + b ^ 2) * p) +
    W (((2 : S) * (a * b)) * p) = W p

/-- Readout conclusions under the two supplied regrouping columns. -/
structure Conclusion (a b : S) (W : S → ℝ) (k : ℝ) : Prop where
  nullDefect : ∀ p, W ((a ^ 2 + b ^ 2) * p) = 0
  transparentReadout : ∀ p, W (((2 : S) * (a * b)) * p) = W p
  halfA : ∀ p, W (a * p) = W p / 2
  halfB : ∀ p, W (b * p) = W p / 2
  gainFour : k = 4

/-- Conditional gain selection under the supplied coefficient relations. -/
theorem derive (W : S → ℝ) (k : ℝ) (h : Contract a b W k) :
    Conclusion a b W k := by
  have hcomm :=
    (IDT.FourthRejoinIdempotent.contract_of_transparent_fourth h.sum h.fourthRejoin).commute
  have hk := IDT.DuplicationGainDestructive.gain_ne_two W k h.unit
    (h.duplicationGain 1) h.unitDuplicationContrast
  have hnull := null_defect_contexts h.sum h.fourthRejoin W k h.unit h.column
    h.duplicationGain h.unitDuplicationContrast
  have htransparent := readout_transparency W hnull h.regroupingColumn
  obtain ⟨ha, hb⟩ := half_laws hcomm h.fourthRejoin W k hk h.column
    h.duplicationGain htransparent
  have hb_one : W b = 1 / 2 := by
    simpa only [mul_one, h.unit] using hb 1
  have hab : W (a * b) = 1 / 4 := by
    rw [ha b, hb_one]
    norm_num
  have hc : W ((2 : S) * (a * b)) = 1 := by
    simpa only [mul_one, h.unit] using htransparent 1
  have hfour : k = 4 := by
    have hg := h.duplicationGain (a * b)
    rw [hab, hc] at hg
    linarith
  exact ⟨hnull, htransparent, ha, hb, hfour⟩

/-- Explicit-hypothesis adapter for the supplied regrouping contract. -/
theorem gain_selection_of_regrouping
    (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4)
    (W : S → ℝ) (k : ℝ) (hunit : W 1 = 1)
    (hcolumn : ∀ p, W (a * p) + W (b * p) = W p)
    (hgain : ∀ p, W ((2 : S) * p) = k * W p)
    (hcontrast : W (2 : S) ≠ 2)
    (hregroup : ∀ p, W ((a ^ 2 + b ^ 2) * p) +
      W (((2 : S) * (a * b)) * p) = W p) :
    Conclusion a b W k :=
  derive W k ⟨hsum, hfour, hunit, hcolumn, hgain, hcontrast, hregroup⟩

end Algebra

end IDT.RegroupingGainSelection
