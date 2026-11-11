import Mathlib

/-!
# Uniform duplication gain and finite destructive contexts

All hypotheses are supplied operational/algebraic contracts. In particular, this file does not
establish physical availability of a fixed duplication gain, fourth-power
rejoin, or zero detection. The ambient algebra is an arbitrary semiring with
an explicit commuting pair. Additive cancellation and additive inverses are
absent from the input contract.
-/

namespace IDT.DuplicationGainDestructive

section Algebra

variable {S : Type*} [Semiring S] {a b : S}

/-- The sorting rule retains an arbitrary right-hand context. -/
lemma commute_context (hcomm : Commute a b) (x : S) :
    b * (a * x) = a * (b * x) := by
  calc
    b * (a * x) = (b * a) * x := (mul_assoc _ _ _).symm
    _ = (a * b) * x := by rw [hcomm.symm.eq]
    _ = a * (b * x) := mul_assoc _ _ _

/-- Subtraction-free algebra preceding any readout argument. -/
theorem destructive_duplication_identities
    (hcomm : Commute a b) (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4) :
    let T := a ^ 2 + b ^ 2
    T = (2 : S) * (a * T) ∧ T = (2 : S) * (b * T) := by
  dsimp
  let T := a ^ 2 + b ^ 2
  have hsort := commute_context hcomm
  have hsquare : a ^ 2 * T = b ^ 2 * T := by
    calc
      a ^ 2 * T = a ^ 4 + a ^ 2 * b ^ 2 := by dsimp [T]; noncomm_ring
      _ = b ^ 4 + a ^ 2 * b ^ 2 := by rw [hfour]
      _ = b ^ 2 * T := by dsimp [T]; noncomm_ring [hcomm.symm.eq, hsort]
  have hlinear : a * T = b * T := by
    calc
      a * T = a * T * (a + b) := by rw [hsum]; simp
      _ = a ^ 2 * T + (a * b) * T := by
        dsimp [T]; noncomm_ring [hcomm.symm.eq, hsort]
      _ = b ^ 2 * T + (a * b) * T := by rw [hsquare]
      _ = b * T * (a + b) := by
        dsimp [T]; noncomm_ring [hcomm.symm.eq, hsort]
      _ = b * T := by rw [hsum]; simp
  have hsplit : T = a * T + b * T := by
    calc
      T = (a + b) * T := by rw [hsum]; simp
      _ = a * T + b * T := add_mul _ _ _
  constructor
  · calc
      a ^ 2 + b ^ 2 = a * T + b * T := hsplit
      _ = (2 : S) * (a * T) := by rw [← hlinear]; noncomm_ring
  · calc
      a ^ 2 + b ^ 2 = a * T + b * T := hsplit
      _ = (2 : S) * (b * T) := by rw [hlinear]; noncomm_ring

/-- Readout contrast excludes the additive-linear duplication gain. -/
lemma gain_ne_two (W : S → ℝ) (k : ℝ) (hunit : W 1 = 1)
    (hgain_one : W ((2 : S) * 1) = k * W 1)
    (hcontrast : W (2 : S) ≠ 2) : k ≠ 2 := by
  intro hk
  apply hcontrast
  simpa [hunit, hk] using hgain_one

/-- The destructive core uses four gain/column contexts and one zero test.
The full contract below supplies these finite restrictions globally. -/
theorem destructive_zero_of_finite_contexts
    (hcomm : Commute a b) (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4)
    (W : S → ℝ) (k : ℝ) (hunit : W 1 = 1)
    (hcontrast : W (2 : S) ≠ 2)
    (hgain_one : W ((2 : S) * 1) = k * W 1)
    (hgain_a : W ((2 : S) * (a * (a ^ 2 + b ^ 2))) =
      k * W (a * (a ^ 2 + b ^ 2)))
    (hgain_b : W ((2 : S) * (b * (a ^ 2 + b ^ 2))) =
      k * W (b * (a ^ 2 + b ^ 2)))
    (hcolumn : W (a * (a ^ 2 + b ^ 2)) + W (b * (a ^ 2 + b ^ 2)) =
      W (a ^ 2 + b ^ 2))
    (hzero : W (a ^ 2 + b ^ 2) = 0 → a ^ 2 + b ^ 2 = 0) :
    a ^ 2 + b ^ 2 = 0 := by
  obtain ⟨ha, hb⟩ := destructive_duplication_identities hcomm hsum hfour
  have hk := gain_ne_two W k hunit hgain_one hcontrast
  have haW : W (a ^ 2 + b ^ 2) = k * W (a * (a ^ 2 + b ^ 2)) := by
    calc
      W (a ^ 2 + b ^ 2) = W ((2 : S) * (a * (a ^ 2 + b ^ 2))) := congrArg W ha
      _ = k * W (a * (a ^ 2 + b ^ 2)) := hgain_a
  have hbW : W (a ^ 2 + b ^ 2) = k * W (b * (a ^ 2 + b ^ 2)) := by
    calc
      W (a ^ 2 + b ^ 2) = W ((2 : S) * (b * (a ^ 2 + b ^ 2))) := congrArg W hb
      _ = k * W (b * (a ^ 2 + b ^ 2)) := hgain_b
  have hscaled := congrArg (fun r : ℝ => k * r) hcolumn
  have hproduct : (k - 2) * W (a ^ 2 + b ^ 2) = 0 := by
    nlinarith [hscaled]
  apply hzero
  rcases mul_eq_zero.mp hproduct with h | h
  · exact False.elim (hk (by linarith))
  · exact h

/-- Transparency follows through a positive-coefficient square expansion. -/
theorem two_mul_ab_eq_one (hcomm : Commute a b) (hsum : a + b = 1)
    (hdestructive : a ^ 2 + b ^ 2 = 0) : (2 : S) * (a * b) = 1 := by
  have hsort := commute_context hcomm
  have hexpand : (a + b) ^ 2 = (a ^ 2 + b ^ 2) + (2 : S) * (a * b) := by
    noncomm_ring [hcomm.symm.eq, hsort]
  simpa [hsum, hdestructive] using hexpand.symm

/-- A column at a monomial, with no commutation assumed for the preparation. -/
lemma column_monomial (hcomm : Commute a b) (W : S → ℝ)
    (hcolumn : ∀ x, W (a * x) + W (b * x) = W x) (i j : ℕ) (p : S) :
    W (a ^ (i + 1) * b ^ j * p) + W (a ^ i * b ^ (j + 1) * p) =
      W (a ^ i * b ^ j * p) := by
  have ha : a * (a ^ i * b ^ j * p) = a ^ (i + 1) * b ^ j * p := by
    simp only [pow_succ', mul_assoc]
  have hb : b * (a ^ i * b ^ j * p) = a ^ i * b ^ (j + 1) * p := by
    calc
      b * (a ^ i * b ^ j * p) = (b * a ^ i) * b ^ j * p := by simp only [mul_assoc]
      _ = (a ^ i * b) * b ^ j * p := by rw [(hcomm.symm.pow_right i).eq]
      _ = a ^ i * b ^ (j + 1) * p := by simp only [pow_succ', mul_assoc]
  simpa only [ha, hb] using hcolumn (a ^ i * b ^ j * p)

/-- A finite eight-column identity. Subtraction takes place only in ℝ. -/
theorem finite_fourth_difference (hcomm : Commute a b) (W : S → ℝ)
    (hcolumn : ∀ x, W (a * x) + W (b * x) = W x) (p : S) :
    W (a * p) - W (b * p) =
      (W (a ^ 4 * p) - W (b ^ 4 * p)) +
        2 * (W (a * ((a * b) * p)) - W (b * ((a * b) * p))) := by
  have h10 := column_monomial hcomm W hcolumn 1 0 p
  have h01 := column_monomial hcomm W hcolumn 0 1 p
  have h20 := column_monomial hcomm W hcolumn 2 0 p
  have h02 := column_monomial hcomm W hcolumn 0 2 p
  have h30 := column_monomial hcomm W hcolumn 3 0 p
  have h03 := column_monomial hcomm W hcolumn 0 3 p
  have h21 := column_monomial hcomm W hcolumn 2 1 p
  have h12 := column_monomial hcomm W hcolumn 1 2 p
  norm_num only [pow_zero, pow_one, mul_one, one_mul] at h10 h01 h20 h02 h30 h03 h21 h12
  have ha : a * ((a * b) * p) = a ^ 2 * b * p := by noncomm_ring
  have hb : b * ((a * b) * p) = a * b ^ 2 * p := by
    noncomm_ring [hcomm.symm.eq, commute_context hcomm]
  rw [ha, hb]
  linarith

/-- The fourth rejoin and non-linear fixed gain force both column halves.
Every preparation uses finitely many column and gain contexts. -/
theorem half_laws (hcomm : Commute a b) (hfour : a ^ 4 = b ^ 4)
    (htwo : (2 : S) * (a * b) = 1) (W : S → ℝ) (k : ℝ) (hk : k ≠ 2)
    (hcolumn : ∀ x, W (a * x) + W (b * x) = W x)
    (hgain : ∀ x, W ((2 : S) * x) = k * W x) :
    (∀ x, W (a * x) = W x / 2) ∧ (∀ x, W (b * x) = W x / 2) := by
  have hequal : ∀ p, W (a * p) = W (b * p) := by
    intro p
    have hsort := commute_context hcomm
    have hinput_a : (2 : S) * (a * ((a * b) * p)) = a * p := by
      calc
        (2 : S) * (a * ((a * b) * p)) = a * (((2 : S) * (a * b)) * p) := by
          noncomm_ring
        _ = a * p := by rw [htwo]; simp
    have hinput_b : (2 : S) * (b * ((a * b) * p)) = b * p := by
      calc
        (2 : S) * (b * ((a * b) * p)) = b * (((2 : S) * (a * b)) * p) := by
          noncomm_ring
        _ = b * p := by rw [htwo]; simp
    have hga := hgain (a * ((a * b) * p))
    have hgb := hgain (b * ((a * b) * p))
    rw [hinput_a] at hga
    rw [hinput_b] at hgb
    have hfinite := finite_fourth_difference hcomm W hcolumn p
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
  · intro x; linarith [hcolumn x, hequal x]
  · intro x; linarith [hcolumn x, hequal x]

/-- Explicit finite algebraic contexts, without installing a Ring instance. -/
structure AlgebraicWitnesses (a b : S) : Prop where
  negativeOne : (4 : S) * a ^ 4 + 1 = 0
  additiveInverseLeft : ∀ x : S, ((4 : S) * a ^ 4) * x + x = 0
  additiveInverseRight : ∀ x : S, x + ((4 : S) * a ^ 4) * x = 0
  aInverseLeft : ((2 : S) * b) * a = 1
  aInverseRight : a * ((2 : S) * b) = 1
  bInverseLeft : ((2 : S) * a) * b = 1
  bInverseRight : b * ((2 : S) * a) = 1

theorem algebraic_witnesses (hcomm : Commute a b)
    (hdestructive : a ^ 2 + b ^ 2 = 0) (htwo : (2 : S) * (a * b) = 1) :
    AlgebraicWitnesses a b := by
  have hsort := commute_context hcomm
  have hsquare : (4 : S) * (a ^ 2 * b ^ 2) = 1 := by
    calc
      (4 : S) * (a ^ 2 * b ^ 2) = ((2 : S) * (a * b)) ^ 2 := by
        noncomm_ring [hcomm.symm.eq, hsort]
      _ = 1 := by rw [htwo]; simp
  have hnegative : (4 : S) * a ^ 4 + 1 = 0 := by
    calc
      (4 : S) * a ^ 4 + 1 = ((4 : S) * a ^ 2) * (a ^ 2 + b ^ 2) := by
        rw [← hsquare]
        noncomm_ring
      _ = 0 := by rw [hdestructive]; simp
  refine ⟨hnegative, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    calc
      ((4 : S) * a ^ 4) * x + x = ((4 : S) * a ^ 4 + 1) * x := by noncomm_ring
      _ = 0 := by rw [hnegative]; simp
  · intro x
    rw [add_comm]
    calc
      ((4 : S) * a ^ 4) * x + x = ((4 : S) * a ^ 4 + 1) * x := by noncomm_ring
      _ = 0 := by rw [hnegative]; simp
  · calc
      ((2 : S) * b) * a = (2 : S) * (a * b) := by noncomm_ring [hcomm.symm.eq, hsort]
      _ = 1 := htwo
  · calc
      a * ((2 : S) * b) = (2 : S) * (a * b) := by noncomm_ring
      _ = 1 := htwo
  · calc
      ((2 : S) * a) * b = (2 : S) * (a * b) := mul_assoc _ _ _
      _ = 1 := htwo
  · calc
      b * ((2 : S) * a) = (2 : S) * (a * b) := by noncomm_ring [hcomm.symm.eq, hsort]
      _ = 1 := htwo

/-- Complete supplied contract. The gain is one unknown universal real scalar. -/
structure Contract (a b : S) (W : S → ℝ) (k : ℝ) : Prop where
  commute : Commute a b
  sum : a + b = 1
  fourthRejoin : a ^ 4 = b ^ 4
  unit : W 1 = 1
  zeroDetection : ∀ x, W x = 0 → x = 0
  column : ∀ x, W (a * x) + W (b * x) = W x
  duplicationGain : ∀ x, W ((2 : S) * x) = k * W x
  unitDuplicationContrast : W (2 : S) ≠ 2

structure Conclusion (a b : S) (W : S → ℝ) (k : ℝ) : Prop where
  destructiveZero : a ^ 2 + b ^ 2 = 0
  transparency : (2 : S) * (a * b) = 1
  halfA : ∀ x, W (a * x) = W x / 2
  halfB : ∀ x, W (b * x) = W x / 2
  gainFour : k = 4
  witnesses : AlgebraicWitnesses a b

/-- Conditional finite derivation. It supplies neither a unique norm nor a
physical realization. Inverse witnesses are finite algebraic contexts only. -/
theorem derive {W : S → ℝ} {k : ℝ} (h : Contract a b W k) : Conclusion a b W k := by
  have hk := gain_ne_two W k h.unit (h.duplicationGain 1) h.unitDuplicationContrast
  have hT := destructive_zero_of_finite_contexts h.commute h.sum h.fourthRejoin
    W k h.unit h.unitDuplicationContrast (h.duplicationGain 1)
    (h.duplicationGain (a * (a ^ 2 + b ^ 2)))
    (h.duplicationGain (b * (a ^ 2 + b ^ 2)))
    (h.column (a ^ 2 + b ^ 2)) (h.zeroDetection (a ^ 2 + b ^ 2))
  have htwo := two_mul_ab_eq_one h.commute h.sum hT
  obtain ⟨ha, hb⟩ := half_laws h.commute h.fourthRejoin htwo W k hk h.column h.duplicationGain
  have hinput : a * (b * (2 : S)) = 1 := by
    calc
      a * (b * (2 : S)) = (2 : S) * (a * b) := by noncomm_ring
      _ = 1 := htwo
  have hab := ha (b * (2 : S))
  have hb2 := hb (2 : S)
  rw [hinput, h.unit] at hab
  have hWtwo : W (2 : S) = 4 := by linarith
  have hg := h.duplicationGain 1
  have hfour : k = 4 := by simpa [h.unit, hWtwo] using hg.symm
  exact ⟨hT, htwo, ha, hb, hfour, algebraic_witnesses h.commute hT htwo⟩

/-- A classical real shadow evaluates the destructive context to one half.
This depends only on the supplied homomorphism and its generator values. -/
theorem real_shadow_destructive_value (phi : S →+* ℝ)
    (ha : phi a = 1 / 2) (hb : phi b = 1 / 2) :
    phi (a ^ 2 + b ^ 2) = 1 / 2 := by
  rw [map_add, map_pow, map_pow, ha, hb]
  norm_num

/-- Such an unquotiented carrier cannot carry the full selected readout
contract faithfully. Destructive cancellation comes from the combined
structural and readout assumptions, not from the two grammar equations. -/
theorem no_contract_of_real_shadow (phi : S →+* ℝ)
    (ha : phi a = 1 / 2) (hb : phi b = 1 / 2) :
    ¬ ∃ (W : S → ℝ) (k : ℝ), Contract a b W k := by
  rintro ⟨W, k, h⟩
  have hT := (derive h).destructiveZero
  have hshadow := real_shadow_destructive_value phi ha hb
  rw [hT, map_zero] at hshadow
  norm_num at hshadow

end Algebra

end IDT.DuplicationGainDestructive
