import Proofs.QMClosure.DyadicResponseExtension

namespace IDT.QMClosure.NativeDyadicMixerSelection

noncomputable section

open LocalHistoryReadoutOrderWall DyadicResponseExtension

/-!
# Algebraic selection from a specified native half-mixer

The integer cancellation carrier, C4/Gaussian serial algebra, real-valued
unital multiplicative response with zero vacuum, formal inverse doubling, and
the exact two-output routing below are supplied. Only conservation for native
INTEGER inputs is assumed. No positivity, bilinear readout, topology,
continuity, differentiability, real carrier completion, or fractional-input
conservation is assumed. Positivity is a consequence of selection.

The routing is an explicitly selected algebraic candidate, not discovered or
forced by the primitive base. An independent operational reason for this
routing, physical accessibility, and exhaustive raw-total conservation remain
open operational bridges. This conditional universal algebraic result is not a
derivation of actualization, Hilbert representation, Born physics, or QM.
-/

def p : Residual := (1, 1)
def m : Residual := (1, -1)
def i : Residual := (0, 1)
def ni : Residual := (0, -1)

def numerator₁ (z w : Residual) : Residual := serial p z + serial m w
def numerator₂ (z w : Residual) : Residual := serial m z + serial p w
def output₁ (z w : Residual) : DyadicResponseExtension.Dyadic := fraction (numerator₁ z w) 1
def output₂ (z w : Residual) : DyadicResponseExtension.Dyadic := fraction (numerator₂ z w) 1

def Conserves (W : Response) (hc : doublingValue W ≠ 0) : Prop :=
  ∀ z w : Residual, extension W hc (output₁ z w) +
    extension W hc (output₂ z w) = W.weight z + W.weight w

def NumeratorConserves (W : Response) : Prop :=
  ∀ z w : Residual, W.weight (numerator₁ z w) + W.weight (numerator₂ z w) =
    doublingValue W * (W.weight z + W.weight w)

theorem conservation_iff (W : Response) (hc : doublingValue W ≠ 0) :
    Conserves W hc ↔ NumeratorConserves W := by
  unfold Conserves NumeratorConserves output₁ output₂
  simp only [extension_fraction, pow_one, ← add_div]
  constructor
  · intro h z w
    exact (div_eq_iff hc).mp (h z w) |>.trans (mul_comm _ _)
  · intro h z w
    apply (div_eq_iff hc).mpr
    exact (h z w).trans (mul_comm _ _)

theorem phase_values (W : Response) :
    W.weight (-unit) = 1 ∧ W.weight i ^ 2 = 1 ∧ W.weight ni = W.weight i := by
  have hi : serial i i = -unit := by norm_num [serial, i, unit]
  have hn : serial (-unit) (-unit) = unit := by norm_num [serial, unit]
  have hni : serial (-unit) i = ni := by norm_num [serial, unit, i, ni]
  have ht := W.multiplicative i i
  have hs := W.multiplicative (-unit) (-unit)
  rw [hi] at ht
  rw [hn, W.unital] at hs
  have nonneg : 0 ≤ W.weight (-unit) := by nlinarith [sq_nonneg (W.weight i)]
  have value : W.weight (-unit) = 1 := by nlinarith
  refine ⟨value, ?_, ?_⟩
  · nlinarith
  · rw [← hni, W.multiplicative, value, one_mul]

theorem mixer_phase_and_gain (W : Response) (hc : doublingValue W ≠ 0)
    (hzero : W.weight (0, 0) = 0) (h : NumeratorConserves W) :
    W.weight i = 1 ∧ W.weight ni = 1 ∧ W.weight m = W.weight p ∧
      2 * W.weight p = doublingValue W ∧ W.weight p ≠ 0 := by
  have ph := phase_values W
  have hm : serial ni p = m := by norm_num [serial, ni, p, m]
  have wm : W.weight m = W.weight i * W.weight p := by
    rw [← hm, W.multiplicative, ph.2.2]
  have seed := h unit (0, 0)
  have n₁ : numerator₁ unit (0, 0) = p := by
    norm_num [numerator₁, serial, p, m, unit]
  have n₂ : numerator₂ unit (0, 0) = m := by
    norm_num [numerator₂, serial, p, m, unit]
  rw [n₁, n₂, W.unital, hzero, add_zero, mul_one, wm] at seed
  have ti : W.weight i = 1 := by
    have cases : W.weight i = 1 ∨ W.weight i = -1 := by
      exact sq_eq_one_iff.mp ph.2.1
    rcases cases with yes | no
    · exact yes
    · rw [no] at seed
      have : doublingValue W = 0 := by linarith
      exact (hc this).elim
  rw [ti, one_mul] at seed
  refine ⟨ti, ph.2.2.trans ti, ?_, ?_, ?_⟩
  · simpa [ti] using wm
  · nlinarith [seed]
  · intro hz
    apply hc
    nlinarith [seed]

theorem numerator_factor₁ (z w : Residual) :
    numerator₁ z w = serial p (z - serial i w) := by
  apply Prod.ext <;> dsimp [numerator₁, serial, p, m, i] <;> ring

theorem numerator_factor₂ (z w : Residual) :
    numerator₂ z w = serial m (z + serial i w) := by
  apply Prod.ext <;> dsimp [numerator₂, serial, p, m, i] <;> ring

theorem conservation_parallelogram (W : Response) (hc : doublingValue W ≠ 0)
    (hzero : W.weight (0, 0) = 0) (h : NumeratorConserves W)
    (z v : Residual) :
    W.weight (z + v) + W.weight (z - v) = 2 * (W.weight z + W.weight v) := by
  obtain ⟨hi, hni, hm, hgain, hp⟩ := mixer_phase_and_gain W hc hzero h
  have step := h z (serial ni v)
  have phase : serial i (serial ni v) = v := by
    apply Prod.ext <;> dsimp [serial, i, ni] <;> ring
  rw [numerator_factor₁, numerator_factor₂, phase, W.multiplicative,
    W.multiplicative, W.multiplicative, hni, one_mul, hm, ← hgain] at step
  have eq : W.weight p * (W.weight (z + v) + W.weight (z - v) -
      2 * (W.weight z + W.weight v)) = 0 := by nlinarith [step]
  have := (mul_eq_zero.mp eq).resolve_left hp
  linarith

theorem integer_axis (W : Response) (hc : doublingValue W ≠ 0)
    (hzero : W.weight (0, 0) = 0) (h : NumeratorConserves W) (n : ℤ) :
    W.weight (n, 0) = (n : ℝ) ^ 2 := by
  have recurrence : ∀ k : ℤ, W.weight (k + 1, 0) + W.weight (k - 1, 0) =
      2 * (W.weight (k, 0) + 1) := by
    intro k
    have one : W.weight (1, 0) = 1 := W.unital
    simpa [unit, one] using conservation_parallelogram W hc hzero h (k, 0) unit
  have pair : ∀ k : ℕ, W.weight (k, 0) = (k : ℝ) ^ 2 ∧
      W.weight ((k : ℤ) + 1, 0) = ((k : ℝ) + 1) ^ 2 := by
    intro k
    induction k with
    | zero => simpa [unit] using And.intro hzero W.unital
    | succ k ih =>
      have r := recurrence ((k : ℤ) + 1)
      have cancel : (k : ℤ) + 1 - 1 = (k : ℤ) := by ring
      rw [cancel, ih.1, ih.2] at r
      constructor
      · simpa only [Nat.cast_add, Nat.cast_one] using ih.2
      · push_cast
        nlinarith [r]
  cases n with
  | ofNat k => exact (pair k).1
  | negSucc k =>
      have even : W.weight (-((k : ℤ) + 1), 0) = W.weight ((k : ℤ) + 1, 0) := by
        have prod : serial (-unit) (((k : ℤ) + 1), 0) = (-((k : ℤ) + 1), 0) := by
          apply Prod.ext <;> simp [serial, unit]
        rw [← prod, W.multiplicative, (phase_values W).1, one_mul]
      change W.weight (-((k : ℤ) + 1), 0) = _
      rw [even]
      convert (pair (k + 1)).1 using 1; push_cast; ring

theorem native_selection (W : Response) (hc : doublingValue W ≠ 0)
    (hzero : W.weight (0, 0) = 0) (h : Conserves W hc) (z : Residual) :
    W.weight z = (quadratic z : ℝ) := by
  have hn := (conservation_iff W hc).mp h
  have hi := (mixer_phase_and_gain W hc hzero hn).1
  rcases z with ⟨a, b⟩
  have imag : W.weight (0, b) = (b : ℝ) ^ 2 := by
    have prod : serial i (b, 0) = (0, b) := by simp [serial, i]
    rw [← prod, W.multiplicative, hi, one_mul, integer_axis W hc hzero hn]
  have sum := conservation_parallelogram W hc hzero hn (a, 0) (0, b)
  have sum' : W.weight (a, b) + W.weight (a, -b) =
      2 * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
    simpa [integer_axis W hc hzero hn, imag] using sum
  have prod : serial (a, b) (a, -b) = (a ^ 2 + b ^ 2, 0) := by
    apply Prod.ext <;> dsimp [serial] <;> ring
  have mul := W.multiplicative (a, b) (a, -b)
  rw [prod, integer_axis W hc hzero hn] at mul
  push_cast at mul ⊢
  dsimp [quadratic]
  push_cast
  nlinarith [sq_nonneg (W.weight (a, b) - ((a : ℝ)^2 + (b : ℝ)^2))]

theorem selected_doubling (W : Response) (hc : doublingValue W ≠ 0)
    (hzero : W.weight (0, 0) = 0) (h : Conserves W hc) : doublingValue W = 4 := by
  simpa [doublingValue, double, quadratic] using native_selection W hc hzero h double

theorem selected_extension (W : Response) (hc : doublingValue W ≠ 0)
    (hzero : W.weight (0, 0) = 0) (h : Conserves W hc) (z : Residual) (n : ℕ) :
    extension W hc (fraction z n) = (quadratic z : ℝ) / (4 : ℝ) ^ n := by
  rw [extension_fraction, native_selection W hc hzero h, selected_doubling W hc hzero h]

theorem selected_nonnegative (W : Response) (hc : doublingValue W ≠ 0)
    (hzero : W.weight (0, 0) = 0) (h : Conserves W hc) (z : Residual) :
    0 ≤ W.weight z := by
  rw [native_selection W hc hzero h]
  exact_mod_cast quadratic_nonnegative z

/-- Exact polynomial identity for every pair of native integer inputs. -/
theorem quadratic_numerator_conservation (z w : Residual) :
    quadratic (numerator₁ z w) + quadratic (numerator₂ z w) =
      4 * (quadratic z + quadratic w) := by
  dsimp [quadratic, numerator₁, numerator₂, serial, p, m]
  ring

theorem quadratic_response_conserves (W : Response) (hc : doublingValue W ≠ 0)
    (hq : ∀ z, W.weight z = (quadratic z : ℝ)) : Conserves W hc := by
  apply (conservation_iff W hc).mpr
  intro z w
  have four : doublingValue W = 4 := by
    simpa [doublingValue, double, quadratic] using hq double
  rw [hq, hq, hq, hq, four]
  exact_mod_cast quadratic_numerator_conservation z w

/-- An exact conditional iff over the supplied Response contract. -/
theorem conservation_iff_quadratic (W : Response) (hc : doublingValue W ≠ 0)
    (hzero : W.weight (0, 0) = 0) :
    Conserves W hc ↔ ∀ z, W.weight z = (quadratic z : ℝ) :=
  ⟨fun h z => native_selection W hc hzero h z, quadratic_response_conserves W hc⟩

theorem quadratic_doubling_nonzero : doublingValue (powerResponse 1) ≠ 0 := by
  norm_num [doublingValue, powerResponse, powerReadout, quadratic, double]

/-- Nonvacuity is universal conservation, not a finite numerical gate. -/
theorem quadratic_witness :
    (powerResponse 1).weight (0, 0) = 0 ∧
      Conserves (powerResponse 1) quadratic_doubling_nonzero := by
  constructor
  · norm_num [powerResponse, powerReadout, quadratic]
  · apply quadratic_response_conserves
    intro z
    simp [powerResponse, powerReadout]

def constantResponse : Response where
  weight _ := 1
  unital := rfl
  multiplicative _ _ := by norm_num

theorem constant_doubling_nonzero : doublingValue constantResponse ≠ 0 := by
  norm_num [doublingValue, constantResponse]

/-- Zero vacuum is essential: the nonzero constant response conserves totals. -/
theorem zero_vacuum_is_essential :
    Conserves constantResponse constant_doubling_nonzero ∧
      constantResponse.weight (0, 0) ≠ 0 ∧
      constantResponse.weight (0, 0) ≠ (quadratic (0, 0) : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (conservation_iff constantResponse constant_doubling_nonzero).mpr
    intro z w
    norm_num [constantResponse, doublingValue]
  · norm_num [constantResponse]
  · norm_num [constantResponse, quadratic]

theorem quartic_doubling_nonzero : doublingValue (powerResponse 2) ≠ 0 := by
  norm_num [doublingValue, powerResponse, powerReadout, quadratic, double]

theorem quartic_unit_vacuum_violation :
    extension (powerResponse 2) quartic_doubling_nonzero (output₁ unit (0, 0)) +
      extension (powerResponse 2) quartic_doubling_nonzero (output₂ unit (0, 0)) =
        (1 : ℝ) / 2 ∧
      (powerResponse 2).weight unit + (powerResponse 2).weight (0, 0) = 1 := by
  norm_num [output₁, output₂, extension_fraction, doublingValue,
    numerator₁, numerator₂, p, m, unit, double, serial,
    powerResponse, powerReadout, quadratic]

theorem quartic_fails_conservation : ¬ Conserves (powerResponse 2) quartic_doubling_nonzero := by
  intro h
  have atUnit := h unit (0, 0)
  rw [quartic_unit_vacuum_violation.1, quartic_unit_vacuum_violation.2] at atUnit
  norm_num at atUnit

/-- Two numerator stages swap the inputs and introduce exactly four. -/
theorem numerator_twice₁ (z w : Residual) :
    numerator₁ (numerator₁ z w) (numerator₂ z w) = scale 2 w := by
  apply Prod.ext <;> dsimp [numerator₁, numerator₂, serial, p, m, scale] <;> ring

theorem numerator_twice₂ (z w : Residual) :
    numerator₂ (numerator₁ z w) (numerator₂ z w) = scale 2 z := by
  apply Prod.ext <;> dsimp [numerator₁, numerator₂, serial, p, m, scale] <;> ring

/-- Synchronized two-stage circuit identity; no arbitrary-pair endomap is asserted. -/
theorem synchronized_two_stages (z w : Residual) :
    fraction (numerator₁ (numerator₁ z w) (numerator₂ z w)) 2 = base w ∧
      fraction (numerator₂ (numerator₁ z w) (numerator₂ z w)) 2 = base z := by
  rw [numerator_twice₁, numerator_twice₂]
  constructor <;> apply (fraction_eq_iff _ _ 2 0).mpr <;> rw [scale_zero]

def circuitNumerators : ℕ → Residual → Residual → Residual × Residual
  | 0, z, w => (z, w)
  | n + 1, z, w =>
    let prior := circuitNumerators n z w
    (numerator₁ prior.1 prior.2, numerator₂ prior.1 prior.2)

theorem synchronized_four_stages (z w : Residual) :
    fraction (circuitNumerators 4 z w).1 4 = base z ∧
      fraction (circuitNumerators 4 z w).2 4 = base w := by
  have first : (circuitNumerators 4 z w).1 = scale 4 z := by
    dsimp [circuitNumerators]
    rw [numerator_twice₁, numerator_twice₂]
    apply Prod.ext <;> dsimp [numerator₁, numerator₂, serial, p, m, scale] <;> ring
  have second : (circuitNumerators 4 z w).2 = scale 4 w := by
    dsimp [circuitNumerators]
    rw [numerator_twice₁, numerator_twice₂]
    apply Prod.ext <;> dsimp [numerator₁, numerator₂, serial, p, m, scale] <;> ring
  rw [first, second]
  constructor <;> apply (fraction_eq_iff _ _ 4 0).mpr <;> rw [scale_zero]

inductive ResearchKind where
  | supplied
  | formallyAdjoined
  | derived
  | openOrigin
deriving DecidableEq, Repr

def researchLedger : List (ResearchKind × String) :=
  [(.supplied, "integer cancellation quotient and C4/Gaussian serial algebra"),
   (.supplied, "real-valued unital serial-multiplicative response with zero vacuum"),
   (.formallyAdjoined, "inverse doubling through the cancellation quotient"),
   (.supplied, "explicitly selected routing p=(1,1), m=(1,-1)"),
   (.supplied, "conservation for every native integer input pair"),
   (.derived, "universal native quadratic selection and all fraction response values"),
   (.derived, "positivity without a positivity premise"),
   (.derived, "synchronized two-stage swap and four-stage restoration"),
   (.derived, "quadratic witness; quartic violation; necessity of zero vacuum"),
   (.openOrigin, "deriveIndependentOperationalReasonForThisRouting"),
   (.openOrigin, "derivePhysicalAccessibilityOfEveryNativeIntegerInput"),
   (.openOrigin, "deriveExhaustivePassiveRawTotalConservation"),
   (.openOrigin, "actualization, representation, composites, and physical scale closure")]

end
end IDT.QMClosure.NativeDyadicMixerSelection
