import Proofs.QMClosure.LocalHistoryReadoutOrderWall
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.DenseEmbedding

namespace IDT.QMClosure.DyadicResponseExtension

noncomputable section

open LocalHistoryReadoutOrderWall

/-!
# Conditional dyadic localization of a native serial response

The integer cancellation quotient and Gaussian serial operation are supplied.
This file formally adjoins inverse doubling by an actual quotient, then derives
a uniform half-response gain for every supplied unital multiplicative response
whose value at double is nonzero. Halving is multiplication by this inverse;
it is not asserted to be a serial algebra homomorphism.

No physically admissible preparation/refinement, continuous real completion,
passive mixing, total readout coupling, actualization, composites, or physical
scales are derived. In particular this is no Born or full-QM status upgrade.
-/

def unit : Residual := (1, 0)
def double : Residual := (2, 0)

/-- Native integer scaling, with no real carrier completion. -/
def scale (n : ℕ) (z : Residual) : Residual :=
  ((2 : ℤ) ^ n * z.1, (2 : ℤ) ^ n * z.2)

theorem scale_zero (z : Residual) : scale 0 z = z := by
  simp [scale]

theorem scale_add (n m : ℕ) (z : Residual) :
    scale (n + m) z = scale n (scale m z) := by
  apply Prod.ext <;> simp [scale, pow_add, mul_assoc]

theorem scale_commute (n m : ℕ) (z : Residual) :
    scale n (scale m z) = scale m (scale n z) := by
  rw [← scale_add, ← scale_add, Nat.add_comm]

theorem scale_injective (n : ℕ) : Function.Injective (scale n) := by
  intro z w h
  have hn : (2 : ℤ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  apply Prod.ext
  · exact mul_left_cancel₀ hn (congrArg Prod.fst h)
  · exact mul_left_cancel₀ hn (congrArg Prod.snd h)

theorem scale_serial (n m : ℕ) (z w : Residual) :
    scale (n + m) (serial z w) = serial (scale n z) (scale m w) := by
  apply Prod.ext <;> dsimp [scale, serial] <;> rw [pow_add] <;> ring

structure Presentation where
  numerator : Residual
  denominator : ℕ

/-- `(z,n) ~ (w,m)` means exactly `2^m z = 2^n w`. -/
def Equivalent (p q : Presentation) : Prop :=
  scale q.denominator p.numerator = scale p.denominator q.numerator

theorem equivalent_trans {p q r : Presentation}
    (hpq : Equivalent p q) (hqr : Equivalent q r) : Equivalent p r := by
  apply scale_injective q.denominator
  calc
    scale q.denominator (scale r.denominator p.numerator) =
        scale r.denominator (scale q.denominator p.numerator) := scale_commute _ _ _
    _ = scale r.denominator (scale p.denominator q.numerator) := congrArg _ hpq
    _ = scale p.denominator (scale r.denominator q.numerator) := scale_commute _ _ _
    _ = scale p.denominator (scale q.denominator r.numerator) := congrArg _ hqr
    _ = scale q.denominator (scale p.denominator r.numerator) := scale_commute _ _ _

instance presentationSetoid : Setoid Presentation where
  r := Equivalent
  iseqv := ⟨fun _ => rfl, Eq.symm, equivalent_trans⟩

def Dyadic := Quotient presentationSetoid

def fraction (z : Residual) (n : ℕ) : Dyadic := Quotient.mk _ ⟨z, n⟩
def base (z : Residual) : Dyadic := fraction z 0
def one : Dyadic := base unit
def inverseDouble : Dyadic := fraction unit 1

theorem fraction_eq_iff (z w : Residual) (n m : ℕ) :
    fraction z n = fraction w m ↔ scale m z = scale n w := Quotient.eq

theorem base_injective : Function.Injective base := by
  intro z w h
  have he := (fraction_eq_iff z w 0 0).mp h
  simpa only [scale_zero] using he

def presentationSerial (p q : Presentation) : Presentation :=
  ⟨serial p.numerator q.numerator, p.denominator + q.denominator⟩

theorem presentation_serial_respects {p p' q q' : Presentation}
    (hp : Equivalent p p') (hq : Equivalent q q') :
    Equivalent (presentationSerial p q) (presentationSerial p' q') := by
  dsimp [Equivalent, presentationSerial]
  rw [scale_serial, scale_serial, hp, hq]

def product (x y : Dyadic) : Dyadic :=
  Quotient.liftOn₂ x y (fun p q => Quotient.mk _ (presentationSerial p q))
    (fun _ _ _ _ hp hq => Quotient.sound (presentation_serial_respects hp hq))

theorem product_fraction (z w : Residual) (n m : ℕ) :
    product (fraction z n) (fraction w m) = fraction (serial z w) (n + m) := rfl

theorem serial_unit (z : Residual) : serial z unit = z := by
  apply Prod.ext <;> simp [serial, unit]

theorem unit_serial (z : Residual) : serial unit z = z := by
  apply Prod.ext <;> simp [serial, unit]

theorem serial_assoc (z w v : Residual) :
    serial (serial z w) v = serial z (serial w v) := by
  apply Prod.ext <;> dsimp [serial] <;> ring

theorem serial_comm (z w : Residual) : serial z w = serial w z := by
  apply Prod.ext <;> dsimp [serial] <;> ring

theorem product_assoc (x y z : Dyadic) :
    product (product x y) z = product x (product y z) := by
  induction x using Quotient.inductionOn with | _ p =>
    induction y using Quotient.inductionOn with | _ q =>
      induction z using Quotient.inductionOn with | _ r =>
        change fraction (serial (serial p.numerator q.numerator) r.numerator)
            ((p.denominator + q.denominator) + r.denominator) =
          fraction (serial p.numerator (serial q.numerator r.numerator))
            (p.denominator + (q.denominator + r.denominator))
        rw [serial_assoc, Nat.add_assoc]

theorem product_comm (x y : Dyadic) : product x y = product y x := by
  induction x using Quotient.inductionOn with | _ p =>
    induction y using Quotient.inductionOn with | _ q =>
      change fraction (serial p.numerator q.numerator) (p.denominator + q.denominator) =
        fraction (serial q.numerator p.numerator) (q.denominator + p.denominator)
      rw [serial_comm, Nat.add_comm]

theorem product_one (x : Dyadic) : product x one = x := by
  induction x using Quotient.inductionOn with | _ p =>
    change fraction (serial p.numerator unit) (p.denominator + 0) =
      fraction p.numerator p.denominator
    rw [serial_unit, Nat.add_zero]

theorem inverse_double : product (base double) inverseDouble = one := by
  apply Quotient.sound
  change scale 0 (serial double unit) = scale (0 + 1) unit
  norm_num [scale, serial, unit, double]

def half (x : Dyadic) : Dyadic := product x inverseDouble

theorem half_fraction (z : Residual) (n : ℕ) :
    half (fraction z n) = fraction z (n + 1) := by
  change fraction (serial z unit) (n + 1) = _
  rw [serial_unit]

theorem half_not_unital : half one ≠ one := by
  rw [one, base, half_fraction]
  intro h
  have he := (fraction_eq_iff unit unit 1 0).mp h
  norm_num [scale, unit] at he

/-- Only these response laws are supplied; no exponent is selected. -/
structure Response where
  weight : Residual → ℝ
  unital : weight unit = 1
  multiplicative : ∀ z w, weight (serial z w) = weight z * weight w

def doublingValue (W : Response) : ℝ := W.weight double
def gain (W : Response) : ℝ := (doublingValue W)⁻¹

theorem scale_succ (n : ℕ) (z : Residual) :
    scale (n + 1) z = serial double (scale n z) := by
  apply Prod.ext <;> dsimp [scale, serial, double] <;> rw [pow_succ] <;> ring

theorem response_scale (W : Response) (n : ℕ) (z : Residual) :
    W.weight (scale n z) = doublingValue W ^ n * W.weight z := by
  induction n with
  | zero => simp [scale_zero]
  | succ n ih =>
    rw [scale_succ, W.multiplicative, ih]
    dsimp [doublingValue]
    rw [pow_succ]
    ring

def presentationWeight (W : Response) (p : Presentation) : ℝ :=
  W.weight p.numerator / doublingValue W ^ p.denominator

theorem presentation_weight_respects (W : Response) (hc : doublingValue W ≠ 0)
    {p q : Presentation} (h : Equivalent p q) :
    presentationWeight W p = presentationWeight W q := by
  have hw := congrArg W.weight h
  rw [response_scale, response_scale] at hw
  dsimp [presentationWeight]
  apply (div_eq_div_iff (pow_ne_zero _ hc) (pow_ne_zero _ hc)).2
  simpa only [mul_comm] using hw

/-- The response descends by a proved invariance result, not by assumption. -/
def extension (W : Response) (hc : doublingValue W ≠ 0) : Dyadic → ℝ :=
  Quotient.lift (presentationWeight W) (fun _ _ h => presentation_weight_respects W hc h)

theorem extension_fraction (W : Response) (hc : doublingValue W ≠ 0)
    (z : Residual) (n : ℕ) :
    extension W hc (fraction z n) = W.weight z / doublingValue W ^ n := rfl

theorem extension_base (W : Response) (hc : doublingValue W ≠ 0) (z : Residual) :
    extension W hc (base z) = W.weight z := by simp [base, extension_fraction]

theorem extension_unital (W : Response) (hc : doublingValue W ≠ 0) :
    extension W hc one = 1 := by rw [one, extension_base, W.unital]

theorem extension_multiplicative (W : Response) (hc : doublingValue W ≠ 0)
    (x y : Dyadic) :
    extension W hc (product x y) = extension W hc x * extension W hc y := by
  induction x using Quotient.inductionOn with | _ p =>
    induction y using Quotient.inductionOn with | _ q =>
      change W.weight (serial p.numerator q.numerator) /
          doublingValue W ^ (p.denominator + q.denominator) =
        (W.weight p.numerator / doublingValue W ^ p.denominator) *
          (W.weight q.numerator / doublingValue W ^ q.denominator)
      rw [W.multiplicative, pow_add, mul_div_mul_comm]

theorem extension_inverse_double (W : Response) (hc : doublingValue W ≠ 0) :
    extension W hc inverseDouble = gain W := by
  simp [inverseDouble, extension_fraction, W.unital, gain]

theorem extension_half (W : Response) (hc : doublingValue W ≠ 0) (x : Dyadic) :
    extension W hc (half x) = gain W * extension W hc x := by
  rw [half, extension_multiplicative, extension_inverse_double, mul_comm]

theorem cancel_denominator (z : Residual) (n : ℕ) :
    product (base (scale n unit)) (fraction z n) = base z := by
  apply Quotient.sound
  change scale 0 (serial (scale n unit) z) = scale (0 + n) z
  rw [scale_zero, Nat.zero_add]
  apply Prod.ext <;> simp [serial, scale, unit]

/-- Every multiplicative extension has the quotient formula, hence is unique. -/
theorem extension_unique (W : Response) (hc : doublingValue W ≠ 0)
    (F : Dyadic → ℝ)
    (hmul : ∀ x y, F (product x y) = F x * F y)
    (hbase : ∀ z, F (base z) = W.weight z) : F = extension W hc := by
  funext x
  induction x using Quotient.inductionOn with | _ p =>
    have h := congrArg F (cancel_denominator p.numerator p.denominator)
    rw [hmul, hbase, hbase, response_scale, W.unital, mul_one] at h
    change F (fraction p.numerator p.denominator) =
      W.weight p.numerator / doublingValue W ^ p.denominator
    apply (eq_div_iff (pow_ne_zero _ hc)).2
    simpa only [mul_comm] using h

/-- Inverse doubling makes nonzero response at double necessary. -/
theorem nonzero_necessary (W : Response) (F : Dyadic → ℝ)
    (hmul : ∀ x y, F (product x y) = F x * F y)
    (hbase : ∀ z, F (base z) = W.weight z) : doublingValue W ≠ 0 := by
  have h := congrArg F inverse_double
  rw [hmul, hbase, one, hbase, W.unital] at h
  intro hc
  change W.weight double = 0 at hc
  rw [hc, zero_mul] at h
  exact zero_ne_one h

theorem unique_unital_multiplicative_extension (W : Response)
    (hc : doublingValue W ≠ 0) :
    ∃! F : Dyadic → ℝ, F one = 1 ∧
      (∀ x y, F (product x y) = F x * F y) ∧
      (∀ z, F (base z) = W.weight z) := by
  refine ⟨extension W hc,
    ⟨extension_unital W hc, extension_multiplicative W hc, extension_base W hc⟩, ?_⟩
  intro F hF
  exact extension_unique W hc F hF.2.1 hF.2.2

theorem positive_doubling_value (W : Response) (hc : doublingValue W ≠ 0)
    (hnonneg : ∀ z, 0 ≤ W.weight z) : 0 < doublingValue W :=
  lt_of_le_of_ne (hnonneg double) (Ne.symm hc)

theorem positive_gain (W : Response) (hc : doublingValue W ≠ 0)
    (hnonneg : ∀ z, 0 ≤ W.weight z) : 0 < gain W :=
  inv_pos.mpr (positive_doubling_value W hc hnonneg)

/-- Conditional propagation only: existence of this completion is not proved.
Density and compatibility suffice; injectivity of the supplied map is not needed
for this implication. -/
theorem compatible_dense_completion_half_scaling
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (W : Response) (hc : doublingValue W ≠ 0)
    (embed : Dyadic → V) (dense : DenseRange embed)
    (intertwines : ∀ d, embed (half d) = (1 / 2 : ℝ) • embed d)
    (F : V → ℝ) (continuousF : Continuous F)
    (compatible : ∀ d, F (embed d) = extension W hc d) (v : V) :
    F ((1 / 2 : ℝ) • v) = gain W * F v := by
  have equalFunctions : (fun x => F ((1 / 2 : ℝ) • x)) =
      (fun x => gain W * F x) := by
    apply dense.equalizer (continuousF.comp (continuous_const.smul continuous_id))
      (continuous_const.mul continuousF)
    funext d
    change F ((1 / 2 : ℝ) • embed d) = gain W * F (embed d)
    rw [← intertwines, compatible, extension_half, compatible]
  exact congrFun equalFunctions v

/-- Native Q^k responses remain available after localization. -/
def powerResponse (k : ℕ) : Response where
  weight z := (powerReadout k z : ℝ)
  unital := by simp [unit, powerReadout, quadratic]
  multiplicative z w := by exact_mod_cast power_readout_serial k z w

theorem quadratic_gain : gain (powerResponse 1) = 1 / 4 := by
  norm_num [gain, doublingValue, powerResponse, double, powerReadout, quadratic]

theorem quartic_gain : gain (powerResponse 2) = 1 / 16 := by
  norm_num [gain, doublingValue, powerResponse, double, powerReadout, quadratic]

theorem localization_does_not_select_exponent :
    gain (powerResponse 1) ≠ gain (powerResponse 2) := by
  rw [quadratic_gain, quartic_gain]
  norm_num

theorem quadratic_eq_zero_iff (z : Residual) : quadratic z = 0 ↔ z = (0, 0) := by
  constructor
  · intro h
    have h1 : z.1 ^ 2 = 0 := by
      dsimp [quadratic] at h
      nlinarith [sq_nonneg z.1, sq_nonneg z.2]
    have h2 : z.2 ^ 2 = 0 := by
      dsimp [quadratic] at h
      nlinarith [sq_nonneg z.1, sq_nonneg z.2]
    exact Prod.ext (sq_eq_zero_iff.mp h1) (sq_eq_zero_iff.mp h2)
  · rintro rfl
    norm_num [quadratic]

theorem serial_eq_zero_iff (z w : Residual) :
    serial z w = (0, 0) ↔ z = (0, 0) ∨ w = (0, 0) := by
  constructor
  · intro h
    have hn : quadratic z * quadratic w = 0 := by
      rw [← quadratic_serial, h]
      norm_num [quadratic]
    exact (mul_eq_zero.mp hn).imp (quadratic_eq_zero_iff z).mp (quadratic_eq_zero_iff w).mp
  · rintro (rfl | rfl) <;> simp [serial]

/-- Faithful zero detection need not provide strict attenuation. -/
def indicatorResponse : Response where
  weight z := if z = (0, 0) then 0 else 1
  unital := by norm_num [unit]
  multiplicative z w := by
    by_cases hz : z = (0, 0) <;> by_cases hw : w = (0, 0) <;>
      simp [serial_eq_zero_iff, hz, hw]

theorem indicator_nonnegative (z : Residual) : 0 ≤ indicatorResponse.weight z := by
  dsimp [indicatorResponse]
  split_ifs <;> norm_num

theorem indicator_faithful (z : Residual) :
    indicatorResponse.weight z = 0 ↔ z = (0, 0) := by
  simp [indicatorResponse]

theorem indicator_gain : gain indicatorResponse = 1 := by
  norm_num [gain, doublingValue, indicatorResponse, double]

inductive ResearchKind where
  | supplied
  | formallyAdjoined
  | derived
  | openOrigin
deriving DecidableEq, Repr

def researchLedger : List (ResearchKind × String) :=
  [ (.supplied, "Native integer cancellation quotient, Gaussian serial multiplication, and unital multiplicative response."),
    (.formallyAdjoined, "Inverse doubling by the proved presentation quotient; no physical preparation is supplied."),
    (.derived, "Unique extension and state-independent half gain W(double)^(-1), with positive gain for nonnegative W."),
    (.derived, "Q and Q squared have distinct gains; localization does not select the response exponent."),
    (.derived, "The faithful nonzero-indicator response has gain one, so strict attenuation is not implied."),
    (.derived, "Half-scaling propagates to any supplied compatible dense continuous real completion; no such completion is constructed."),
    (.openOrigin, "Physically admissible preparation/refinement and existence of a compatible continuous real completion."),
    (.openOrigin, "Passive mixing and total readout coupling; actualization, composites, and physical scales remain separate burdens.") ]

end

end IDT.QMClosure.DyadicResponseExtension
