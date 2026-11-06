import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace IDT.QMClosure.LocalHistoryReadoutOrderWall

/-!
# Supplied local history rules do not select detector response order

The residual carrier, token translations, merge, Gaussian serial product, and
terminal readouts in this file are supplied mathematical constructions. They
are not derived physical detectors or new IDT primitives. Exact cancellation,
commuting reversible updates, C4 covariance, nonnegative response, unit
calibration, and serial weight multiplicativity allow both Q and Q squared.

The scalar register construction has linear updates and a linear output, but
unbounded integer register values. It is not finite-state memory. Its scalar
scope is separate from the full C4 residual construction above it.

These algebraic walls do not derive Born probabilities, actualization,
physical attenuation, quantum mechanics, or gravity.
-/

abbrev Residual := ℤ × ℤ

def merge (x y : Residual) : Residual := (x.1 + y.1, x.2 + y.2)

def update (token state : Residual) : Residual := merge token state

def inverseToken (token : Residual) : Residual := (-token.1, -token.2)

def localTokens : List Residual := [(1, 0), (-1, 0), (0, 1), (0, -1)]

def rotate (z : Residual) : Residual := (-z.2, z.1)

def serial (x y : Residual) : Residual :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

def quadratic (z : Residual) : ℤ := z.1 ^ 2 + z.2 ^ 2

def powerReadout (k : ℕ) (z : Residual) : ℤ := quadratic z ^ k

theorem update_inverse (token state : Residual) :
    update (inverseToken token) (update token state) = state := by
  apply Prod.ext <;> dsimp [update, merge, inverseToken] <;> ring

theorem update_inverse_other_order (token state : Residual) :
    update token (update (inverseToken token) state) = state := by
  apply Prod.ext <;> dsimp [update, merge, inverseToken] <;> ring

theorem updates_commute (t u state : Residual) :
    update t (update u state) = update u (update t state) := by
  apply Prod.ext <;> dsimp [update, merge] <;> ring

theorem rotation_covariant_update (token state : Residual) :
    rotate (update token state) = update (rotate token) (rotate state) := by
  exact Prod.ext (by dsimp [rotate, update, merge]; ring) rfl

theorem rotation_has_order_four (state : Residual) :
    rotate (rotate (rotate (rotate state))) = state := by
  apply Prod.ext <;> simp [rotate]

theorem quadratic_nonnegative (z : Residual) : 0 ≤ quadratic z := by
  dsimp [quadratic]
  positivity

theorem quadratic_rotation (z : Residual) : quadratic (rotate z) = quadratic z := by
  dsimp [quadratic, rotate]
  ring

theorem quadratic_serial (x y : Residual) :
    quadratic (serial x y) = quadratic x * quadratic y := by
  dsimp [quadratic, serial]
  ring

theorem power_readout_nonnegative (k : ℕ) (z : Residual) :
    0 ≤ powerReadout k z := by
  exact pow_nonneg (quadratic_nonnegative z) k

theorem power_readout_rotation (k : ℕ) (z : Residual) :
    powerReadout k (rotate z) = powerReadout k z := by
  simp only [powerReadout, quadratic_rotation]

theorem power_readout_serial (k : ℕ) (x y : Residual) :
    powerReadout k (serial x y) = powerReadout k x * powerReadout k y := by
  simp only [powerReadout, quadratic_serial, mul_pow]

/-- A narrow supplied response contract; it does not include an I3 law. -/
structure SuppliedReadoutLaws (weight : Residual → ℤ) : Prop where
  nonnegative : ∀ z, 0 ≤ weight z
  emptyZero : weight (0, 0) = 0
  unitCalibration : weight (1, 0) = 1
  rotationInvariant : ∀ z, weight (rotate z) = weight z
  serialMultiplicative : ∀ x y, weight (serial x y) = weight x * weight y

theorem positive_power_satisfies_supplied_laws (k : ℕ) (positiveOrder : 0 < k) :
    SuppliedReadoutLaws (powerReadout k) where
  nonnegative := power_readout_nonnegative k
  emptyZero := by simp [powerReadout, quadratic, Nat.ne_of_gt positiveOrder]
  unitCalibration := by simp [powerReadout, quadratic]
  rotationInvariant := power_readout_rotation k
  serialMultiplicative := power_readout_serial k

def equalUnitI3 (weight : Residual → ℤ) : ℤ :=
  weight (3, 0) - 3 * weight (2, 0) + 3 * weight (1, 0) - weight (0, 0)

theorem quadratic_equal_unit_i3 : equalUnitI3 (powerReadout 1) = 0 := by
  norm_num [equalUnitI3, powerReadout, quadratic]

theorem quartic_equal_unit_i3 : equalUnitI3 (powerReadout 2) = 36 := by
  norm_num [equalUnitI3, powerReadout, quadratic]

theorem sextic_equal_unit_i3 : equalUnitI3 (powerReadout 3) = 540 := by
  norm_num [equalUnitI3, powerReadout, quadratic]

theorem octic_equal_unit_i3 : equalUnitI3 (powerReadout 4) = 5796 := by
  norm_num [equalUnitI3, powerReadout, quadratic]

theorem quartic_differs_from_quadratic : powerReadout 2 ≠ powerReadout 1 := by
  intro equalFunctions
  have atTwo := congrFun equalFunctions (2, 0)
  norm_num [powerReadout, quadratic] at atTwo

/-- Existence of a second response, not a claim about physical detectors. -/
theorem supplied_laws_do_not_select_quadratic :
    ∃ weight : Residual → ℤ, SuppliedReadoutLaws weight ∧
      weight ≠ powerReadout 1 ∧ equalUnitI3 weight ≠ 0 := by
  refine ⟨powerReadout 2, positive_power_satisfies_supplied_laws 2 (by decide),
    quartic_differs_from_quadratic, ?_⟩
  rw [quartic_equal_unit_i3]
  norm_num

/-! ## A scalar quartic output with linear register updates

The five coordinates store (1,n,n squared,n cubed,n to the fourth). Every
translation is linear on the entire register space, including its constant
coordinate; the quartic terminal response is a linear coordinate projection.
This separately scoped example does not itself construct a full C4 register.
-/

@[ext] structure ScalarRegister where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
  c4 : ℤ
deriving DecidableEq, Repr

def encode (n : ℤ) : ScalarRegister := ⟨1, n, n ^ 2, n ^ 3, n ^ 4⟩

def registerAdd (x y : ScalarRegister) : ScalarRegister :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3, x.c4 + y.c4⟩

def registerScale (a : ℤ) (x : ScalarRegister) : ScalarRegister :=
  ⟨a * x.c0, a * x.c1, a * x.c2, a * x.c3, a * x.c4⟩

def registerTranslate (h : ℤ) (x : ScalarRegister) : ScalarRegister :=
  ⟨x.c0,
   x.c1 + h * x.c0,
   x.c2 + 2 * h * x.c1 + h ^ 2 * x.c0,
   x.c3 + 3 * h * x.c2 + 3 * h ^ 2 * x.c1 + h ^ 3 * x.c0,
   x.c4 + 4 * h * x.c3 + 6 * h ^ 2 * x.c2 + 4 * h ^ 3 * x.c1 + h ^ 4 * x.c0⟩

def registerOutput (x : ScalarRegister) : ℤ := x.c4

theorem register_translation_additive (h : ℤ) (x y : ScalarRegister) :
    registerTranslate h (registerAdd x y) =
      registerAdd (registerTranslate h x) (registerTranslate h y) := by
  ext <;> dsimp [registerTranslate, registerAdd] <;> ring

theorem register_translation_homogeneous (h a : ℤ) (x : ScalarRegister) :
    registerTranslate h (registerScale a x) = registerScale a (registerTranslate h x) := by
  ext <;> dsimp [registerTranslate, registerScale] <;> ring

theorem register_translation_preserves_encoding (h n : ℤ) :
    registerTranslate h (encode n) = encode (n + h) := by
  ext <;> dsimp [registerTranslate, encode] <;> ring

theorem register_translation_composes (h j : ℤ) (x : ScalarRegister) :
    registerTranslate h (registerTranslate j x) = registerTranslate (h + j) x := by
  ext <;> dsimp [registerTranslate] <;> ring

theorem register_translation_zero (x : ScalarRegister) : registerTranslate 0 x = x := by
  ext <;> dsimp [registerTranslate] <;> ring

theorem register_translation_inverse (h : ℤ) (x : ScalarRegister) :
    registerTranslate (-h) (registerTranslate h x) = x := by
  rw [register_translation_composes]
  simpa using register_translation_zero x

theorem register_translations_commute (h j : ℤ) (x : ScalarRegister) :
    registerTranslate h (registerTranslate j x) = registerTranslate j (registerTranslate h x) := by
  rw [register_translation_composes, register_translation_composes, add_comm h j]

theorem register_output_additive (x y : ScalarRegister) :
    registerOutput (registerAdd x y) = registerOutput x + registerOutput y := by
  rfl

theorem register_output_homogeneous (a : ℤ) (x : ScalarRegister) :
    registerOutput (registerScale a x) = a * registerOutput x := by
  rfl

theorem register_output_is_quartic (n : ℤ) : registerOutput (encode n) = n ^ 4 := by
  rfl

theorem register_output_agrees_with_scalar_quartic (n : ℤ) :
    registerOutput (encode n) = powerReadout 2 (n, 0) := by
  dsimp [registerOutput, encode, powerReadout, quadratic]
  ring

/-! ## Literal monotone cumulative records cannot be erased by cancellation

This applies only if a token and its inverse are actual sequential steps and
the cumulative recorded score never decreases under either step. It allows
deferred terminal readout and latent memory, and makes no detector-realism
claim about other meanings of history insertion.
-/

theorem monotone_cumulative_record_cannot_increase_under_cancellation
    {State : Type*} (score : State → ℕ) (forward undo : State → State)
    (cancels : ∀ state, undo (forward state) = state)
    (forwardMonotone : ∀ state, score state ≤ score (forward state))
    (undoMonotone : ∀ state, score state ≤ score (undo state))
    (state : State) : score (forward state) = score state := by
  apply Nat.le_antisymm
  · simpa only [cancels state] using undoMonotone (forward state)
  · exact forwardMonotone state

/-! ## One optional weak-response route: data-only direction ledger

The Hessian hypothesis below is supplied only for this optional route.
`Proofs/QMClosure/InfinitesimalPairReadoutSelection.lean` instead derives
quadraticity conditionally from universal linear exchange and raw-response
conservation, without a Hessian assumption. Neither route derives the physical
origin of its bridges; this ledger adds no axioms or physics proofs.
-/

inductive WeakResponseResearchKind where
  | conditionalHypothesis
  | openOrigin
deriving DecidableEq, Repr

structure WeakResponseResearchItem where
  id : String
  kind : WeakResponseResearchKind
  obligation : String
deriving Repr

def weakResponseResearchLedger : List WeakResponseResearchItem :=
  [ ⟨"smooth_extension", .conditionalHypothesis,
      "A sufficiently smooth real response extension near the dark residual is proposed, not derived from the integer register model."⟩,
    ⟨"nonzero_dark_hessian", .conditionalHypothesis,
      "A nonzero positive quadratic response at the dark residual is a proposed detector hypothesis; quartic register readout does not supply it."⟩,
    ⟨"response_symmetry", .conditionalHypothesis,
      "Symmetry of the physical response and its accessible transformations must be justified; the present algebra proves only supplied C4 covariance."⟩,
    ⟨"attenuation_origin", .openOrigin,
      "Derive physically accessible attenuation and the meaning of weak-response scaling without assuming amplitude or probability scaling."⟩,
    ⟨"detector_origin", .openOrigin,
      "Derive the detector response and readout normalization rather than select a polynomial terminal function by hand."⟩ ]

end IDT.QMClosure.LocalHistoryReadoutOrderWall
