import Mathlib

namespace IDT.QMClosure.NativeAttenuationBoundary

/-!
# Integer attenuation obstruction and an explicit rational extension

These are algebraic residual models. The rational model supplies exact halving;
it does not derive a minimal completion or an operationally available refinement.
Both response weights obey multiplicative serial laws and have uniform halving
factors, whose values differ. Their normalized ratios also differ. No physical
response rule is selected.
-/

namespace IntegerResidual

abbrev Residual := ℤ × ℤ

def unit : Residual := (1, 0)
def phase (v : Residual) : Residual := (-v.2, v.1)
def product (u v : Residual) : Residual :=
  (u.1 * v.1 - u.2 * v.2, u.1 * v.2 + u.2 * v.1)
def norm (v : Residual) : ℤ := v.1 ^ 2 + v.2 ^ 2

theorem norm_nonnegative (v : Residual) : 0 ≤ norm v :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem norm_zero_iff (v : Residual) : norm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have ha : v.1 = 0 := by
      dsimp [norm] at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2]
    have hb : v.2 = 0 := by
      dsimp [norm] at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2]
    exact Prod.ext ha hb
  · rintro rfl
    norm_num [norm]

theorem integer_gap {v : Residual} (h : v ≠ 0) : 1 ≤ norm v := by
  have hn := norm_nonnegative v
  have hz : norm v ≠ 0 := fun hz => h ((norm_zero_iff v).mp hz)
  omega

theorem product_norm (u v : Residual) :
    norm (product u v) = norm u * norm v := by
  dsimp [norm, product]
  ring

theorem coordinate_decomposition (v : Residual) :
    v = v.1 • unit + v.2 • phase unit := by
  ext <;> simp [unit, phase]

/-- Classification of all additive maps commuting with the displayed quarter turn. -/
theorem phase_covariant_classification (f : Residual →+ Residual)
    (hphase : ∀ v, f (phase v) = phase (f v)) (v : Residual) :
    f v = product (f unit) v := by
  calc
    f v = v.1 • f unit + v.2 • phase (f unit) := by
      conv_lhs => rw [coordinate_decomposition v]
      rw [map_add, map_zsmul, map_zsmul, hphase]
    _ = product (f unit) v := by
      ext <;> simp [product, phase, zsmul_eq_mul] <;> ring

theorem nonzero_map_unit (f : Residual →+ Residual)
    (hphase : ∀ v, f (phase v) = phase (f v)) (hf : f ≠ 0) :
    f unit ≠ 0 := by
  intro hz
  apply hf
  apply AddMonoidHom.ext
  intro v
  rw [phase_covariant_classification f hphase, hz]
  simp [product]

theorem phase_covariant_norm_nondecreasing (f : Residual →+ Residual)
    (hphase : ∀ v, f (phase v) = phase (f v)) (hf : f ≠ 0)
    (v : Residual) : norm v ≤ norm (f v) := by
  rw [phase_covariant_classification f hphase, product_norm]
  have hgap := integer_gap (nonzero_map_unit f hphase hf)
  have hn := norm_nonnegative v
  nlinarith

theorem no_nonzero_uniform_strict_contraction :
    ¬ ∃ f : Residual →+ Residual,
      (∀ v, f (phase v) = phase (f v)) ∧ f ≠ 0 ∧
      (∀ v, v ≠ 0 → norm (f v) < norm v) := by
  rintro ⟨f, hphase, hf, hstrict⟩
  have hn := phase_covariant_norm_nondecreasing f hphase hf unit
  have hs := hstrict unit (by simp [unit])
  omega

end IntegerResidual

namespace RationalResidual

abbrev Residual := ℚ × ℚ

def unit : Residual := (1, 0)
def doubleUnit : Residual := (2, 0)
def phase (v : Residual) : Residual := (-v.2, v.1)
def product (u v : Residual) : Residual :=
  (u.1 * v.1 - u.2 * v.2, u.1 * v.2 + u.2 * v.1)
def half (v : Residual) : Residual := (v.1 / 2, v.2 / 2)
def norm (v : Residual) : ℚ := v.1 ^ 2 + v.2 ^ 2
def fourthWeight (v : Residual) : ℚ := norm v ^ 2
def ratio (weight : Residual → ℚ) (u v : Residual) : ℚ :=
  weight u / (weight u + weight v)

theorem half_add_half (v : Residual) : half v + half v = v := by
  ext <;> dsimp [half] <;> ring

theorem half_add (u v : Residual) : half (u + v) = half u + half v := by
  ext <;> dsimp [half] <;> ring

theorem half_phase (v : Residual) : half (phase v) = phase (half v) := by
  ext <;> simp [half, phase, neg_div]

theorem half_injective : Function.Injective half := by
  intro u v h
  have hsum := congrArg (fun z : Residual => z + z) h
  simpa only [half_add_half] using hsum

theorem half_zero_iff (v : Residual) : half v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply half_injective
    simpa [half] using h
  · rintro rfl
    simp [half]

theorem half_preserves_cancellation (u v : Residual) :
    half u + half v = 0 ↔ u + v = 0 := by
  rw [← half_add, half_zero_iff]

theorem norm_nonnegative (v : Residual) : 0 ≤ norm v :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem product_norm (u v : Residual) :
    norm (product u v) = norm u * norm v := by
  dsimp [norm, product]
  ring

theorem product_fourth_weight (u v : Residual) :
    fourthWeight (product u v) = fourthWeight u * fourthWeight v := by
  simp only [fourthWeight, product_norm]
  ring

theorem half_norm (v : Residual) : norm (half v) = norm v / 4 := by
  dsimp [norm, half]
  ring

theorem half_strict_norm_contraction {v : Residual} (hv : v ≠ 0) :
    norm (half v) < norm v := by
  have hn := norm_nonnegative v
  have hz : norm v ≠ 0 := by
    intro hz
    apply hv
    have ha : v.1 = 0 := by
      dsimp [norm] at hz
      nlinarith [sq_nonneg v.1, sq_nonneg v.2]
    have hb : v.2 = 0 := by
      dsimp [norm] at hz
      nlinarith [sq_nonneg v.1, sq_nonneg v.2]
    exact Prod.ext ha hb
  rw [half_norm]
  have hp : 0 < norm v := lt_of_le_of_ne hn (Ne.symm hz)
  linarith

theorem half_fourth_weight (v : Residual) :
    fourthWeight (half v) = fourthWeight v / 16 := by
  dsimp [fourthWeight]
  rw [half_norm]
  ring

theorem common_half_norm_ratio (u v : Residual)
    (htotal : norm u + norm v ≠ 0) :
    ratio norm (half u) (half v) = ratio norm u v := by
  dsimp [ratio]
  rw [half_norm, half_norm]
  field_simp [htotal]

theorem common_half_fourth_ratio (u v : Residual)
    (htotal : fourthWeight u + fourthWeight v ≠ 0) :
    ratio fourthWeight (half u) (half v) = ratio fourthWeight u v := by
  dsimp [ratio]
  rw [half_fourth_weight, half_fourth_weight]
  field_simp [htotal]

theorem ratios_disagree :
    ratio norm unit doubleUnit = 1 / 5 ∧
    ratio fourthWeight unit doubleUnit = 1 / 17 ∧
    ratio norm unit doubleUnit ≠ ratio fourthWeight unit doubleUnit := by
  norm_num [ratio, norm, fourthWeight, unit, doubleUnit]

/-- Coherent recombination differs from adding distinguishable-channel weights. -/
theorem distinguishable_halves_unit :
    norm (half unit) + norm (half unit) = 1 / 2 ∧
    fourthWeight (half unit) + fourthWeight (half unit) = 1 / 8 ∧
    norm (half unit) + norm (half unit) ≠ norm unit ∧
    fourthWeight (half unit) + fourthWeight (half unit) ≠ fourthWeight unit := by
  norm_num [half, norm, fourthWeight, unit]

/-- Halving is a scalar action, not a homomorphism of serial products. -/
theorem half_not_serial_homomorphism :
    half (product unit unit) ≠ product (half unit) (half unit) := by
  norm_num [half, product, unit, Prod.mk.injEq]

end RationalResidual

namespace ScalarTwoPort

def shear (v : ℚ × ℚ) : ℚ × ℚ := (v.1 + v.2, v.2)
def unshear (v : ℚ × ℚ) : ℚ × ℚ := (v.1 - v.2, v.2)

theorem unshear_shear (v : ℚ × ℚ) : unshear (shear v) = v := by
  ext <;> simp [shear, unshear]

theorem shear_unshear (v : ℚ × ℚ) : shear (unshear v) = v := by
  ext <;> simp [shear, unshear]

/--
This reversible algebraic circuit has no constant total-response gain for any
normalized response. Thus algebraic reversibility alone does not identify every
circuit with a uniform-gain closed physical symmetry. This is not a law imposed
on arbitrary admissible maps.
-/
theorem no_uniform_gain (g : ℚ → ℚ) (hzero : g 0 = 0) (hone : g 1 = 1) :
    ¬ ∃ c : ℚ, ∀ x y : ℚ,
      g (x + y) + g y = c * (g x + g y) := by
  rintro ⟨c, hgain⟩
  have hunit := hgain 1 0
  have hsplit := hgain 0 1
  norm_num [hzero, hone] at hunit hsplit
  linarith

/-- Algebraic mixer syntax does not establish physical accessibility. -/
def mixer (v : ℚ × ℚ) : ℚ × ℚ :=
  ((v.1 + v.2) / 2, (v.1 - v.2) / 2)

def unmix (v : ℚ × ℚ) : ℚ × ℚ := (v.1 + v.2, v.1 - v.2)

theorem unmix_mixer (v : ℚ × ℚ) : unmix (mixer v) = v := by
  ext <;> dsimp [mixer, unmix] <;> ring

theorem mixer_unmix (v : ℚ × ℚ) : mixer (unmix v) = v := by
  ext <;> dsimp [mixer, unmix] <;> ring

def squareResponse (t : ℚ) : ℚ := t ^ 2
def fourthResponse (t : ℚ) : ℚ := t ^ 4

def total (g : ℚ → ℚ) (v : ℚ × ℚ) : ℚ := g v.1 + g v.2

theorem mixer_square_total (v : ℚ × ℚ) :
    total squareResponse (mixer v) = total squareResponse v / 2 := by
  dsimp [total, squareResponse, mixer]
  ring

theorem mixer_fourth_gain_ratios :
    total fourthResponse (mixer (1, 0)) / total fourthResponse (1, 0) = 1 / 8 ∧
    total fourthResponse (mixer (1, 1)) / total fourthResponse (1, 1) = 1 / 2 := by
  norm_num [total, fourthResponse, mixer]

/-- The two exact inputs already exclude any constant fourth-response gain. -/
theorem mixer_no_uniform_fourth_gain :
    ¬ ∃ c : ℚ, ∀ v : ℚ × ℚ,
      total fourthResponse (mixer v) = c * total fourthResponse v := by
  rintro ⟨c, hgain⟩
  have hfirst := hgain (1, 0)
  have hsecond := hgain (1, 1)
  norm_num [total, fourthResponse, mixer] at hfirst hsecond
  linarith

end ScalarTwoPort

/-- Data-only obligations: none is discharged by the rational example above. -/
inductive OpenObligation where
  | deriveEqualRefinementFromBase
  | authorizeChildSelectionOperationally
  | deriveTopologyAndConvergence
  | deriveDarkPointSensitivity
  | deriveRecords
  | deriveComposites
  | deriveActualization
  | deriveClosedMixerAndEnvironmentAccounting
  | deriveInputIndependentGainWithoutSelectingReadout
  | testEntangledContextOperationsBeyondProductPreparations
  deriving DecidableEq, Repr

def openObligations : List OpenObligation :=
  [.deriveEqualRefinementFromBase, .authorizeChildSelectionOperationally,
   .deriveTopologyAndConvergence, .deriveDarkPointSensitivity,
   .deriveRecords, .deriveComposites, .deriveActualization,
   .deriveClosedMixerAndEnvironmentAccounting,
   .deriveInputIndependentGainWithoutSelectingReadout,
   .testEntangledContextOperationsBeyondProductPreparations]

end IDT.QMClosure.NativeAttenuationBoundary
