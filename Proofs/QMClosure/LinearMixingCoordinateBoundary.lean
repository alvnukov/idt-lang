import Mathlib

namespace IDT.QMClosure.LinearMixingBoundary

noncomputable section

/-!
# Linear mixing and the coordinate boundary

Two independent results test the next primitive-search shortcut.

QUARTIC RIGIDITY. Any real 2x2 linear map preserving x^4+y^4 for every input
has disjoint column support: a*b=0 and c*d=0. In particular, an output cannot
depend nontrivially on both inputs. Only four inputs are needed to derive the
obstruction. No probability postulate, continuity or invertibility is assumed
in this theorem. This rules out quartic normalization together with genuine
linear mixing in these coordinates; it is not a classification of all weights.

COORDINATE COUNTEREXAMPLE. The invertible polynomial encoding
  E(x,y)=(x,y+x^2)
transports ordinary rotations into a continuous family of reversible nonlinear
maps preserving F(x,y)=x^2+(y+x^2)^2. F is positive away from the origin and is
not quadratic under ordinary scalar multiplication in the original coordinates.
The transported quarter turn fails ordinary vector additivity. Thus continuous
reversibility and a positive conserved scalar do not pick a quadratic formula
in an unspecified coordinate system.

This is exactly a reparameterization of quadratic geometry, NOT new physics,
NOT an inequivalent nonquantum theory and NOT a refutation of an intrinsic
Hilbert-space reconstruction. E also transports the composition law, under which
the conjugated transformations are linear. F is not of the separable form
w(x)+w(y), and need not be called a norm in the original vector structure.
The counterexample tests the weaker proposed requirements, not that stronger
separable class. It has no detector statistics or relativistic composite model.

Research consequence: state the operational composition law first, then derive
which dynamics preserve it. Classical probabilistic mixing and coherent merging
of alternatives are different operations. Assuming amplitude addition, or
calling a map linear before fixing that operation, does not derive it.
Neither result establishes Born, complex amplitudes, the Standard Model or GR.
-/

def PreservesQuartic (a b c d : ℝ) : Prop :=
  ∀ x y : ℝ, (a * x + b * y) ^ 4 + (c * x + d * y) ^ 4 = x ^ 4 + y ^ 4

theorem quartic_preservation_forces_disjoint_support
    (a b c d : ℝ) (preserves : PreservesQuartic a b c d) :
    a * b = 0 ∧ c * d = 0 := by
  have h10 := preserves 1 0
  have h01 := preserves 0 1
  have h11 := preserves 1 1
  have h1m := preserves 1 (-1)
  norm_num at h10 h01 h11 h1m
  have cross : (a * b) ^ 2 + (c * d) ^ 2 = 0 := by
    nlinarith [h10, h01, h11, h1m]
  constructor <;> nlinarith [sq_nonneg (a * b), sq_nonneg (c * d)]

theorem quartic_preservation_excludes_a_mixed_output :
    ¬ ∃ a b c d : ℝ, PreservesQuartic a b c d ∧ a ≠ 0 ∧ b ≠ 0 := by
  rintro ⟨a, b, c, d, preserves, ha, hb⟩
  exact (mul_ne_zero ha hb)
    (quartic_preservation_forces_disjoint_support a b c d preserves).1

abbrev Plane := ℝ × ℝ

def quadraticMass (v : Plane) : ℝ := v.1 ^ 2 + v.2 ^ 2

def encode (v : Plane) : Plane := (v.1, v.2 + v.1 ^ 2)
def decode (v : Plane) : Plane := (v.1, v.2 - v.1 ^ 2)

@[simp] theorem encode_decode (v : Plane) : encode (decode v) = v := by
  apply Prod.ext <;> simp [encode, decode]

@[simp] theorem decode_encode (v : Plane) : decode (encode v) = v := by
  apply Prod.ext <;> simp [encode, decode]

def rotated (angle : ℝ) (v : Plane) : Plane :=
  (Real.cos angle * v.1 - Real.sin angle * v.2,
    Real.sin angle * v.1 + Real.cos angle * v.2)

theorem rotation_preserves_mass (angle : ℝ) (v : Plane) :
    quadraticMass (rotated angle v) = quadraticMass v := by
  unfold quadraticMass rotated
  calc
    _ = (Real.sin angle ^ 2 + Real.cos angle ^ 2) * (v.1 ^ 2 + v.2 ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

theorem rotation_inverse (angle : ℝ) (v : Plane) :
    rotated (-angle) (rotated angle v) = v := by
  have trig := Real.sin_sq_add_cos_sq angle
  have hx := congrArg (fun z : ℝ => z * v.1) trig
  have hy := congrArg (fun z : ℝ => z * v.2) trig
  apply Prod.ext <;> simp [rotated, Real.cos_neg, Real.sin_neg] <;>
    nlinarith [hx, hy]

def transportedMass (v : Plane) : ℝ := quadraticMass (encode v)

def transportedRotation (angle : ℝ) (v : Plane) : Plane :=
  decode (rotated angle (encode v))

theorem transported_mass_nonnegative (v : Plane) : 0 ≤ transportedMass v := by
  unfold transportedMass quadraticMass
  positivity

theorem transported_mass_zero_iff_origin (v : Plane) :
    transportedMass v = 0 ↔ v = (0, 0) := by
  rcases v with ⟨x, y⟩
  simp only [transportedMass, quadraticMass, encode]
  constructor
  · intro h
    have hx : x = 0 := by nlinarith [sq_nonneg (y + x ^ 2)]
    subst x
    have hy : y = 0 := by nlinarith
    subst y
    rfl
  · rintro h
    cases h
    norm_num

theorem transported_rotation_preserves_mass (angle : ℝ) (v : Plane) :
    transportedMass (transportedRotation angle v) = transportedMass v := by
  simp only [transportedMass, transportedRotation, encode_decode]
  exact rotation_preserves_mass angle (encode v)

theorem transported_rotation_reversible (angle : ℝ) (v : Plane) :
    transportedRotation (-angle) (transportedRotation angle v) = v := by
  simp [transportedRotation, rotation_inverse]

theorem transported_rotation_jointly_continuous :
    Continuous (fun input : ℝ × Plane => transportedRotation input.1 input.2) := by
  unfold transportedRotation decode rotated encode
  fun_prop

theorem transported_rotation_at_zero (v : Plane) : transportedRotation 0 v = v := by
  simp [transportedRotation, rotated]

/-- Ordinary homogeneity of degree two fails in the original coordinates. -/
theorem transported_mass_is_not_an_ordinary_quadratic_form :
    transportedMass (2, 0) ≠ 4 * transportedMass (1, 0) := by
  norm_num [transportedMass, quadraticMass, encode]

def quarterTurn (v : Plane) : Plane := (-v.2, v.1)
def transportedQuarterTurn (v : Plane) : Plane := decode (quarterTurn (encode v))

theorem quarter_turn_is_in_continuous_family (v : Plane) :
    transportedRotation (Real.pi / 2) v = transportedQuarterTurn v := by
  simp [transportedRotation, transportedQuarterTurn, rotated, quarterTurn]

theorem transported_quarter_turn_fails_ordinary_additivity :
    transportedQuarterTurn ((1, 0) + (0, 1)) ≠
      transportedQuarterTurn (1, 0) + transportedQuarterTurn (0, 1) := by
  norm_num [transportedQuarterTurn, decode, quarterTurn, encode, Prod.mk_add_mk]

/-- Composition is transported too; its existence alone cannot fix coordinates. -/
def transportedMerge (u v : Plane) : Plane := decode (encode u + encode v)

theorem transported_quarter_turn_preserves_transported_merge (u v : Plane) :
    transportedQuarterTurn (transportedMerge u v) =
      transportedMerge (transportedQuarterTurn u) (transportedQuarterTurn v) := by
  simp only [transportedQuarterTurn, transportedMerge, encode_decode]
  congr 1
  apply Prod.ext <;> simp [quarterTurn, add_comm]

inductive OpenObligation where
  | specifyOperationalCoherentMergeSeparatelyFromClassicalMixing
  | deriveDynamicsCompatibilityWithOperationalMerge
  | fixPhysicalEquivalenceUnderReparameterization
  | deriveSeparableWeightsAndAllowedContinuousSymmetries
  | testBeyondQuarticWeightsAndTwoRealCoordinates
  | deriveComplexCarrierAndCompositeStructure
  deriving DecidableEq, Repr

def openObligations : List OpenObligation :=
  [ .specifyOperationalCoherentMergeSeparatelyFromClassicalMixing,
    .deriveDynamicsCompatibilityWithOperationalMerge,
    .fixPhysicalEquivalenceUnderReparameterization,
    .deriveSeparableWeightsAndAllowedContinuousSymmetries,
    .testBeyondQuarticWeightsAndTwoRealCoordinates,
    .deriveComplexCarrierAndCompositeStructure ]

end

end IDT.QMClosure.LinearMixingBoundary
