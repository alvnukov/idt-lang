import Mathlib

/-!
# Closed-state-set circle closure of two cubic coordinate rotations

This is a mathematical closure statement for a closed subset of real coordinate
space. It supplies no physical availability of limiting operations.
-/

noncomputable section

namespace IDT.QMClosure.CubicRotationCircleDensity

open Set

/-- Coordinates carry their usual product topology. -/
abbrev Vec3 := ℝ × ℝ × ℝ

private def sqrtThree : ℝ := Real.sqrt 3
private def invSqrtFive : ℝ := Real.sqrt (1 / 5 : ℝ)

private theorem sqrtThree_sq : sqrtThree ^ 2 = 3 := by
  exact Real.sq_sqrt (by norm_num)

private theorem sqrtThree_cube : sqrtThree ^ 3 = 3 * sqrtThree := by
  calc
    sqrtThree ^ 3 = sqrtThree ^ 2 * sqrtThree := by ring
    _ = 3 * sqrtThree := by rw [sqrtThree_sq]

private theorem sqrtThree_fourth : sqrtThree ^ 4 = 9 := by
  calc
    sqrtThree ^ 4 = (sqrtThree ^ 2) ^ 2 := by ring
    _ = 9 := by rw [sqrtThree_sq]; norm_num

private theorem sqrtThree_fifth : sqrtThree ^ 5 = 9 * sqrtThree := by
  calc
    sqrtThree ^ 5 = sqrtThree ^ 4 * sqrtThree := by ring
    _ = 9 * sqrtThree := by rw [sqrtThree_fourth]

private theorem invSqrtFive_sq : invSqrtFive ^ 2 = 1 / 5 := by
  exact Real.sq_sqrt (by norm_num)

private theorem invSqrtFive_pos : 0 < invSqrtFive := by
  exact Real.sqrt_pos.2 (by norm_num)

/-- The positive 120-degree rotation around the third coordinate axis. -/
def az (p : Vec3) : Vec3 :=
  ⟨-p.1 / 2 - sqrtThree / 2 * p.2.1,
    sqrtThree / 2 * p.1 - p.2.1 / 2, p.2.2⟩

/-- The positive 120-degree rotation around the first coordinate axis. -/
def ax (p : Vec3) : Vec3 :=
  ⟨p.1, -p.2.1 / 2 - sqrtThree / 2 * p.2.2,
    sqrtThree / 2 * p.2.1 - p.2.2 / 2⟩

theorem az_cube (p : Vec3) : az (az (az p)) = p := by
  rcases p with ⟨x, y, z⟩
  ext <;> dsimp [az] <;> ring_nf <;>
    simp only [sqrtThree_sq, sqrtThree_cube] <;> ring

theorem ax_cube (p : Vec3) : ax (ax (ax p)) = p := by
  rcases p with ⟨x, y, z⟩
  ext <;> dsimp [ax] <;> ring_nf <;>
    simp only [sqrtThree_sq, sqrtThree_cube] <;> ring

/-- The first unit axis, parallel to `(1, sqrt 3, 1)`. -/
def axisN : Vec3 :=
  ⟨invSqrtFive, sqrtThree * invSqrtFive, invSqrtFive⟩

/-- The second axis is the image of the first under `az`. -/
def axisN' : Vec3 := ⟨-2 * invSqrtFive, 0, invSqrtFive⟩

def dot (p q : Vec3) : ℝ := p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

/-- Rodrigues rotation, parametrized by a pair on the real unit circle. -/
def rodrigues (axis : Vec3) (k l : ℝ) (p : Vec3) : Vec3 :=
  ⟨k * p.1 + l * (axis.2.1 * p.2.2 - axis.2.2 * p.2.1) +
      (1 - k) * dot axis p * axis.1,
   k * p.2.1 + l * (axis.2.2 * p.1 - axis.1 * p.2.2) +
      (1 - k) * dot axis p * axis.2.1,
   k * p.2.2 + l * (axis.1 * p.2.1 - axis.2.1 * p.1) +
      (1 - k) * dot axis p * axis.2.2⟩

/-- An arithmetic-friendly expression for rotation about `axisN`. -/
private def circleN (k l : ℝ) (p : Vec3) : Vec3 :=
  ⟨k * p.1 + l * invSqrtFive * (sqrtThree * p.2.2 - p.2.1) +
      (1 - k) * (p.1 + sqrtThree * p.2.1 + p.2.2) / 5,
   k * p.2.1 + l * invSqrtFive * (p.1 - p.2.2) +
      (1 - k) * (p.1 + sqrtThree * p.2.1 + p.2.2) * sqrtThree / 5,
   k * p.2.2 + l * invSqrtFive * (p.2.1 - sqrtThree * p.1) +
      (1 - k) * (p.1 + sqrtThree * p.2.1 + p.2.2) / 5⟩

private theorem circleN_eq_rodrigues (k l : ℝ) (p : Vec3) :
    circleN k l p = rodrigues axisN k l p := by
  rcases p with ⟨x, y, z⟩
  ext <;> dsimp [circleN, rodrigues, axisN, dot] <;> ring_nf <;>
    simp only [invSqrtFive_sq] <;> ring

private theorem circleN_mul (k l k' l' : ℝ) (p : Vec3) :
    circleN k l (circleN k' l' p) =
      circleN (k * k' - l * l') (l * k' + k * l') p := by
  rcases p with ⟨x, y, z⟩
  ext <;> dsimp [circleN] <;> ring_nf <;>
    simp only [sqrtThree_sq, sqrtThree_cube, sqrtThree_fourth, invSqrtFive_sq] <;> ring

private theorem circleN_one (p : Vec3) : circleN 1 0 p = p := by
  rcases p with ⟨x, y, z⟩
  simp [circleN]

/-- Angle parameters are quotient angles, with period `2 * pi`. -/
private def angleN (t : Real.Angle) (p : Vec3) : Vec3 :=
  circleN t.cos t.sin p

private theorem angleN_add (t u : Real.Angle) (p : Vec3) :
    angleN (t + u) p = angleN t (angleN u p) := by
  unfold angleN
  rw [circleN_mul, Real.Angle.cos_add, Real.Angle.sin_add]

private theorem angleN_zero (p : Vec3) : angleN 0 p = p := by
  simpa [angleN] using circleN_one p

private theorem continuous_angleN (p : Vec3) : Continuous (fun t => angleN t p) := by
  unfold angleN circleN
  continuity

private def theta : ℝ := Real.arccos (-7 / 8 : ℝ)

private theorem cos_theta : Real.cos theta = -7 / 8 := by
  exact Real.cos_arccos (by norm_num) (by norm_num)

private theorem sin_theta_nonneg : 0 ≤ Real.sin theta := by
  rw [theta, Real.sin_arccos]
  positivity

/-- This exact sine coefficient avoids any numerical angle approximation. -/
private theorem sin_theta_mul_invSqrtFive :
    Real.sin theta * invSqrtFive = sqrtThree / 8 := by
  have hsin : (Real.sin theta) ^ 2 = 15 / 64 := by
    have h := Real.sin_sq_add_cos_sq theta
    rw [cos_theta] at h
    nlinarith
  have hleft : 0 ≤ Real.sin theta * invSqrtFive :=
    mul_nonneg sin_theta_nonneg (le_of_lt invSqrtFive_pos)
  have hright : 0 ≤ sqrtThree / 8 := by
    dsimp [sqrtThree]
    positivity
  have hsq : (Real.sin theta * invSqrtFive) ^ 2 = (sqrtThree / 8) ^ 2 := by
    rw [mul_pow, hsin, invSqrtFive_sq, div_pow, sqrtThree_sq]
    norm_num
  nlinarith

/-- The actual finite word is a single rotation about the displayed axis. -/
theorem product_factorization (p : Vec3) :
    angleN (theta : Real.Angle) p = az (ax p) := by
  rcases p with ⟨x, y, z⟩
  simp only [angleN, Real.Angle.cos_coe, Real.Angle.sin_coe, cos_theta]
  ext <;> dsimp [circleN, az, ax] <;>
    rw [sin_theta_mul_invSqrtFive] <;> ring_nf <;>
    simp only [sqrtThree_sq] <;> ring

private theorem inverse_product_factorization (p : Vec3) :
    angleN (-(theta : Real.Angle)) p = ax (ax (az (az p))) := by
  have hinv : az (ax (angleN (-(theta : Real.Angle)) p)) = p := by
    rw [← product_factorization, ← angleN_add]
    simp only [add_neg_cancel, angleN_zero]
  have h := congrArg (fun q => ax (ax (az (az q)))) hinv
  simpa only [az_cube, ax_cube] using h

/-- Niven's theorem excludes rational multiples of the full angular period. -/
private theorem theta_div_two_pi_irrational : Irrational (theta / (2 * Real.pi)) := by
  intro h
  rcases h with ⟨q, hq⟩
  have hperiod : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have htheta : theta = (q : ℝ) * (2 * Real.pi) :=
    (div_eq_iff hperiod).mp hq.symm
  have hrat : theta = ((2 * q : ℚ) : ℝ) * Real.pi := by
    push_cast
    nlinarith [htheta]
  have hniven := niven (θ := theta) ⟨2 * q, hrat⟩
    ⟨(-7 / 8 : ℚ), by norm_num [cos_theta]⟩
  norm_num [cos_theta] at hniven

private theorem integer_angle_mem {C : Set Vec3}
    (haz : MapsTo az C C) (hax : MapsTo ax C C) {p : Vec3} (hp : p ∈ C) :
    ∀ n : ℤ, angleN (n • (theta : Real.Angle)) p ∈ C := by
  intro n
  induction n using Int.induction_on with
  | zero => simpa only [zero_zsmul, angleN_zero] using hp
  | succ n ih =>
      have hstep : ((n : ℤ) + 1) • (theta : Real.Angle) =
          (theta : Real.Angle) + (n : ℤ) • (theta : Real.Angle) := by
        rw [add_zsmul, one_zsmul, add_comm]
      rw [hstep, angleN_add, product_factorization]
      exact haz (hax ih)
  | pred n ih =>
      have hstep : (-(n : ℤ) - 1) • (theta : Real.Angle) =
          -(theta : Real.Angle) + (-(n : ℤ)) • (theta : Real.Angle) := by
        rw [sub_zsmul, one_zsmul]
        abel
      rw [hstep, angleN_add, inverse_product_factorization]
      exact hax (hax (haz (haz ih)))

/-- Closedness transfers dense integer-word invariance to every angle. -/
theorem closed_invariant_angleN {C : Set Vec3} (hclosed : IsClosed C)
    (haz : MapsTo az C C) (hax : MapsTo ax C C) (t : Real.Angle) :
    MapsTo (angleN t) C C := by
  intro p hp
  have hdense : DenseRange (fun n : ℤ => n • (theta : Real.Angle)) :=
    AddCircle.denseRange_zsmul_coe_iff.2 theta_div_two_pi_irrational
  exact hdense.induction_on t
    (hclosed.preimage (continuous_angleN p)) (integer_angle_mem haz hax hp)

private theorem exists_angle_pair (k l : ℝ) (hcircle : k ^ 2 + l ^ 2 = 1) :
    ∃ t : Real.Angle, t.cos = k ∧ t.sin = l := by
  let z : ℂ := ⟨k, l⟩
  have hnormsq : ‖z‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    change k * k + l * l = 1
    nlinarith [hcircle]
  have hnorm : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hnorm
  refine ⟨(Complex.arg z : Real.Angle), ?_, ?_⟩
  · simp only [Real.Angle.cos_coe, Complex.cos_arg hz, hnorm, div_one]
    rfl
  · simp only [Real.Angle.sin_coe, Complex.sin_arg, hnorm, div_one]
    rfl

/-- Full-circle preservation about a specified unit axis. -/
def FullCircleInvariant (C : Set Vec3) (axis : Vec3) : Prop :=
  ∀ k l : ℝ, k ^ 2 + l ^ 2 = 1 → MapsTo (rodrigues axis k l) C C

theorem closed_invariant_first_circle {C : Set Vec3} (hclosed : IsClosed C)
    (haz : MapsTo az C C) (hax : MapsTo ax C C) : FullCircleInvariant C axisN := by
  intro k l hcircle p hp
  obtain ⟨t, htcos, htsin⟩ := exists_angle_pair k l hcircle
  have h := closed_invariant_angleN hclosed haz hax t hp
  simpa only [angleN, htcos, htsin, circleN_eq_rodrigues] using h

theorem az_axisN : az axisN = axisN' := by
  ext <;> dsimp [az, axisN, axisN'] <;> ring_nf
  all_goals simp only [sqrtThree_sq]; ring

/-- Conjugating by the finite cubic word transports the whole circle. -/
theorem conjugate_circle (k l : ℝ) (p : Vec3) :
    az (circleN k l (az (az p))) = rodrigues axisN' k l p := by
  rcases p with ⟨x, y, z⟩
  ext <;> dsimp [az, circleN, rodrigues, axisN', dot] <;> ring_nf <;>
    simp only [sqrtThree_sq, sqrtThree_cube, sqrtThree_fourth, sqrtThree_fifth, invSqrtFive_sq] <;> ring

theorem closed_invariant_second_circle {C : Set Vec3} (hclosed : IsClosed C)
    (haz : MapsTo az C C) (hax : MapsTo ax C C) : FullCircleInvariant C axisN' := by
  intro k l hcircle p hp
  have hfirst := closed_invariant_first_circle hclosed haz hax k l hcircle
    (haz (haz hp))
  rw [← circleN_eq_rodrigues] at hfirst
  have h := haz hfirst
  rwa [conjugate_circle] at h

/-- The axes are unit and their inner product is exactly `-1/5`. -/
theorem axes_geometry :
    dot axisN axisN = 1 ∧ dot axisN' axisN' = 1 ∧ dot axisN axisN' = -1 / 5 := by
  unfold dot axisN axisN'
  constructor
  · ring_nf
    simp only [sqrtThree_sq, invSqrtFive_sq]
    norm_num
  constructor <;> ring_nf <;> simp only [invSqrtFive_sq] <;> norm_num

/-- The two actual axes are nonparallel, certified by a strict inner-product bound. -/
theorem axes_nonparallel : |dot axisN axisN'| < 1 := by
  rw [axes_geometry.2.2]
  norm_num

/-- Closed finite-gate invariance supplies the two genuine, nonparallel circles. -/
theorem closed_cubic_invariant_two_circles {C : Set Vec3} (hclosed : IsClosed C)
    (haz : MapsTo az C C) (hax : MapsTo ax C C) :
    FullCircleInvariant C axisN ∧ FullCircleInvariant C axisN' :=
  ⟨closed_invariant_first_circle hclosed haz hax,
   closed_invariant_second_circle hclosed haz hax⟩

end IDT.QMClosure.CubicRotationCircleDensity
