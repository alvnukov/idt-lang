import Proofs.QMClosure.BalancedNonmedialMixerCore
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Continuity and joint complex homogeneity of the nonlinear mixer

The sum-coordinate axis is handled by an algebraic form of the unnormalized
turn with no division by that coordinate. Away from zero difference, all
remaining denominators are nonzero. At zero difference, including the origin,
the exact norm identity proves continuity without requiring continuity of the
direction-dependent parameter itself.

Joint complex scaling preserves that parameter for nonzero scalars. The
frozen turn then scales equivariantly, and the normalization ratio cancels.
These are continuity and simultaneous scaling statements, not additivity,
differentiability, physical availability, no-signalling, or full QM closure.
-/

namespace IDT.QMClosure.BalancedNonmedialMixerRegularity

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open BalancedNonmedialMixerCore
open Filter
open scoped Topology

private theorem star_nonzero {z : ℂ} (hz : z ≠ 0) : star z ≠ 0 := by
  intro h
  apply hz
  simpa using congrArg star h

/-- The coefficient replacing `B(k) * q` after cancellation of the sum-axis factor. -/
def regularCoefficient (s d : ℂ) : ℝ :=
  (2 * R s d + Complex.normSq s) / (2 * k s d * (R s d)^2)

private theorem R_pos_of_left {s : ℂ} (d : ℂ) (hs : s ≠ 0) : 0 < R s d := by
  exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hs) (Complex.normSq_nonneg d)

private theorem R_pos_of_right (s : ℂ) {d : ℂ} (hd : d ≠ 0) : 0 < R s d := by
  exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg s) (Complex.normSq_pos.mpr hd)

private theorem B_regularCoefficient (s d : ℂ) (hR : R s d ≠ 0) :
    B (k s d) = -Complex.normSq s * regularCoefficient s d := by
  have hkR : k s d * R s d = R s d + Complex.normSq s := by
    unfold k
    field_simp [hR]
  have hkR2 := congrArg (fun x : ℝ => x^2) hkR
  unfold B regularCoefficient
  field_simp [k_ne_zero s d, hR]
  nlinarith only [hkR2]

/-- This formula is valid even on the sum axis and at the origin. Its
coefficient need only be continuous where `R` is nonzero. -/
theorem turn_regular_form (s d : ℂ) :
    turn s d = Complex.I * ((A (k s d) : ℂ) * d -
      (regularCoefficient s d : ℂ) * s^2 * star d) := by
  by_cases hs : s = 0
  · subst s
    simp [turn, frozenTurn, k, R, q, A, B, regularCoefficient]
  · have hR := ne_of_gt (R_pos_of_left d hs)
    have hb : (B (k s d) : ℂ) =
        -(Complex.normSq s : ℂ) * (regularCoefficient s d : ℂ) := by
      exact_mod_cast B_regularCoefficient s d hR
    have hsq : (Complex.normSq s : ℂ) * q s = s^2 := by
      rw [Complex.normSq_eq_conj_mul_self]
      calc
        (star s * s) * q s = s * (q s * star s) := by ring
        _ = s^2 := by rw [q_mul_star]; ring
    have hbq : (B (k s d) : ℂ) * q s = -(regularCoefficient s d : ℂ) * s^2 := by
      rw [hb]
      calc
        -(Complex.normSq s : ℂ) * (regularCoefficient s d : ℂ) * q s =
            -(regularCoefficient s d : ℂ) * ((Complex.normSq s : ℂ) * q s) := by ring
        _ = _ := by rw [hsq]
    unfold turn frozenTurn
    rw [hbq]
    ring

private theorem continuous_R : Continuous (fun p : ℂ × ℂ => R p.1 p.2) :=
  (Complex.continuous_normSq.comp continuous_fst).add
    (Complex.continuous_normSq.comp continuous_snd)

private theorem continuousAt_k {p : ℂ × ℂ} (hR : R p.1 p.2 ≠ 0) :
    ContinuousAt (fun x : ℂ × ℂ => k x.1 x.2) p := by
  unfold k
  exact continuousAt_const.add
    ((Complex.continuous_normSq.comp continuous_fst).continuousAt.div
      continuous_R.continuousAt hR)

private theorem continuousAt_A_k {p : ℂ × ℂ} (hR : R p.1 p.2 ≠ 0) :
    ContinuousAt (fun x : ℂ × ℂ => A (k x.1 x.2)) p := by
  have hk := continuousAt_k hR
  unfold A
  exact (hk.add (continuousAt_const.div hk (k_ne_zero p.1 p.2))).div_const 2

private theorem continuousAt_regularCoefficient {p : ℂ × ℂ} (hR : R p.1 p.2 ≠ 0) :
    ContinuousAt (fun x : ℂ × ℂ => regularCoefficient x.1 x.2) p := by
  have hr := continuous_R.continuousAt (x := p)
  have hk := continuousAt_k hR
  unfold regularCoefficient
  exact ((continuousAt_const.mul hr).add
    (Complex.continuous_normSq.comp continuous_fst).continuousAt).div
      ((continuousAt_const.mul hk).mul (hr.pow 2))
      (mul_ne_zero (mul_ne_zero (by norm_num) (k_ne_zero p.1 p.2)) (pow_ne_zero 2 hR))

/-- No sum-axis nonzero assumption is needed. -/
theorem continuousAt_turn_of_R_ne {p : ℂ × ℂ} (hR : R p.1 p.2 ≠ 0) :
    ContinuousAt (fun x : ℂ × ℂ => turn x.1 x.2) p := by
  have hA := Complex.continuous_ofReal.continuousAt.comp (continuousAt_A_k hR)
  have hC := Complex.continuous_ofReal.continuousAt.comp
    (continuousAt_regularCoefficient hR)
  have hc : ContinuousAt
      (fun x : ℂ × ℂ => Complex.I * ((A (k x.1 x.2) : ℂ) * x.2 -
        (regularCoefficient x.1 x.2 : ℂ) * x.1^2 * star x.2)) p :=
    continuousAt_const.mul ((hA.mul continuousAt_snd).sub
      (((hC.mul (continuousAt_fst.pow 2)).mul
        (Complex.continuous_conj.continuousAt.comp continuousAt_snd))))
  simpa only [turn_regular_form] using hc

/-- At zero difference the norm identity handles all directions, including the origin. -/
theorem continuous_rotated : Continuous (fun p : ℂ × ℂ => rotated p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨s,d⟩
  by_cases hd : d = 0
  · subst d
    change Tendsto (fun p : ℂ × ℂ => rotated p.1 p.2) (𝓝 (s,0)) (𝓝 (rotated s 0))
    rw [rotated_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn : ContinuousAt (fun p : ℂ × ℂ => ‖p.2‖) (s,0) :=
      continuous_snd.norm.continuousAt
    simpa only [ContinuousAt, rotated_norm, norm_zero] using hn
  · have hR := ne_of_gt (R_pos_of_right s hd)
    have ht := continuousAt_turn_of_R_ne (p := (s,d)) hR
    have hn : ‖turn s d‖ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      exact fun h => hd ((turn_eq_zero_iff s d).mp h)
    change ContinuousAt (fun p : ℂ × ℂ =>
      (‖p.2‖ / ‖turn p.1 p.2‖) • turn p.1 p.2) (s,d)
    have hr := continuousAt_snd.norm.div ht.norm hn
    have hrc := Complex.continuous_ofReal.continuousAt.comp hr
    simpa only [Complex.real_smul] using hrc.mul ht

theorem continuous_gate : Continuous gate := by
  have hu : Continuous (fun p : ℂ × ℂ => rotated (p.1+p.2) (p.1-p.2)) :=
    continuous_rotated.comp ((continuous_fst.add continuous_snd).prodMk
      (continuous_fst.sub continuous_snd))
  unfold gate
  exact (((continuous_fst.add continuous_snd).add hu).div_const 2).prodMk
    (((continuous_fst.add continuous_snd).sub hu).div_const 2)

/-! ## Simultaneous complex scaling -/

theorem R_mul (z s d : ℂ) : R (z*s) (z*d) = Complex.normSq z * R s d := by
  unfold R
  rw [Complex.normSq_mul, Complex.normSq_mul, mul_add]

theorem k_mul {z : ℂ} (hz : z ≠ 0) (s d : ℂ) : k (z*s) (z*d) = k s d := by
  have hn : Complex.normSq z ≠ 0 := fun h => hz (Complex.normSq_eq_zero.mp h)
  simp only [k, R_mul, Complex.normSq_mul]
  rw [mul_div_mul_left _ _ hn]

private theorem q_mul_star_mul {z : ℂ} (hz : z ≠ 0) (s d : ℂ) :
    q (z*s) * star (z*d) = z * (q s * star d) := by
  unfold q
  rw [star_mul, star_mul, mul_comm (star s) (star z),
    mul_comm (star d) (star z), mul_div_mul_comm]
  calc
    (z / star z * (s / star s)) * (star z * star d) =
        (z / star z * star z) * (s / star s * star d) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ (star_nonzero hz)]

theorem frozenTurn_mul (t : ℝ) (z s d : ℂ) :
    frozenTurn t (z*s) (z*d) = z * frozenTurn t s d := by
  by_cases hz : z = 0
  · subst z
    simp [frozenTurn, q]
  · unfold frozenTurn
    rw [mul_assoc (B t : ℂ), q_mul_star_mul hz]
    ring

theorem turn_mul (z s d : ℂ) : turn (z*s) (z*d) = z * turn s d := by
  by_cases hz : z = 0
  · subst z
    simp [turn, frozenTurn, q]
  · unfold turn
    rw [k_mul hz, frozenTurn_mul]

theorem rotated_mul (z s d : ℂ) : rotated (z*s) (z*d) = z * rotated s d := by
  by_cases hz : z = 0
  · subst z
    simp [rotated, turn, frozenTurn, q]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp only [rotated, turn_mul, norm_mul]
    rw [mul_div_mul_left _ _ hn]
    simp only [Complex.real_smul]
    ring

/-- The same complex scalar acts on both inputs and both outputs. -/
theorem gate_joint_complex_homogeneity (z x y : ℂ) :
    gate (z*x,z*y) = (z*(gate (x,y)).1, z*(gate (x,y)).2) := by
  apply Prod.ext <;>
    simp only [gate, ← mul_add, ← mul_sub, rotated_mul] <;> ring

theorem gate_smul (z : ℂ) (p : ℂ × ℂ) : gate (z • p) = z • gate p := by
  rcases p with ⟨x,y⟩
  exact gate_joint_complex_homogeneity z x y

end

end IDT.QMClosure.BalancedNonmedialMixerRegularity
