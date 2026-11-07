import Proofs.QMClosure.RawSparseConservationTests
import Proofs.QMClosure.NativeAttenuationCircuit
import Proofs.QMClosure.HomogeneousProductInterchange
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# A continuous homogeneous control for the six sparse test families

The supplied complex norm-square model retains all six universally quantified
test families while violating the full sparse law. The operation is continuous
and jointly complex-homogeneous. These are mathematical control properties of
a supplied encoding. No physical availability or IDT-native primitive derivation
is asserted.
-/

namespace IDT.QMClosure.RawSparsePhaseTwistControl

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

open NativeAttenuationCircuit
open RawSparseConservationSelection
open Filter
open scoped Topology

abbrev N := NativeMixerEventConeExclusion.mixer

def total (p : ℂ × ℂ) : ℝ := Complex.normSq p.1 + Complex.normSq p.2
def difference (p : ℂ × ℂ) : ℝ := Complex.normSq p.1 - Complex.normSq p.2
def cross (p : ℂ × ℂ) : ℝ := (p.1 * star p.2).im
def h (p : ℂ × ℂ) : ℝ := difference p * cross p / total p ^ 2
def phase (r : ℝ) : ℂ := (1 + Complex.I * (r : ℂ)) / (1 - Complex.I * (r : ℂ))
def gate (p : ℂ × ℂ) : ℂ × ℂ :=
  (phase (h p) * (N p).1, phase (h p) * (N p).2)

theorem phase_denominator_ne_zero (r : ℝ) : 1 - Complex.I * (r : ℂ) ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  norm_num at hr

theorem phase_normSq (r : ℝ) : Complex.normSq (phase r) = 1 := by
  rw [phase, Complex.normSq_div]
  have hd : Complex.normSq (1 - Complex.I * (r : ℂ)) ≠ 0 :=
    (Complex.normSq_pos.mpr (phase_denominator_ne_zero r)).ne'
  apply (div_eq_one_iff_eq hd).mpr
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

theorem phase_neg_mul (r : ℝ) : phase (-r) * phase r = 1 := by
  have hp := phase_denominator_ne_zero r
  have hm : 1 + Complex.I * (r : ℂ) ≠ 0 := by
    simpa using phase_denominator_ne_zero (-r)
  unfold phase
  push_cast
  field_simp [hp, hm]
  ring

theorem native_homogeneous (c : ℂ) (p : ℂ × ℂ) :
    N (c * p.1, c * p.2) = (c * (N p).1, c * (N p).2) := by
  rcases p with ⟨x,y⟩
  apply Prod.ext <;> simp only [mixer_fst, mixer_snd] <;> ring

theorem native_difference (p : ℂ × ℂ) : difference (N p) = -2 * cross p := by
  rcases p with ⟨x,y⟩
  norm_num [difference, cross, mixer_fst, mixer_snd, a, b, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem native_cross (p : ℂ × ℂ) : cross (N p) = difference p / 2 := by
  rcases p with ⟨x,y⟩
  norm_num [difference, cross, mixer_fst, mixer_snd, a, b, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem native_total (p : ℂ × ℂ) : total (N p) = total p :=
  NativeMixerEventConeExclusion.mixer_conserves p.1 p.2

theorem h_native (p : ℂ × ℂ) : h (N p) = -h p := by
  rw [h, native_difference, native_cross, native_total, h]
  ring

theorem cross_scale (c : ℂ) (p : ℂ × ℂ) :
    cross (c * p.1, c * p.2) = Complex.normSq c * cross p := by
  simp only [cross, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem h_scale (c : ℂ) (p : ℂ × ℂ) (hc : c ≠ 0) :
    h (c * p.1, c * p.2) = h p := by
  have hn : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  simp only [h, difference, total, Complex.normSq_mul, cross_scale]
  field_simp

theorem phase_ne_zero (r : ℝ) : phase r ≠ 0 := by
  intro he
  have hn := phase_normSq r
  rw [he] at hn
  norm_num at hn

theorem h_gate (p : ℂ × ℂ) : h (gate p) = -h p := by
  exact (h_scale _ (N p) (phase_ne_zero _)).trans (h_native p)

theorem gate_square (p : ℂ × ℂ) : gate (gate p) = p.swap := by
  have hs := NativeMixerEventConeExclusion.mixer_square p
  unfold gate
  rw [show h (phase (h p) * (N p).1, phase (h p) * (N p).2) = -h p from h_gate p,
    native_homogeneous, hs]
  apply Prod.ext <;> dsimp only <;>
    rw [← mul_assoc, phase_neg_mul, one_mul]

theorem h_diagonal (x : ℂ) : h (x,x) = 0 := by simp [h, difference]
theorem h_vacuum_left (x : ℂ) : h (0,x) = 0 := by simp [h, cross]
theorem h_vacuum_right (x : ℂ) : h (x,0) = 0 := by simp [h, cross]

theorem gate_of_h_zero (p : ℂ × ℂ) (hp : h p = 0) : gate p = N p := by
  simp [gate, hp, phase]

theorem gate_transparent (x : ℂ) : gate (x,x) = (x,x) := by
  rw [gate_of_h_zero _ (h_diagonal x)]
  exact NativeMixerEventConeExclusion.mixer_transparent x

def contract : Contract ℂ where
  chosenZero := 0
  operation := gate
  weight := Complex.normSq
  vacuum := by norm_num
  square := gate_square
  transparent := gate_transparent

theorem nonnegative (x : ℂ) : 0 ≤ contract.weight x := Complex.normSq_nonneg x

theorem port_weight_fst (p : ℂ × ℂ) :
    Complex.normSq (gate p).1 = Complex.normSq (N p).1 := by
  simp only [gate, Complex.normSq_mul, phase_normSq, one_mul]

theorem port_weight_snd (p : ℂ × ℂ) :
    Complex.normSq (gate p).2 = Complex.normSq (N p).2 := by
  simp only [gate, Complex.normSq_mul, phase_normSq, one_mul]

theorem pair_conserved : PairConserved contract := by
  intro x y
  change Complex.normSq (gate (x,y)).1 + Complex.normSq (gate (x,y)).2 = _
  rw [port_weight_fst, port_weight_snd]
  exact NativeMixerEventConeExclusion.mixer_conserves x y

theorem native_vacuum_A (x : ℂ) : A contract x = a * x := by
  change (gate (x,0)).1 = _
  rw [gate_of_h_zero _ (h_vacuum_right x), mixer_fst]
  ring

theorem native_vacuum_B (x : ℂ) : B contract x = b * x := by
  change (gate (0,x)).1 = _
  rw [gate_of_h_zero _ (h_vacuum_left x), mixer_fst]
  ring

theorem gate_joint_complex_homogeneity (c : ℂ) (p : ℂ × ℂ) :
    gate (c * p.1, c * p.2) = (c * (gate p).1, c * (gate p).2) := by
  by_cases hc : c = 0
  · subst c
    simp [gate, mixer_fst, mixer_snd]
  · unfold gate
    rw [h_scale c p hc, native_homogeneous]
    apply Prod.ext <;> dsimp only <;> ring


/-- Exact interchange on scalar product arrays follows from joint homogeneity. -/
theorem interchange_product_inputs (p q : ℂ × ℂ) :
    RawNetworkMedialWall.columns gate
        (RawNetworkMedialWall.rows gate (HomogeneousProductInterchange.productArray p q)) =
      RawNetworkMedialWall.rows gate
        (RawNetworkMedialWall.columns gate (HomogeneousProductInterchange.productArray p q)) :=
  HomogeneousProductInterchange.interchange_productArray gate gate
    gate_joint_complex_homogeneity gate_joint_complex_homogeneity p q

theorem weight_m (x y : ℂ) :
    contract.weight (m contract x y) = Complex.normSq (N (x,y)).1 :=
  port_weight_fst (x,y)

theorem h_split (x : ℂ) : h (a*x,b*x) = 0 := by
  have he : Complex.normSq (a*x) - Complex.normSq (b*x) = 0 := by
    norm_num [Complex.normSq_mul, a, b, Complex.normSq_apply,
      Complex.div_re, Complex.div_im]
    ring
  unfold h difference
  rw [he]
  simp

theorem h_split_reverse (x : ℂ) : h (b*x,a*x) = 0 := by
  have he : Complex.normSq (b*x) - Complex.normSq (a*x) = 0 := by
    norm_num [Complex.normSq_mul, a, b, Complex.normSq_apply,
      Complex.div_re, Complex.div_im]
    ring
  unfold h difference
  rw [he]
  simp

theorem native_sparse_identity (x y z : ℂ) :
    Complex.normSq (N ((N (x,y)).1, a*z)).1 +
      Complex.normSq (N ((N (x,y)).2, b*z)).1 =
    Complex.normSq (N (x,z)).1 + Complex.normSq (a*y) := by
  norm_num [mixer_fst, mixer_snd, a, b, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem sparse_at_of_h_zero (x y z : ℂ) (hp : h (x,y) = 0) :
    RawSparseConservationTests.SparseAt contract x y z := by
  have hg := gate_of_h_zero (x,y) hp
  have hfirst : m contract x y = (N (x,y)).1 := congrArg Prod.fst hg
  have hsecond : m contract y x = (N (x,y)).2 := by
    rw [← second_eq_reverse contract]
    exact congrArg Prod.snd hg
  unfold RawSparseConservationTests.SparseAt
  rw [weight_m, weight_m, weight_m, native_vacuum_A, native_vacuum_B,
    native_vacuum_A, hfirst, hsecond]
  exact native_sparse_identity x y z

theorem vacuum_reference (x y : ℂ) :
    RawSparseConservationTests.SparseAt contract x y 0 := by
  have hhalf (w : ℂ) : contract.weight (A contract w) = Complex.normSq w / 2 := by
    rw [native_vacuum_A]
    norm_num [contract, Complex.normSq_mul, a, Complex.normSq_apply,
      Complex.div_re, Complex.div_im]
    ring
  have hc := pair_conserved x y
  rw [second_eq_reverse contract] at hc
  unfold RawSparseConservationTests.SparseAt
  rw [show (0 : ℂ) = contract.chosenZero from rfl, A_zero, B_zero]
  change contract.weight (A contract (m contract x y)) +
    contract.weight (A contract (m contract y x)) =
    contract.weight (A contract x) + contract.weight (A contract y)
  simp only [hhalf]
  change Complex.normSq (m contract x y) + Complex.normSq (m contract y x) =
    Complex.normSq x + Complex.normSq y at hc
  linarith

theorem tests : RawSparseConservationTests.Tests contract where
  vacuum_diagonal t := sparse_at_of_h_zero 0 t t (h_vacuum_left t)
  vacuum_reference := vacuum_reference
  diagonal t z := sparse_at_of_h_zero t t z (h_diagonal t)
  split_forward t z := by
    rw [native_vacuum_A, native_vacuum_B]
    exact sparse_at_of_h_zero (a*t) (b*t) z (h_split t)
  split_reverse t z := by
    rw [native_vacuum_A, native_vacuum_B]
    exact sparse_at_of_h_zero (b*t) (a*t) z (h_split_reverse t)
  vacuum_second t z := sparse_at_of_h_zero t 0 z (h_vacuum_right t)

theorem witness_h : h (1,1+Complex.I) = 1/9 := by
  norm_num [h, difference, cross, total, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im]

theorem witness_phase : phase (h (1,1+Complex.I)) = (40+9*Complex.I)/41 := by
  rw [witness_h]
  apply Complex.ext <;>
    norm_num [phase, Complex.div_re, Complex.div_im, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]

theorem sparse_witness :
    contract.weight (m contract (m contract 1 (1+Complex.I)) (A contract Complex.I)) +
      contract.weight (m contract (m contract (1+Complex.I) 1) (B contract Complex.I)) =
        122/41 ∧
    contract.weight (m contract 1 Complex.I) +
      contract.weight (A contract (1+Complex.I)) = 3 := by
  have hh : h (1+Complex.I,1) = 1/9 := by
    norm_num [h, difference, cross, total, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im]
  constructor
  · rw [weight_m, weight_m, native_vacuum_A, native_vacuum_B]
    change Complex.normSq (N ((gate (1,1+Complex.I)).1,a*Complex.I)).1 +
      Complex.normSq (N ((gate (1+Complex.I,1)).1,b*Complex.I)).1 = _
    simp only [gate]
    rw [witness_phase, hh]
    norm_num [phase, mixer_fst, mixer_snd, a, b,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im]
  · rw [weight_m, native_vacuum_A]
    norm_num [contract, mixer_fst, a, b, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.div_re, Complex.div_im]

theorem not_sparse_law : ¬ SparseMarginalLaw contract := by
  intro hs
  have hw := hs 1 (1+Complex.I) Complex.I
  rw [sparse_witness.1, sparse_witness.2] at hw
  norm_num at hw

theorem not_observed_medial : ¬ ObservedMedial contract := by
  intro hm
  exact not_sparse_law (sparse_of_conserved_and_observed_medial contract pair_conserved hm)

private theorem continuous_native_fst :
    Continuous (fun p : ℂ × ℂ => (N p).1) := by
  have he : (fun p : ℂ × ℂ => (N p).1) =
      (fun p : ℂ × ℂ => a*p.1+b*p.2) :=
    funext (fun p => mixer_fst p.1 p.2)
  rw [he]
  exact (continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)

private theorem continuous_native_snd :
    Continuous (fun p : ℂ × ℂ => (N p).2) := by
  have he : (fun p : ℂ × ℂ => (N p).2) =
      (fun p : ℂ × ℂ => b*p.1+a*p.2) :=
    funext (fun p => mixer_snd p.1 p.2)
  rw [he]
  exact (continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)

theorem port_norm_fst (p : ℂ × ℂ) : ‖(gate p).1‖ = ‖(N p).1‖ := by
  have hw := port_weight_fst p
  simp only [Complex.normSq_eq_norm_sq] at hw
  nlinarith [norm_nonneg (gate p).1, norm_nonneg (N p).1]

theorem port_norm_snd (p : ℂ × ℂ) : ‖(gate p).2‖ = ‖(N p).2‖ := by
  have hw := port_weight_snd p
  simp only [Complex.normSq_eq_norm_sq] at hw
  nlinarith [norm_nonneg (gate p).2, norm_nonneg (N p).2]

private theorem continuous_total : Continuous total :=
  (Complex.continuous_normSq.comp continuous_fst).add
    (Complex.continuous_normSq.comp continuous_snd)

private theorem continuous_difference : Continuous difference :=
  (Complex.continuous_normSq.comp continuous_fst).sub
    (Complex.continuous_normSq.comp continuous_snd)

private theorem continuous_cross : Continuous cross :=
  Complex.continuous_im.comp
    (continuous_fst.mul (Complex.continuous_conj.comp continuous_snd))

theorem continuousAt_h {p : ℂ × ℂ} (hp : total p ≠ 0) : ContinuousAt h p :=
  (continuous_difference.mul continuous_cross).continuousAt.div
    (continuous_total.pow 2).continuousAt (pow_ne_zero 2 hp)

theorem continuous_phase : Continuous phase := by
  unfold phase
  exact (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).div
    (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal))
    phase_denominator_ne_zero

theorem total_ne_zero {p : ℂ × ℂ} (hp : p ≠ (0,0)) : total p ≠ 0 := by
  intro he
  have h1 := Complex.normSq_nonneg p.1
  have h2 := Complex.normSq_nonneg p.2
  have hz1 : p.1 = 0 := Complex.normSq_eq_zero.mp (by unfold total at he; linarith)
  have hz2 : p.2 = 0 := Complex.normSq_eq_zero.mp (by unfold total at he; linarith)
  exact hp (Prod.ext hz1 hz2)

theorem continuous_gate : Continuous gate := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p = (0,0)
  · subst p
    have hg : gate (0,0) = (0,0) := gate_transparent 0
    have hf : Tendsto (fun p : ℂ × ℂ => (gate p).1) (𝓝 (0,0)) (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have hn := continuous_native_fst.norm.tendsto (0,0)
      simpa only [port_norm_fst, mixer_fst, mul_zero, add_zero, norm_zero] using hn
    have hs : Tendsto (fun p : ℂ × ℂ => (gate p).2) (𝓝 (0,0)) (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have hn := continuous_native_snd.norm.tendsto (0,0)
      simpa only [port_norm_snd, mixer_snd, mul_zero, add_zero, norm_zero] using hn
    have hp' := hf.prodMk_nhds hs
    simpa only [ContinuousAt, hg] using hp'
  · have hc := continuous_phase.continuousAt.comp (continuousAt_h (total_ne_zero hp))
    exact (hc.mul continuous_native_fst.continuousAt).prodMk
      (hc.mul continuous_native_snd.continuousAt)

/-- Continuity and joint scaling still leave a strict gap between the six test
families and the full sparse law. -/
theorem continuous_homogeneous_countercontrol :
    RawSparseConservationTests.Tests contract ∧
    (∀ x, 0 ≤ contract.weight x) ∧ PairConserved contract ∧
    Continuous contract.operation ∧
    (∀ c p, contract.operation (c*p.1,c*p.2) =
      (c*(contract.operation p).1,c*(contract.operation p).2)) ∧
    ¬ SparseMarginalLaw contract ∧ ¬ ObservedMedial contract :=
  ⟨tests, nonnegative, pair_conserved, continuous_gate,
    gate_joint_complex_homogeneity, not_sparse_law, not_observed_medial⟩

end
end IDT.QMClosure.RawSparsePhaseTwistControl
