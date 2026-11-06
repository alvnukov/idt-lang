import Proofs.QMClosure.NativeMixerEventConeExclusion
import Proofs.QMClosure.DyadicMixtureLinearization

/-!
# Finite rational coordinates spanned by native wire events

The ambient space is explicitly finite rational Hermitian coordinates. Complex
scalar wires, a fresh vacuum port for each separate experiment, availability of
selected-port events, and classical half mixing remain supplied assumptions.
The signed recovery identities below are representational linear algebra, not
physical event subtraction. They do not construct a joint measurement of the
whole spanning family or permit reuse of an uncleared ancilla.

Midpoint accounting on a domain containing this family gives a unique rational
linear functional. A finite calibration control shows why that conclusion does
not establish positivity on every positive contraction, a density matrix,
probability actualization, or full QM closure.
-/

namespace IDT.QMClosure.NativeWireEffectSpan

noncomputable section

open scoped BigOperators
open MixerGeneratedProcessWall

abbrev UpperPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Coord (n : ℕ) := Fin n ⊕ (UpperPair n × Bool)
abbrev V (n : ℕ) := Coord n → ℚ

/-- `false` denotes the real upper entry, `true` the imaginary upper entry. -/
def atom {n : ℕ} (x : Fin n → ℂ) : Coord n → ℝ
  | .inl i => Complex.normSq (x i)
  | .inr (p, false) => 2 * (star (x p.val.1) * x p.val.2).re
  | .inr (p, true) => -(2 * (star (x p.val.1) * x p.val.2).im)

/-- The full complex quadratic form, including both upper-entry coordinates. -/
def quadratic {n : ℕ} (v : V n) (x : Fin n → ℂ) : ℝ :=
  ∑ c, (v c : ℝ) * atom x c

theorem quadratic_add {n : ℕ} (v w : V n) (x : Fin n → ℂ) :
    quadratic (v + w) x = quadratic v x + quadratic w x := by
  simp [quadratic, add_mul, Finset.sum_add_distrib]

theorem quadratic_smul {n : ℕ} (q : ℚ) (v : V n) (x : Fin n → ℂ) :
    quadratic (q • v) x = (q : ℝ) * quadratic v x := by
  simp only [quadratic, Pi.smul_apply, smul_eq_mul, Rat.cast_mul,
    mul_assoc, Finset.mul_sum]

theorem quadratic_single {n : ℕ} (c : Coord n) (x : Fin n → ℂ) :
    quadratic (Pi.single c 1) x = atom x c := by
  classical
  simp [quadratic, Pi.single_apply, apply_ite]

def P {n : ℕ} (i : Fin n) : V n := Pi.single (.inl i) 1
def X {n : ℕ} (p : UpperPair n) : V n := Pi.single (.inr (p, false)) 1
def Y {n : ℕ} (p : UpperPair n) : V n := Pi.single (.inr (p, true)) 1

def H {n : ℕ} (p : UpperPair n) : V n :=
  (1 / 2 : ℚ) • P p.val.1 + (1 / 2 : ℚ) • P p.val.2 - (1 / 2 : ℚ) • Y p

def F {n : ℕ} (p : UpperPair n) : V n :=
  (1 / 8 : ℚ) • P p.val.1 + (5 / 8 : ℚ) • P p.val.2 - (1 / 4 : ℚ) • X p

theorem recover_Y {n : ℕ} (p : UpperPair n) :
    Y p = P p.val.1 + P p.val.2 - (2 : ℚ) • H p := by
  ext c
  simp only [H, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem recover_X {n : ℕ} (p : UpperPair n) :
    X p = (1 / 2 : ℚ) • P p.val.1 + (5 / 2 : ℚ) • P p.val.2 - (4 : ℚ) • F p := by
  ext c
  simp only [F, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Native event coordinates span without a supplied spanning premise. -/
theorem native_span_eq_top {n : ℕ} (D : Set (V n))
    (hP : ∀ i, P i ∈ D) (hH : ∀ p, H p ∈ D) (hF : ∀ p, F p ∈ D) :
    Submodule.span ℚ D = ⊤ := by
  classical
  let S := Submodule.span ℚ D
  have hp (i : Fin n) : P i ∈ S := Submodule.subset_span (hP i)
  have hy (p : UpperPair n) : Y p ∈ S := by
    rw [recover_Y]
    exact S.sub_mem (S.add_mem (hp _) (hp _))
      (S.smul_mem 2 (Submodule.subset_span (hH p)))
  have hx (p : UpperPair n) : X p ∈ S := by
    rw [recover_X]
    exact S.sub_mem (S.add_mem (S.smul_mem _ (hp _)) (S.smul_mem _ (hp _)))
      (S.smul_mem 4 (Submodule.subset_span (hF p)))
  have hb (c : Coord n) : Pi.single c (1 : ℚ) ∈ S := by
    rcases c with i | ⟨p, b⟩
    · exact hp i
    · cases b
      · exact hx p
      · exact hy p
  apply top_unique
  intro v _
  have hv : v = ∑ c, v c • (Pi.single c (1 : ℚ) : V n) := by
    ext c
    simp [Pi.single_apply, apply_ite]
  rw [hv]
  exact S.sum_mem fun c _ => S.smul_mem _ (hb c)

theorem quadratic_P {n : ℕ} (i : Fin n) (x : Fin n → ℂ) :
    quadratic (P i) x = Complex.normSq (x i) := quadratic_single _ _

theorem quadratic_H {n : ℕ} (p : UpperPair n) (x : Fin n → ℂ) :
    quadratic (H p) x =
      Complex.normSq (CompositeProductControls.RawSign.n (x p.val.1) (x p.val.2)) := by
  have hs (v w : V n) : quadratic (v - w) x = quadratic v x - quadratic w x := by
    simp [quadratic, sub_mul, Finset.sum_sub_distrib]
  rw [H, hs, quadratic_add, quadratic_smul, quadratic_smul, quadratic_smul,
    quadratic_P, quadratic_P, Y, quadratic_single]
  norm_num [atom, Complex.normSq_apply, CompositeProductControls.RawSign.n_re,
    CompositeProductControls.RawSign.n_im, Complex.mul_re, Complex.mul_im]
  ring

theorem quadratic_F {n : ℕ} (p : UpperPair n) (x : Fin n → ℂ) :
    quadratic (F p) x =
      NativeMixerEventConeExclusion.compressedWeight (x p.val.1) (x p.val.2) 0 := by
  rw [NativeMixerEventConeExclusion.native_selected_weight,
    ContextualActualizationControl.complexExpectation_real]
  have hs (v w : V n) : quadratic (v - w) x = quadratic v x - quadratic w x := by
    simp [quadratic, sub_mul, Finset.sum_sub_distrib]
  rw [F, hs, quadratic_add, quadratic_smul, quadratic_smul, quadratic_smul,
    quadratic_P, quadratic_P, X, quadratic_single]
  norm_num [atom, Complex.normSq_apply, ContextualActualizationControl.quadratic,
    NativeMixerEventConeExclusion.F, Complex.mul_re, Complex.mul_im]
  ring

/-! Each pair uses one fresh vacuum port in its own experiment. -/

abbrev Wire (n : ℕ) := Fin n ⊕ Unit
abbrev NativeCircuit (n : ℕ) := Circuit (ι := Wire n) NativeMixerEventConeExclusion.mixer

def input {n : ℕ} (x : Fin n → ℂ) : Wire n → ℂ := Sum.elim x (fun _ => 0)

def gateIJ {n : ℕ} (p : UpperPair n) : NativeCircuit n :=
  .pair (.inl p.val.1) (.inl p.val.2) (by simpa using ne_of_lt p.property)

def gateIA {n : ℕ} (p : UpperPair n) : NativeCircuit n :=
  .pair (.inl p.val.1) (.inr ()) (by simp)

def gateJA {n : ℕ} (p : UpperPair n) : NativeCircuit n :=
  .pair (.inl p.val.2) (.inr ()) (by simp)

def cPlus {n : ℕ} (p : UpperPair n) : NativeCircuit n :=
  .seq (.seq (gateIJ p) (gateIA p)) (gateIJ p)

def cMinus {n : ℕ} (p : UpperPair n) : NativeCircuit n :=
  .seq (.seq (gateIJ p) (gateJA p)) (gateIA p)

theorem cPlus_selected {n : ℕ} (p : UpperPair n) (x : Fin n → ℂ) :
    (cPlus p).eval (input x) (.inl p.val.1) =
      -(1 + Complex.I) * x p.val.1 / 4 + (3 + Complex.I) * x p.val.2 / 4 := by
  have hij : p.val.1 ≠ p.val.2 := ne_of_lt p.property
  simpa [cPlus, gateIJ, gateIA, NativeMixerEventConeExclusion.cPlus,
    NativeMixerEventConeExclusion.gate01, NativeMixerEventConeExclusion.gate02,
    NativeMixerEventConeExclusion.input, Circuit.eval, pairGate, pairReplace,
    NativeMixerEventConeExclusion.mixer, NativeMixerEventConeExclusion.Raw,
    CompositeProductControls.RawSign.N, input, hij, Ne.symm hij] using
    NativeMixerEventConeExclusion.cPlus_selected (x p.val.1) (x p.val.2)

theorem cMinus_selected {n : ℕ} (p : UpperPair n) (x : Fin n → ℂ) :
    (cMinus p).eval (input x) (.inl p.val.1) =
      -(1 - Complex.I) * x p.val.1 / 4 + (3 - Complex.I) * x p.val.2 / 4 := by
  have hij : p.val.1 ≠ p.val.2 := ne_of_lt p.property
  simpa [cMinus, gateIJ, gateIA, gateJA, NativeMixerEventConeExclusion.cMinus,
    NativeMixerEventConeExclusion.gate01, NativeMixerEventConeExclusion.gate02,
    NativeMixerEventConeExclusion.gate12, NativeMixerEventConeExclusion.input,
    Circuit.eval, pairGate, pairReplace,
    NativeMixerEventConeExclusion.mixer, NativeMixerEventConeExclusion.Raw,
    CompositeProductControls.RawSign.N, input, hij, Ne.symm hij] using
    NativeMixerEventConeExclusion.cMinus_selected (x p.val.1) (x p.val.2)

theorem native_F_weight {n : ℕ} (p : UpperPair n) (x : Fin n → ℂ) :
    quadratic (F p) x =
      (Complex.normSq ((cPlus p).eval (input x) (.inl p.val.1)) +
        Complex.normSq ((cMinus p).eval (input x) (.inl p.val.1))) / 2 := by
  rw [quadratic_F, NativeMixerEventConeExclusion.compressedWeight,
    cPlus_selected, cMinus_selected,
    NativeMixerEventConeExclusion.cPlus_selected,
    NativeMixerEventConeExclusion.cMinus_selected]

theorem native_H_weight {n : ℕ} (p : UpperPair n) (x : Fin n → ℂ) :
    quadratic (H p) x =
      Complex.normSq ((gateIJ p).eval (input x) (.inl p.val.1)) := by
  rw [quadratic_H]
  simp [gateIJ, Circuit.eval, pairGate, pairReplace,
    NativeMixerEventConeExclusion.mixer, NativeMixerEventConeExclusion.Raw,
    CompositeProductControls.RawSign.N, input]

theorem all_port_resolution {n : ℕ} (c : NativeCircuit n) (x : Fin n → ℂ) :
    ∑ k, Complex.normSq (c.eval (input x) k) = ∑ i, Complex.normSq (x i) := by
  have h := c.preserves_readout Complex.normSq
    NativeMixerEventConeExclusion.mixer_conserves (input x)
  simpa [totalReadout, input, Fintype.sum_sum_type] using h

/-- Event availability replaces the abstract spanning premise; accounting is
still explicitly hypothesized on one coordinate-noncontextual readout. -/
theorem unique_rational_readout {n : ℕ} (D : Set (V n)) (p : V n → ℝ)
    (hzero : (0 : V n) ∈ D) (hpzero : p 0 = 0)
    (hclosed : ∀ x ∈ D, ∀ y ∈ D, (1 / 2 : ℚ) • (x + y) ∈ D)
    (hpres : ∀ x ∈ D, ∀ y ∈ D, p ((1 / 2 : ℚ) • (x + y)) = (p x + p y) / 2)
    (hP : ∀ i, P i ∈ D) (hH : ∀ q, H q ∈ D) (hF : ∀ q, F q ∈ D) :
    ∃! ell : V n →ₗ[ℚ] ℝ, ∀ x ∈ D, ell x = p x :=
  DyadicMixtureLinearization.exists_unique_rational_linear_extension
    D p hzero hpzero hclosed hpres (native_span_eq_top D hP hH hF)

/-! Finite-basis calibration is strictly weaker than global positivity. -/

def pair01 : UpperPair 2 := ⟨(0, 1), by decide⟩
def identity2 : V 2 := P 0 + P 1

def controlReadout : V 2 →ₗ[ℚ] ℚ where
  toFun v := v (.inl 0) + v (.inr (pair01, false)) / 4
  map_add' v w := by simp; ring
  map_smul' q v := by simp; ring

theorem control_values :
    controlReadout (P 0) = 1 ∧ controlReadout (P 1) = 0 ∧
    controlReadout (H pair01) = 1 / 2 ∧ controlReadout (F pair01) = 1 / 16 := by
  norm_num [controlReadout, P, H, F, X, Y, pair01, Pi.single_apply, Sum.inr_ne_inl, Sum.inl_ne_inr]

def controlEvents : Fin 8 → V 2 :=
  ![P 0, P 1, H pair01, F pair01,
    identity2 - P 0, identity2 - P 1, identity2 - H pair01, identity2 - F pair01]

theorem control_calibration (i : Fin 8) :
    0 ≤ controlReadout (controlEvents i) ∧ controlReadout (controlEvents i) ≤ 1 := by
  fin_cases i <;>
    norm_num [controlEvents, controlReadout, identity2, P, H, F, X, Y,
      pair01, Pi.single_apply, Sum.inr_ne_inl, Sum.inl_ne_inr]

/-- Positivity holds on all nonnegative finite combinations of the eight
calibrated events; there is no claim about all native circuit words. -/
theorem control_nonnegative_combinations {ι : Type*} (s : Finset ι)
    (a : ι → ℚ) (event : ι → Fin 8) (ha : ∀ i ∈ s, 0 ≤ a i) :
    0 ≤ controlReadout (∑ i ∈ s, a i • controlEvents (event i)) := by
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (control_calibration _).1

/-- A genuine positive contraction missed by the finite calibration. -/
def negativeControl : V 2 :=
  (1 / 128 : ℚ) • P 0 + (64 / 128 : ℚ) • P 1 - (8 / 128 : ℚ) • X pair01

theorem negativeControl_quadratic (x : Fin 2 → ℂ) :
    quadratic negativeControl x = Complex.normSq (x 0 - 8 * x 1) / 128 := by
  have hs (v w : V 2) : quadratic (v - w) x = quadratic v x - quadratic w x := by
    simp [quadratic, sub_mul, Finset.sum_sub_distrib]
  rw [negativeControl, hs, quadratic_add, quadratic_smul, quadratic_smul,
    quadratic_smul, quadratic_P, quadratic_P, X, quadratic_single]
  norm_num [atom, pair01, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem negativeControl_complement (x : Fin 2 → ℂ) :
    quadratic (identity2 - negativeControl) x =
      (63 * (Complex.normSq (x 0) + Complex.normSq (x 1)) +
        Complex.normSq (8 * x 0 + x 1)) / 128 := by
  have hs : quadratic (identity2 - negativeControl) x =
      quadratic identity2 x - quadratic negativeControl x := by
    simp [quadratic, sub_mul, Finset.sum_sub_distrib]
  rw [hs, identity2, quadratic_add, quadratic_P, quadratic_P,
    negativeControl_quadratic]
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem negativeControl_positive_contraction (x : Fin 2 → ℂ) :
    0 ≤ quadratic negativeControl x ∧
      quadratic negativeControl x ≤ Complex.normSq (x 0) + Complex.normSq (x 1) := by
  constructor
  · rw [negativeControl_quadratic]
    exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)
  · have h : 0 ≤ quadratic (identity2 - negativeControl) x := by
      rw [negativeControl_complement]
      have h0 := Complex.normSq_nonneg (x 0)
      have h1 := Complex.normSq_nonneg (x 1)
      have h2 := Complex.normSq_nonneg (8 * x 0 + x 1)
      positivity
    have hs : quadratic (identity2 - negativeControl) x =
        quadratic identity2 x - quadratic negativeControl x := by
      simp [quadratic, sub_mul, Finset.sum_sub_distrib]
    rw [hs, identity2, quadratic_add, quadratic_P, quadratic_P] at h
    linarith

theorem control_negative : controlReadout negativeControl = -1 / 128 := by
  norm_num [controlReadout, negativeControl, P, X, pair01, Pi.single_apply, Sum.inr_ne_inl, Sum.inl_ne_inr]

end

end IDT.QMClosure.NativeWireEffectSpan
