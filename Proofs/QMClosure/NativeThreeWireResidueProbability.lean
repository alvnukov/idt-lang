import Proofs.QMClosure.NativeThreeWireLocality
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

/-!
# A scalar-residue probability countermodel on native three-wire circuits

The source is the first basis vector. Reduction is defined only for Gaussian
dyadic complex numbers; no map from all complex numbers to characteristic three
is asserted. Probabilities depend on the real part of the scalar residue, with
values zero, one, and one half. The actual native syntax supplies normalization.
This is a mathematical countermodel, not a proposed physical probability law.
No arbitrary-width extension, continuity, physical actualization, or QM closure
is asserted.
-/

namespace IDT.QMClosure.NativeThreeWireResidueProbability

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

open MixerGeneratedProcessWall NativeMixerEventConeExclusion
open scoped BigOperators QuadraticAlgebra

abbrev K := QuadraticAlgebra (ZMod 3) (-1) 0
abbrev RK := Fin 3 → K

instance : Fintype K :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3) (QuadraticAlgebra.equivProd (-1) 0).symm

/-- Integer `x + 3*y` encodes the residue `x + i*y`. -/
def code (n : ℕ) : K := ⟨((n % 3 : ℕ) : ZMod 3), ((n / 3 : ℕ) : ZMod 3)⟩

def normK (z : K) : ZMod 3 := z.re ^ 2 + z.im ^ 2
def Legal (v : RK) : Prop := (∑ i, v i) = 1 ∧ (∑ i, normK (v i)) = 1

instance (v : RK) : Decidable (Legal v) := inferInstanceAs (Decidable (_ ∧ _))

/-- Twice the probability, so finite certification uses only natural numbers. -/
def qUnits (z : K) : ℕ := if z.re = 0 then 0 else if z.re = 1 then 2 else 1
def q (z : K) : ℝ := (qUnits z : ℝ) / 2

/-- Exhaustive kernel reduction over all 729 residue vectors. -/
theorem finite_frame : ∀ v : RK, Legal v → ∑ i, qUnits (v i) = 2 := by
  decide

def pairK (i j : Fin 3) (v : RK) : RK := fun k =>
  if k = i then code 8 * v i + code 5 * v j
  else if k = j then code 5 * v i + code 8 * v j
  else v k

def residueEval : NativeCircuit → RK → RK
  | .identity, v => v
  | .pair i j _, v => pairK i j v
  | .permute e, v => v ∘ e
  | .seq c d, v => residueEval d (residueEval c v)

theorem pairK_legal : ∀ i j : Fin 3, i ≠ j → ∀ v : RK,
    Legal v → Legal (pairK i j v) := by
  decide

theorem residueEval_legal (c : NativeCircuit) (v : RK) (hv : Legal v) :
    Legal (residueEval c v) := by
  induction c generalizing v with
  | identity => exact hv
  | pair i j hij => exact pairK_legal i j hij v hv
  | permute e =>
      constructor
      · simpa [residueEval, Function.comp_def, Equiv.sum_comp] using hv.1
      · change (∑ i, normK (v (e i))) = 1
        rw [e.sum_comp (fun i => normK (v i))]
        exact hv.2
  | seq c d hc hd => exact hd _ (hc _ hv)

/-! ## Functional reduction for the actual complex semantics -/

def gaussianResidue : GaussianInt →+* K where
  toFun g := ⟨(g.re : ZMod 3), (g.im : ZMod 3)⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' g h := by ext <;> simp
  map_mul' g h := by apply QuadraticAlgebra.ext <;> simp <;> ring

theorem two_square : (2 : K) * 2 = 1 := by decide

theorem two_power_cancel (k : ℕ) : (2 : K)^k * (2 : K)^k = 1 := by
  rw [← mul_pow, two_square, one_pow]

/-- A Gaussian dyadic value and its well-defined characteristic-three residue. -/
def Reduces (z : ℂ) (r : K) : Prop :=
  ∃ k : ℕ, ∃ g : GaussianInt,
    z = (g : ℂ) / (2 : ℂ)^k ∧ r = gaussianResidue g * (2 : K)^k

theorem reduces_functional {z : ℂ} {r s : K}
    (hr : Reduces z r) (hs : Reduces z s) : r = s := by
  obtain ⟨k, g, hzg, rfl⟩ := hr
  obtain ⟨l, h, hzh, rfl⟩ := hs
  have hc : (g : ℂ) * (2 : ℂ)^l = (h : ℂ) * (2 : ℂ)^k :=
    (div_eq_div_iff (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by norm_num))).mp (hzg.symm.trans hzh)
  have hg : g * (2 : GaussianInt)^l = h * (2 : GaussianInt)^k := by
    apply GaussianInt.toComplex_injective
    simpa only [map_mul, map_pow, map_ofNat] using hc
  have hf := congrArg gaussianResidue hg
  simp only [map_mul, map_pow, map_ofNat] at hf
  calc
    gaussianResidue g * (2 : K)^k =
        gaussianResidue g * (2 : K)^k * ((2 : K)^l * (2 : K)^l) := by
          rw [two_power_cancel]; ring
    _ = (gaussianResidue g * (2 : K)^l) * ((2 : K)^k * (2 : K)^l) := by ring
    _ = (gaussianResidue h * (2 : K)^k) * ((2 : K)^k * (2 : K)^l) := by rw [hf]
    _ = gaussianResidue h * (2 : K)^l * ((2 : K)^k * (2 : K)^k) := by ring
    _ = gaussianResidue h * (2 : K)^l := by rw [two_power_cancel]; ring

theorem reduces_gaussian (g : GaussianInt) : Reduces (g : ℂ) (gaussianResidue g) := by
  exact ⟨0, g, by simp, by simp⟩

theorem reduces_zero : Reduces (0 : ℂ) (0 : K) := by
  simpa using reduces_gaussian 0

theorem reduces_one : Reduces (1 : ℂ) (1 : K) := by
  simpa using reduces_gaussian 1

theorem reduces_add {z w : ℂ} {r s : K}
    (hz : Reduces z r) (hw : Reduces w s) : Reduces (z + w) (r + s) := by
  obtain ⟨k, g, rfl, rfl⟩ := hz
  obtain ⟨l, h, rfl, rfl⟩ := hw
  refine ⟨k + l, g * (2 : GaussianInt)^l + h * (2 : GaussianInt)^k, ?_, ?_⟩
  · simp only [map_add, map_mul, map_pow, map_ofNat, pow_add]
    field_simp
  · simp only [map_add, map_mul, map_pow, map_ofNat, pow_add]
    symm
    calc
      (gaussianResidue g * (2 : K)^l + gaussianResidue h * (2 : K)^k) *
          ((2 : K)^k * (2 : K)^l) =
          gaussianResidue g * (2 : K)^k * ((2 : K)^l * (2 : K)^l) +
          gaussianResidue h * (2 : K)^l * ((2 : K)^k * (2 : K)^k) := by ring
      _ = _ := by rw [two_power_cancel, two_power_cancel]; ring

theorem reduces_mul {z w : ℂ} {r s : K}
    (hz : Reduces z r) (hw : Reduces w s) : Reduces (z * w) (r * s) := by
  obtain ⟨k, g, rfl, rfl⟩ := hz
  obtain ⟨l, h, rfl, rfl⟩ := hw
  refine ⟨k + l, g * h, ?_, ?_⟩
  · simp only [map_mul, pow_add]
    field_simp
  · simp only [map_mul, pow_add]
    ring

theorem reduces_a : Reduces NativeThreeWireLocality.a (code 8) := by
  refine ⟨1, ⟨1, 1⟩, ?_, ?_⟩
  · simp [NativeThreeWireLocality.a, NativeMixerInfiniteOrder.a, GaussianInt.toComplex_def]
  · decide

theorem reduces_b : Reduces NativeThreeWireLocality.b (code 5) := by
  refine ⟨1, ⟨1, -1⟩, ?_, ?_⟩
  · simp [NativeThreeWireLocality.b, NativeMixerInfiniteOrder.b, GaussianInt.toComplex_def, sub_eq_add_neg]
  · decide

theorem mixer_linear (z w : ℂ) :
    mixer (z, w) =
      (NativeThreeWireLocality.a * z + NativeThreeWireLocality.b * w,
       NativeThreeWireLocality.b * z + NativeThreeWireLocality.a * w) := by
  apply Prod.ext <;> apply Complex.ext <;>
    norm_num [mixer, Raw, CompositeProductControls.RawSign.N,
      CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im,
      NativeThreeWireLocality.a, NativeThreeWireLocality.b,
      NativeMixerInfiniteOrder.a, NativeMixerInfiniteOrder.b,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

theorem pair_reduces (i j : Fin 3) (hij : i ≠ j)
    (v : Fin 3 → ℂ) (r : RK) (h : ∀ k, Reduces (v k) (r k)) :
    ∀ k, Reduces ((Circuit.pair i j hij : NativeCircuit).eval v k) (pairK i j r k) := by
  intro k
  change Reduces (pairReplace mixer i j v k) (pairK i j r k)
  simp only [pairReplace, pairK, mixer_linear]
  split_ifs
  · exact reduces_add (reduces_mul reduces_a (h i)) (reduces_mul reduces_b (h j))
  · exact reduces_add (reduces_mul reduces_b (h i)) (reduces_mul reduces_a (h j))
  · exact h k

/-- Every native constructor respects the reduction relation. -/
theorem circuit_reduces (c : NativeCircuit) (v : Fin 3 → ℂ) (r : RK)
    (h : ∀ i, Reduces (v i) (r i)) :
    ∀ i, Reduces (c.eval v i) (residueEval c r i) := by
  induction c generalizing v r with
  | identity => exact h
  | pair i j hij => exact pair_reduces i j hij v r h
  | permute e => exact fun i => h (e i)
  | seq c d hc hd => exact hd _ _ (hc _ _ h)

/-! ## Normalized actual-circuit probabilities -/

def source : Fin 3 → ℂ := Pi.single 0 1
def sourceK : RK := Pi.single 0 1
def preparedResidue (c : NativeCircuit) : RK := residueEval c sourceK
def probability (c : NativeCircuit) (i : Fin 3) : ℝ := q (preparedResidue c i)

theorem source_reduces (i : Fin 3) : Reduces (source i) (sourceK i) := by
  simp only [source, sourceK, Pi.single_apply]
  split_ifs
  · exact reduces_one
  · exact reduces_zero

theorem prepared_reduces (c : NativeCircuit) (i : Fin 3) :
    Reduces (c.eval source i) (preparedResidue c i) :=
  circuit_reduces c source sourceK source_reduces i

theorem probability_nonnegative (c : NativeCircuit) (i : Fin 3) :
    0 ≤ probability c i := by
  exact div_nonneg (Nat.cast_nonneg _) (by norm_num)

theorem probability_normalized (c : NativeCircuit) : ∑ i, probability c i = 1 := by
  have hs : Legal sourceK := by decide
  have h := finite_frame (preparedResidue c) (residueEval_legal c sourceK hs)
  have hr : (∑ i, (qUnits (preparedResidue c i) : ℝ)) = 2 := by exact_mod_cast h
  simp [probability, q, ← Finset.sum_div, hr]

theorem probability_identity (i : Fin 3) :
    probability .identity i = if i = 0 then 1 else 0 := by
  fin_cases i <;> norm_num [probability, q, qUnits, preparedResidue, residueEval,
    sourceK, Pi.single_apply]

/-- Equality of prepared complex states alone suffices. -/
theorem probability_prepared_eq {c d : NativeCircuit}
    (he : c.eval source = d.eval source) : probability c = probability d := by
  funext i
  have hc := prepared_reduces c i
  rw [he] at hc
  have hr := reduces_functional hc (prepared_reduces d i)
  exact congrArg q hr

theorem probability_complete_eval {c d : NativeCircuit}
    (he : ∀ x, c.eval x = d.eval x) : probability c = probability d :=
  probability_prepared_eq (he source)

theorem probability_output_permutation (c : NativeCircuit)
    (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    probability (.seq c (.permute e)) i = probability c (e i) := rfl

theorem probability_spectator_pair (c : NativeCircuit)
    (i j k : Fin 3) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    probability (.seq c (.pair i j hij)) k = probability c k := by
  simp [probability, preparedResidue, residueEval, pairK, hki, hkj]

theorem probability_spectator (c : NativeCircuit) :
    probability (.seq c gate12) 0 = probability c 0 :=
  probability_spectator_pair c 1 2 0 (by decide) (by decide) (by decide)

/-- Any prefix which fixes the prepared source is invisible to this law. -/
theorem probability_source_fixing_prefix (c d : NativeCircuit)
    (hd : d.eval source = source) : probability (.seq d c) = probability c := by
  apply probability_prepared_eq
  change c.eval (d.eval source) = c.eval source
  rw [hd]

def witness : NativeCircuit := .seq gate01 gate12

theorem witness_probability : probability witness 1 = 1 / 2 := by
  have h : qUnits (preparedResidue witness 1) = 1 := by decide
  simp [probability, q, h]

theorem witness_born : Complex.normSq (witness.eval source 1) = 1 / 4 := by
  norm_num [witness, source, gate01, gate12, Circuit.eval, pairGate, pairReplace,
    Pi.single_apply, mixer, Raw, CompositeProductControls.RawSign.N,
    CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im,
    Complex.normSq_apply, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide]

theorem probability_not_born :
    probability witness 1 ≠ Complex.normSq (witness.eval source 1) := by
  rw [witness_probability, witness_born]
  norm_num

theorem selected_readout_premises :
    NativeThreeWireLocality.ReadoutPremises (fun c => probability c 0) where
  complete_eval _ _ h := congrFun (probability_complete_eval h) 0
  spectator_local := probability_spectator

theorem probability_full_selected_profile (c d : NativeCircuit)
    (h : ∀ x : Fin 3 → ℂ,
      Complex.normSq (c.eval x 0) = Complex.normSq (d.eval x 0)) :
    probability c 0 = probability d 0 :=
  NativeThreeWireLocality.full_selected_profile_readout
    selected_readout_premises c d h


/-- Even equality of the single selected complex amplitude suffices. -/
theorem probability_amplitude_eq {c d : NativeCircuit} (i j : Fin 3)
    (he : c.eval source i = d.eval source j) : probability c i = probability d j := by
  have hc := prepared_reduces c i
  rw [he] at hc
  exact congrArg q (reduces_functional hc (prepared_reduces d j))

/-- Calibration holds for every circuit which prepares a literal basis state. -/
theorem probability_basis_state (c : NativeCircuit) (j i : Fin 3)
    (hc : c.eval source = Pi.single j (1 : ℂ)) :
    probability c i = if i = j then 1 else 0 := by
  have hr : Reduces (c.eval source i) ((Pi.single j (1 : K) : RK) i) := by
    rw [hc]
    simp only [Pi.single_apply]
    split_ifs
    · exact reduces_one
    · exact reduces_zero
  have he := reduces_functional (prepared_reduces c i) hr
  simp only [probability, he, q, qUnits, Pi.single_apply]
  split_ifs <;> norm_num at *

/-! ## An exact obstruction to two-mixture profile sufficiency

The four events need not occur as simultaneous outputs of one circuit.
Their sums of squared-amplitude profiles agree on every complex input.
Their fair-mixture probabilities under this normalized law nevertheless differ.
This construction is restricted to width three; wider extensions are not assumed.
-/

def eventA : NativeCircuit := gate02
def eventB : NativeCircuit := .seq (.seq gate01 gate12) gate01
def eventC : NativeCircuit := gate12
def eventD : NativeCircuit := .seq (.seq gate01 gate12) gate02

theorem equal_two_mixture_profiles (x : Fin 3 → ℂ) :
    (Complex.normSq (eventA.eval x 2) + Complex.normSq (eventB.eval x 0)) / 2 =
      (Complex.normSq (eventC.eval x 1) + Complex.normSq (eventD.eval x 2)) / 2 := by
  norm_num [eventA, eventB, eventC, eventD, gate01, gate02, gate12,
    Circuit.eval, pairGate, pairReplace, mixer, Raw,
    CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n_re,
    CompositeProductControls.RawSign.n_im, Complex.normSq_apply,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide]
  ring

theorem eventA_probability : probability eventA 2 = 1 / 2 := by
  have h : qUnits (preparedResidue eventA 2) = 1 := by decide
  simp [probability, q, h]

theorem eventB_probability : probability eventB 0 = 1 := by
  have h : qUnits (preparedResidue eventB 0) = 2 := by decide
  simp [probability, q, h]

theorem eventC_probability : probability eventC 1 = 0 := by
  have h : qUnits (preparedResidue eventC 1) = 0 := by decide
  simp [probability, q, h]

theorem eventD_probability : probability eventD 2 = 0 := by
  have h : qUnits (preparedResidue eventD 2) = 0 := by decide
  simp [probability, q, h]

theorem unequal_two_mixture_probabilities :
    (probability eventA 2 + probability eventB 0) / 2 ≠
      (probability eventC 1 + probability eventD 2) / 2 := by
  rw [eventA_probability, eventB_probability, eventC_probability, eventD_probability]
  norm_num

/-- These circuit-level conditions do not force mixture-profile descent. -/
theorem two_mixture_profile_sufficiency_fails :
    ¬ (∀ (a b c d : NativeCircuit) (i j k l : Fin 3),
      (∀ x : Fin 3 → ℂ,
        (Complex.normSq (a.eval x i) + Complex.normSq (b.eval x j)) / 2 =
        (Complex.normSq (c.eval x k) + Complex.normSq (d.eval x l)) / 2) →
      (probability a i + probability b j) / 2 =
        (probability c k + probability d l) / 2) := by
  intro h
  exact unequal_two_mixture_probabilities
    (h eventA eventB eventC eventD 2 0 1 2 equal_two_mixture_profiles)

end

end IDT.QMClosure.NativeThreeWireResidueProbability
