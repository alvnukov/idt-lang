import Proofs.QMClosure.NativeScalarAmplitudeSufficiency
import Proofs.QMClosure.GaussianIntegerQuadraticSelection
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Gaussian numerator responses from actual native events

All events live in the canonical doubling tower above one fixed finite wire type
and marked source. Cross-level comparisons use literal vacuum embeddings only.
Numerator witnesses are built from actual circuits independently of any choice
of a probability law. Their weighted probability is independent of both the
witness and its damping exponent under the supplied family contract.
No arbitrary type relabel law, probability continuity, or physical availability
is asserted. The separate quadratic consistency witness is not used here.
-/

namespace IDT.QMClosure.NativeGaussianResponse

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

open NativeSignedAccounting
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open NativeCoherentBranchDilation NativeScalarAmplitudeSufficiency
open scoped BigOperators

abbrev G := GaussianInt
abbrev ii := GaussianIntegerQuadraticSelection.ii

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def Tower (ι : Type) : ℕ → Type
  | 0 => ι
  | n + 1 => Tower ι n ⊕ Tower ι n

instance towerFintype (n : ℕ) : Fintype (Tower ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype ι)
  | succ n ih => letI := ih; exact inferInstanceAs (Fintype (Tower ι n ⊕ Tower ι n))

instance towerDecidableEq (n : ℕ) : DecidableEq (Tower ι n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq ι)
  | succ n ih => letI := ih; exact inferInstanceAs (DecidableEq (Tower ι n ⊕ Tower ι n))

def sourceAt (s : ι) : (n : ℕ) → Tower ι n
  | 0 => s
  | n + 1 => .inl (sourceAt s n)

structure Event (ι : Type) where
  level : ℕ
  circuit : Native (Tower ι level)
  port : Tower ι level

def amplitude (s : ι) (e : Event ι) : ℂ :=
  e.circuit.eval (source (sourceAt s e.level)) e.port

def probability (L : SignedHalvingLaw) (s : ι) (e : Event ι) : ℝ :=
  L.prob (sourceAt s e.level) e.circuit e.port

def baseEvent (c : Native ι) (i : ι) : Event ι := ⟨0, c, i⟩

omit [Fintype ι] in
theorem baseEvent_amplitude (s : ι) (c : Native ι) (i : ι) :
    amplitude s (baseEvent c i) = c.eval (source s) i := rfl

theorem baseEvent_probability (L : SignedHalvingLaw) (s : ι) (c : Native ι) (i : ι) :
    probability L s (baseEvent c i) = L.prob s c i := rfl

def padEvent (e : Event ι) : Event ι :=
  ⟨e.level + 1, padCircuit (Tower ι e.level) e.circuit, .inl e.port⟩

theorem padEvent_amplitude (s : ι) (e : Event ι) :
    amplitude s (padEvent e) = amplitude s e := by
  rcases e with ⟨n, c, i⟩
  exact congrFun (pad_prepared (κ := Tower ι n) (sourceAt s n) c) (Sum.inl i)

theorem padEvent_probability (L : SignedHalvingLaw) (s : ι) (e : Event ι) :
    probability L s (padEvent e) = probability L s e := by
  rcases e with ⟨n, c, i⟩
  exact L.vacuum (sourceAt s n) c i

/-- Padding witnesses are independent of any choice of probability law. -/
theorem exists_padding (s : ι) (e : Event ι) (n : ℕ) (h : e.level ≤ n) :
    ∃ f : Event ι, f.level = n ∧ amplitude s f = amplitude s e ∧
      ∀ L : SignedHalvingLaw, probability L s f = probability L s e := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨e, rfl, rfl, fun _ => rfl⟩
  | succ n hn ih =>
      obtain ⟨f, hf, ha, hp⟩ := ih
      refine ⟨padEvent f, ?_, (padEvent_amplitude s f).trans ha, ?_⟩
      · simp [padEvent, hf]
      · intro L
        exact (padEvent_probability L s f).trans (hp L)

theorem exists_common_level (s : ι) (e f : Event ι) :
    ∃ n : ℕ, ∃ c d : Native (Tower ι n), ∃ i j : Tower ι n,
      c.eval (source (sourceAt s n)) i = amplitude s e ∧
      d.eval (source (sourceAt s n)) j = amplitude s f ∧
      (∀ L : SignedHalvingLaw, L.prob (sourceAt s n) c i = probability L s e) ∧
      (∀ L : SignedHalvingLaw, L.prob (sourceAt s n) d j = probability L s f) := by
  let n := max e.level f.level
  obtain ⟨e', he, hea, hep⟩ := exists_padding s e n (Nat.le_max_left _ _)
  obtain ⟨f', hf, hfa, hfp⟩ := exists_padding s f n (Nat.le_max_right _ _)
  rcases e' with ⟨en, ec, ei⟩
  rcases f' with ⟨fn, fc, fi⟩
  change en = n at he
  change fn = n at hf
  subst en
  subst fn
  exact ⟨n, ec, fc, ei, fi, hea, hfa, hep, hfp⟩

/-- Cross-level comparison uses actual padding followed by the same-source theorem. -/
theorem event_amplitude_sufficiency (L : SignedHalvingLaw) (s : ι) (e f : Event ι)
    (h : amplitude s e = amplitude s f) : probability L s e = probability L s f := by
  obtain ⟨n, c, d, i, j, hc, hd, hpc, hpd⟩ := exists_common_level s e f
  calc
    probability L s e = L.prob (sourceAt s n) c i := (hpc L).symm
    _ = L.prob (sourceAt s n) d j :=
      same_source_amplitude_sufficiency L (sourceAt s n) c d i j
        (hc.trans (h.trans hd.symm))
    _ = probability L s f := hpd L

theorem a_mul_b : NativeAttenuationCircuit.a * NativeAttenuationCircuit.b = (1 / 2 : ℂ) := by
  apply Complex.ext <;> norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

def halfEvent (e : Event ι) : Event ι :=
  ⟨e.level + 2, duplicate (duplicate e.circuit), .inl (.inr e.port)⟩

def rotateHalfEvent (e : Event ι) : Event ι :=
  ⟨e.level + 2, duplicate (duplicate e.circuit), .inl (.inl e.port)⟩

theorem halfEvent_amplitude (s : ι) (e : Event ι) :
    amplitude s (halfEvent e) = amplitude s e / 2 := by
  rcases e with ⟨n, c, i⟩
  change (duplicate (duplicate c)).eval (source (.inl (.inl (sourceAt s n))))
    (.inl (.inr i)) = _
  rw [(duplicate_amplitudes (.inl (sourceAt s n)) (duplicate c) (.inr i)).1,
    (duplicate_amplitudes (sourceAt s n) c i).2, ← mul_assoc, a_mul_b]
  dsimp [amplitude]
  ring

theorem halfEvent_probability (L : SignedHalvingLaw) (s : ι) (e : Event ι) :
    probability L s (halfEvent e) = probability L s e / 4 := by
  rcases e with ⟨n, c, i⟩
  change L.prob (.inl (.inl (sourceAt s n))) (duplicate (duplicate c))
    (.inl (.inr i)) = _
  rw [(duplicate_probabilities L (.inl (sourceAt s n)) (duplicate c) (.inr i)).1,
    (duplicate_probabilities L (sourceAt s n) c i).2]
  dsimp [probability]
  ring

theorem rotateHalfEvent_amplitude (s : ι) (e : Event ι) :
    amplitude s (rotateHalfEvent e) = Complex.I * amplitude s e / 2 := by
  rcases e with ⟨n, c, i⟩
  change (duplicate (duplicate c)).eval (source (.inl (.inl (sourceAt s n))))
    (.inl (.inl i)) = _
  rw [(duplicate_amplitudes (.inl (sourceAt s n)) (duplicate c) (.inl i)).1,
    (duplicate_amplitudes (sourceAt s n) c i).1, ← mul_assoc,
    ← pow_two, NativeAttenuationCircuit.a_square]
  dsimp [amplitude]
  ring

theorem rotateHalfEvent_probability (L : SignedHalvingLaw) (s : ι) (e : Event ι) :
    probability L s (rotateHalfEvent e) = probability L s e / 4 := by
  rcases e with ⟨n, c, i⟩
  change L.prob (.inl (.inl (sourceAt s n))) (duplicate (duplicate c))
    (.inl (.inl i)) = _
  rw [(duplicate_probabilities L (.inl (sourceAt s n)) (duplicate c) (.inl i)).1,
    (duplicate_probabilities L (sourceAt s n) c i).1]
  dsimp [probability]
  ring

theorem exists_damping (s : ι) (e : Event ι) (k : ℕ) :
    ∃ f : Event ι, amplitude s f = amplitude s e / (2 : ℂ)^k ∧
      ∀ L : SignedHalvingLaw, probability L s f = probability L s e / (4 : ℝ)^k := by
  induction k with
  | zero => exact ⟨e, by simp, fun _ => by simp⟩
  | succ k ih =>
      obtain ⟨f, ha, hp⟩ := ih
      refine ⟨halfEvent f, ?_, ?_⟩
      · rw [halfEvent_amplitude, ha, div_div, pow_succ]
      · intro L
        rw [halfEvent_probability, hp, div_div, pow_succ]

def sumDifferenceCircuit {α : Type} [Fintype α] [DecidableEq α]
    (c d : Native α) (i j : α) : Native (α ⊕ α) :=
  .seq (dilation c d) (.pair (.inl i) (.inr j) (by simp))

theorem sumDifference_amplitudes {α : Type} [Fintype α] [DecidableEq α]
    (s : α) (c d : Native α) (i j : α) :
    (sumDifferenceCircuit c d i j).eval (source (.inl s)) (.inl i) =
      Complex.I * (c.eval (source s) i - d.eval (source s) j) / 2 ∧
    (sumDifferenceCircuit c d i j).eval (source (.inl s)) (.inr j) =
      (c.eval (source s) i + d.eval (source s) j) / 2 := by
  constructor <;>
    simp [sumDifferenceCircuit, Circuit.eval, pairGate, pairReplace,
      NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd,
      dilation_amplitude_left, dilation_amplitude_right]
  all_goals
    apply Complex.ext <;>
      norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

theorem sumDifference_probabilities {α : Type} [Fintype α] [DecidableEq α]
    (L : SignedHalvingLaw) (s : α) (c d : Native α) (i j : α) :
    L.prob (.inl s) (sumDifferenceCircuit c d i j) (.inl i) +
      L.prob (.inl s) (sumDifferenceCircuit c d i j) (.inr j) =
      (L.prob s c i + L.prob s d j) / 2 := by
  rw [sumDifferenceCircuit, NativeSignedAccounting.pair_probability_sum L.toSignedLaw,
    dilation_probability_left, dilation_probability_right]
  ring

/-- Two selected outputs of one literal continuation, with retained ancillary wires. -/
theorem exists_sum_difference (s : ι) (e f : Event ι) :
    ∃ u v : Event ι,
      amplitude s u = (amplitude s e + amplitude s f) / 2 ∧
      amplitude s v = Complex.I * (amplitude s e - amplitude s f) / 2 ∧
      ∀ L : SignedHalvingLaw, probability L s u + probability L s v =
        (probability L s e + probability L s f) / 2 := by
  obtain ⟨n, c, d, i, j, hc, hd, hpc, hpd⟩ := exists_common_level s e f
  let t := sumDifferenceCircuit c d i j
  refine ⟨⟨n + 1, t, .inr j⟩, ⟨n + 1, t, .inl i⟩, ?_, ?_, ?_⟩
  · simpa [amplitude, sourceAt, t, hc, hd] using
      (sumDifference_amplitudes (sourceAt s n) c d i j).2
  · simpa [amplitude, sourceAt, t, hc, hd] using
      (sumDifference_amplitudes (sourceAt s n) c d i j).1
  · intro L
    simpa [probability, sourceAt, t, hpc L, hpd L, add_comm] using
      sumDifference_probabilities L (sourceAt s n) c d i j

/-! ## Actual Gaussian numerator witnesses -/

structure Witness (s : ι) (g : G) where
  event : Event ι
  exponent : ℕ
  representation : amplitude s event = (g : ℂ) / (2 : ℂ)^exponent

def weighted (L : SignedHalvingLaw) {s : ι} {g : G} (w : Witness s g) : ℝ :=
  (4 : ℝ)^w.exponent * probability L s w.event

theorem weighted_independent (L : SignedHalvingLaw) (s : ι) (g : G) (u v : Witness s g) :
    weighted L u = weighted L v := by
  obtain ⟨f, hfa, hfp⟩ := exists_damping s u.event v.exponent
  obtain ⟨h, hha, hhp⟩ := exists_damping s v.event u.exponent
  have he : amplitude s f = amplitude s h := by
    rw [hfa, hha, u.representation, v.representation, div_div, div_div, mul_comm]
  have hp := event_amplitude_sufficiency L s f h he
  rw [hfp L, hhp L] at hp
  have hx := (div_eq_div_iff (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0))
    (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0))).mp hp
  simpa [weighted, mul_comm] using hx

def zeroWitness (s : ι) : Witness s 0 where
  event := ⟨1, padCircuit ι (.identity : Native ι), .inr s⟩
  exponent := 0
  representation := by
    have hz := congrFun (pad_prepared (κ := ι) s (.identity : Native ι)) (Sum.inr s)
    simpa only [amplitude, sourceAt, padState, map_zero, pow_zero, zero_div] using hz

def oneWitness (s : ι) : Witness s 1 where
  event := ⟨0, .identity, s⟩
  exponent := 0
  representation := by
    simp [amplitude, sourceAt, Circuit.eval, source, single]

@[simp] theorem cast_ii : (ii : ℂ) = Complex.I := by
  simp [ii, GaussianIntegerQuadraticSelection.ii, GaussianInt.toComplex_def]

theorem ii_mul_ii : (ii : G) * ii = -1 := by decide

def rotateWitness {s : ι} {g : G} (w : Witness s g) : Witness s (ii * g) where
  event := rotateHalfEvent w.event
  exponent := w.exponent + 1
  representation := by
    rw [rotateHalfEvent_amplitude, w.representation]
    simp only [map_mul, cast_ii, pow_succ]
    field_simp

theorem weighted_rotate (L : SignedHalvingLaw) {s : ι} {g : G} (w : Witness s g) :
    weighted L (rotateWitness w) = weighted L w := by
  change (4 : ℝ)^(w.exponent + 1) * probability L s (rotateHalfEvent w.event) = _
  rw [rotateHalfEvent_probability, pow_succ]
  dsimp [weighted]
  ring

/-- The numerator sum and rotated difference are simultaneous outputs of one word.
Their existence and the universal probability certificate do not choose a law. -/
theorem exists_witness_sum_difference (s : ι) (g h : G)
    (u : Witness s g) (v : Witness s h) :
    ∃ wsum : Witness s (g + h), ∃ wdiff : Witness s (ii * (g - h)),
      ∀ L : SignedHalvingLaw, weighted L wsum + weighted L wdiff =
        2 * (weighted L u + weighted L v) := by
  obtain ⟨f, hfa, hfp⟩ := exists_damping s u.event v.exponent
  obtain ⟨t, hta, htp⟩ := exists_damping s v.event u.exponent
  let k := u.exponent + v.exponent
  have hf : amplitude s f = (g : ℂ) / (2 : ℂ)^k := by
    rw [hfa, u.representation, div_div]
    simp only [k, pow_add]
  have ht : amplitude s t = (h : ℂ) / (2 : ℂ)^k := by
    rw [hta, v.representation, div_div]
    simp only [k, pow_add, mul_comm]
  obtain ⟨es, ed, hsa, hda, hp⟩ := exists_sum_difference s f t
  let ws : Witness s (g + h) := {
    event := es
    exponent := k + 1
    representation := by
      rw [hsa, hf, ht]
      simp only [map_add, pow_succ]
      field_simp }
  let wd : Witness s (ii * (g - h)) := {
    event := ed
    exponent := k + 1
    representation := by
      rw [hda, hf, ht]
      simp only [map_mul, map_sub, cast_ii, pow_succ]
      field_simp }
  refine ⟨ws, wd, ?_⟩
  intro L
  change (4 : ℝ)^(k + 1) * probability L s es +
      (4 : ℝ)^(k + 1) * probability L s ed = _
  calc
    _ = (4 : ℝ)^(k + 1) * (probability L s es + probability L s ed) := by ring
    _ = (4 : ℝ)^(k + 1) * ((probability L s f + probability L s t) / 2) := by rw [hp L]
    _ = 2 * (weighted L u + weighted L v) := by
      rw [hfp L, htp L]
      simp only [weighted, k, pow_succ, pow_add]
      field_simp
      ring

def negWitness {s : ι} {g : G} (w : Witness s g) : Witness s (-g) := by
  have he : ii * (ii * g) = -g := by rw [← mul_assoc, ii_mul_ii, neg_one_mul]
  have v := rotateWitness (rotateWitness w)
  rw [he] at v
  exact v

def realizableSubgroup (s : ι) : AddSubgroup G where
  carrier := fun g => Nonempty (Witness s g)
  zero_mem' := ⟨zeroWitness s⟩
  add_mem' := by
    rintro g h ⟨u⟩ ⟨v⟩
    obtain ⟨ws, _, _⟩ := exists_witness_sum_difference s g h u v
    exact ⟨ws⟩
  neg_mem' := by
    rintro g ⟨u⟩
    exact ⟨negWitness u⟩

theorem all_numerators_realizable (s : ι) (g : G) : Nonempty (Witness s g) := by
  let H := realizableSubgroup s
  have h1 : (1 : G) ∈ H := ⟨oneWitness s⟩
  have hi : ii ∈ H := by
    have w := rotateWitness (oneWitness s)
    simpa using (show Nonempty (Witness s (ii * 1)) from ⟨w⟩)
  have hm := H.add_mem (H.zsmul_mem h1 g.re) (H.zsmul_mem hi g.im)
  have he : g.re • (1 : G) + g.im • ii = g := by
    ext <;> simp [ii, GaussianIntegerQuadraticSelection.ii, zsmul_eq_mul]
  rw [he] at hm
  exact hm

def chosenWitness (s : ι) (g : G) : Witness s g :=
  Classical.choice (all_numerators_realizable s g)

def response (L : SignedHalvingLaw) (s : ι) (g : G) : ℝ := weighted L (chosenWitness s g)

theorem response_eq_witness (L : SignedHalvingLaw) (s : ι) (g : G) (w : Witness s g) :
    response L s g = weighted L w := weighted_independent L s g (chosenWitness s g) w

/-- A direct interface for a Gaussian dyadic witness of an original native output. -/
theorem response_native_output (L : SignedHalvingLaw) (s : ι) (c : Native ι) (i : ι)
    (g : G) (k : ℕ) (h : c.eval (source s) i = (g : ℂ) / (2 : ℂ)^k) :
    response L s g = (4 : ℝ)^k * L.prob s c i := by
  let w : Witness s g := ⟨baseEvent c i, k, (baseEvent_amplitude s c i).trans h⟩
  exact response_eq_witness L s g w

theorem response_nonnegative (L : Law) (s : ι) (g : G) : 0 ≤ response L s g := by
  unfold response weighted probability
  exact mul_nonneg (by positivity) (L.nonnegative _ _ _)

theorem response_zero (L : SignedHalvingLaw) (s : ι) : response L s 0 = 0 := by
  rw [response_eq_witness L s 0 (zeroWitness s)]
  have ha : amplitude s (zeroWitness s).event = 0 := by
    simpa [zeroWitness] using (zeroWitness s).representation
  have hp := NativeSignedAccounting.zero_amplitude_probability_zero L.toSignedLaw
    (sourceAt s (zeroWitness s).event.level) (zeroWitness s).event.circuit
    (zeroWitness s).event.port ha
  simpa [weighted, probability, zeroWitness] using hp

theorem response_one (L : SignedHalvingLaw) (s : ι) : response L s 1 = 1 := by
  rw [response_eq_witness L s 1 (oneWitness s)]
  have hp := NativeSignedAccounting.basis_calibration L.toSignedLaw
    s (.identity : Native ι) s (by rfl) s
  simpa [weighted, probability, oneWitness, sourceAt] using hp

theorem response_rotate (L : SignedHalvingLaw) (s : ι) (g : G) :
    response L s (ii * g) = response L s g := by
  rw [response_eq_witness L s (ii * g) (rotateWitness (chosenWitness s g)), weighted_rotate]
  rfl

theorem response_parallelogram (L : SignedHalvingLaw) (s : ι) :
    GaussianIntegerQuadraticSelection.Parallelogram (response L s) := by
  intro g h
  obtain ⟨ws, wd, hp⟩ := exists_witness_sum_difference s g h
    (chosenWitness s g) (chosenWitness s h)
  have hv := hp L
  rw [← response_eq_witness L s (g + h) ws,
    ← response_eq_witness L s (ii * (g - h)) wd] at hv
  change response L s (g + h) + response L s (ii * (g - h)) =
    2 * (response L s g + response L s h) at hv
  rw [response_rotate] at hv
  simpa [mul_add] using hv

end

end IDT.QMClosure.NativeGaussianResponse
