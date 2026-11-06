import Proofs.QMClosure.NativeAttenuationCircuit

/-!
# Conditional probability transfer for a certified native event grammar

The structural profile is computed independently from the rational effect:
attenuation leaves evaluate literal retained-ancilla circuits, and fair mixtures
average profiles. The total event sums all data input weights; it is not one
selected output port. Mathematical quantification over complex inputs does not
assert that every such input is physically preparable.

Probability accounting and full-profile sufficiency, including mixture events,
are supplied laws. The theorem transfers these laws to the committed rational
attenuation selection result. It does not derive profile sufficiency, physical
availability, fair-coin statistics, arbitrary-circuit effect extraction, arbitrary
preparation selection, mixed-state reconstruction, or full QM.
-/

namespace IDT.QMClosure.NativeEventProbabilityBridge

noncomputable section
open scoped BigOperators
open NativeWireEffectSpan NativeAttenuationReadout

/-- A total factor exists exactly when the value is constant on every fibre.
The zero structure supplies the arbitrary extension outside the image. -/
theorem factorization_iff_fibre_constancy {S A R : Type*} [Zero R]
    (e : S → A) (pi : S → R) :
    (∃ q : A → R, ∀ s, q (e s) = pi s) ↔
      (∀ s t, e s = e t → pi s = pi t) := by
  classical
  constructor
  · rintro ⟨q, hq⟩ s t h
    rw [← hq s, ← hq t, h]
  · intro h
    let q : A → R := fun a =>
      if ha : ∃ s, e s = a then pi (Classical.choose ha) else 0
    refine ⟨q, ?_⟩
    intro s
    dsimp [q]
    rw [dif_pos (show ∃ t, e t = e s from ⟨s, rfl⟩)]
    exact h _ s (Classical.choose_spec (show ∃ t, e t = e s from ⟨s, rfl⟩))

/-- Factor uniqueness is asserted only on the image, never on arbitrary inputs. -/
theorem factors_agree_on_range {S A R : Type*} (e : S → A) (pi : S → R)
    (q r : A → R) (hq : ∀ s, q (e s) = pi s) (hr : ∀ s, r (e s) = pi s) :
    ∀ a ∈ Set.range e, q a = r a := by
  rintro a ⟨s, rfl⟩
  exact (hq s).trans (hr s).symm

/-- Exactly the certified leaves used by attenuation selection, closed under
binary fair mixing. This is not the grammar of arbitrary native circuits. -/
inductive Event (n : ℕ) where
  | zero : Event n
  | total : Event n
  | basis : Fin n → Event n
  | attenuation0 : UpperPair n → ℕ → Event n
  | attenuation2 : UpperPair n → ℕ → Event n
  | attenuation4 : UpperPair n → ℕ → Event n
  | attenuation6 : UpperPair n → ℕ → Event n
  | fairMix : Event n → Event n → Event n

def effect {n : ℕ} : Event n → V n
  | .zero => 0
  | .total => identity n
  | .basis i => P i
  | .attenuation0 q m => E0 q m
  | .attenuation2 q m => E2 q m
  | .attenuation4 q m => E4 q m
  | .attenuation6 q m => E6 q m
  | .fairMix s t => (1 / 2 : ℚ) • (effect s + effect t)

/-- Circuit profiles use zero ancillary inputs and the actual right data port.
No effect-coordinate evaluation occurs in this recursive definition. -/
def profile {n : ℕ} : Event n → (Fin n → ℂ) → ℝ
  | .zero, _ => 0
  | .total, x => ∑ i, Complex.normSq (x i)
  | .basis i, x => Complex.normSq (x i)
  | .attenuation0 q m, x => Complex.normSq
      ((NativeAttenuationCircuit.selectedCircuit q (8 * m)).eval
        (NativeAttenuationCircuit.input x) (.inl q.val.2))
  | .attenuation2 q m, x => Complex.normSq
      ((NativeAttenuationCircuit.selectedCircuit q (8 * m + 2)).eval
        (NativeAttenuationCircuit.input x) (.inl q.val.2))
  | .attenuation4 q m, x => Complex.normSq
      ((NativeAttenuationCircuit.selectedCircuit q (8 * m + 4)).eval
        (NativeAttenuationCircuit.input x) (.inl q.val.2))
  | .attenuation6 q m, x => Complex.normSq
      ((NativeAttenuationCircuit.selectedCircuit q (8 * m + 6)).eval
        (NativeAttenuationCircuit.input x) (.inl q.val.2))
  | .fairMix s t, x => (profile s x + profile t x) / 2

theorem quadratic_sum {n : ℕ} {ι : Type*} (s : Finset ι) (v : ι → V n)
    (x : Fin n → ℂ) :
    quadratic (∑ i ∈ s, v i) x = ∑ i ∈ s, quadratic (v i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadratic]
  | @insert i s hi ih => simp [Finset.sum_insert, hi, quadratic_add, ih]

theorem quadratic_identity {n : ℕ} (x : Fin n → ℂ) :
    quadratic (identity n) x = ∑ i, Complex.normSq (x i) := by
  rw [identity, quadratic_sum]
  simp only [quadratic_P]

/-- Algebraic soundness of every grammar event, including all nested mixtures. -/
theorem profile_soundness {n : ℕ} (s : Event n) (x : Fin n → ℂ) :
    profile s x = quadratic (effect s) x := by
  induction s with
  | zero => simp [profile, effect, quadratic]
  | total => exact (quadratic_identity x).symm
  | basis i => exact (quadratic_P i x).symm
  | attenuation0 q m => exact (NativeAttenuationCircuit.selected_E0 q m x).symm
  | attenuation2 q m => exact (NativeAttenuationCircuit.selected_E2 q m x).symm
  | attenuation4 q m => exact (NativeAttenuationCircuit.selected_E4 q m x).symm
  | attenuation6 q m => exact (NativeAttenuationCircuit.selected_E6 q m x).symm
  | fairMix s t ihs iht =>
      simp only [profile, effect, quadratic_smul, quadratic_add, ← ihs, ← iht]
      norm_num
      ring

/-- No injectivity or faithfulness of the quadratic representation is needed. -/
theorem equal_effect_implies_equal_profile {n : ℕ} (s t : Event n)
    (h : effect s = effect t) : ∀ x, profile s x = profile t x := by
  intro x
  rw [profile_soundness, profile_soundness, h]

/-- These are explicit supplied probability laws on the whole mixture grammar.
Global nonnegativity is a sufficient hypothesis; no minimality is asserted. -/
structure ProbabilityLaw (n : ℕ) where
  prob : Event (n + 1) → ℝ
  zero : prob .zero = 0
  total : prob .total = 1
  basisCalibration : prob (.basis 0) = 1
  nonnegative : ∀ s, 0 ≤ prob s
  fairMix : ∀ s t, prob (.fairMix s t) = (prob s + prob t) / 2
  profileSufficiency : ∀ s t, (∀ x, profile s x = profile t x) → prob s = prob t

theorem probability_factors {n : ℕ} (L : ProbabilityLaw n) :
    ∃ q : V (n + 1) → ℝ, ∀ s, q (effect s) = L.prob s := by
  apply (factorization_iff_fibre_constancy effect L.prob).mpr
  intro s t h
  exact L.profileSufficiency s t (equal_effect_implies_equal_profile s t h)

/-- Profile sufficiency and the supplied accounting laws select the calibrated
basis coordinate on every event of this certified grammar. -/
theorem probability_selected {n : ℕ} (L : ProbabilityLaw n) (s : Event (n + 1)) :
    L.prob s = ((effect s) (.inl 0) : ℝ) := by
  obtain ⟨q, hq⟩ := probability_factors L
  let D : Set (V (n + 1)) := Set.range effect
  have hzero : (0 : V (n + 1)) ∈ D := ⟨.zero, rfl⟩
  have hpzero : q 0 = 0 := (hq .zero).trans L.zero
  have hclosed : ∀ x ∈ D, ∀ y ∈ D, (1 / 2 : ℚ) • (x + y) ∈ D := by
    rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
    exact ⟨.fairMix u v, rfl⟩
  have hpres : ∀ x ∈ D, ∀ y ∈ D,
      q ((1 / 2 : ℚ) • (x + y)) = (q x + q y) / 2 := by
    rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
    exact (hq (.fairMix u v)).trans (by rw [L.fairMix, ← hq u, ← hq v])
  have hP : ∀ i, P i ∈ D := fun i => ⟨.basis i, rfl⟩
  have h0 : ∀ r m, E0 r m ∈ D := fun r m => ⟨.attenuation0 r m, rfl⟩
  have h2 : ∀ r m, E2 r m ∈ D := fun r m => ⟨.attenuation2 r m, rfl⟩
  have h4 : ∀ r m, E4 r m ∈ D := fun r m => ⟨.attenuation4 r m, rfl⟩
  have h6 : ∀ r m, E6 r m ∈ D := fun r m => ⟨.attenuation6 r m, rfl⟩
  have hId : identity (n + 1) ∈ D := ⟨.total, rfl⟩
  have hnorm : q (identity (n + 1)) = 1 := (hq .total).trans L.total
  have hcal : q (P 0) = 1 := (hq (.basis 0)).trans L.basisCalibration
  have hpos : ∀ v ∈ D, 0 ≤ q v := by
    rintro v ⟨u, rfl⟩
    rw [hq u]
    exact L.nonnegative u
  rw [← hq s]
  exact domain_basis_calibrated_selection D q hzero hpzero hclosed hpres hP
    h0 h2 h4 h6 hId hnorm hcal hpos (effect s) ⟨s, rfl⟩

/-- Every certified structural profile is mathematically nonnegative. -/
theorem profile_nonnegative {n : ℕ} (s : Event n) (x : Fin n → ℂ) :
    0 ≤ profile s x := by
  induction s with
  | zero => exact le_refl 0
  | total => exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (x i)
  | basis i => exact Complex.normSq_nonneg (x i)
  | attenuation0 q m => exact Complex.normSq_nonneg _
  | attenuation2 q m => exact Complex.normSq_nonneg _
  | attenuation4 q m => exact Complex.normSq_nonneg _
  | attenuation6 q m => exact Complex.normSq_nonneg _
  | fairMix s t ihs iht => exact div_nonneg (add_nonneg ihs iht) (by norm_num)

/-- Retaining every ancillary port supplies a selected-port upper bound. -/
private theorem selected_profile_le_total {n : ℕ} (q : UpperPair n) (k : ℕ)
    (x : Fin n → ℂ) :
    Complex.normSq ((NativeAttenuationCircuit.selectedCircuit q k).eval
      (NativeAttenuationCircuit.input x) (.inl q.val.2)) ≤
        ∑ i, Complex.normSq (x i) := by
  rw [← NativeAttenuationCircuit.all_port_resolution
    (NativeAttenuationCircuit.selectedCircuit q k) x]
  exact Finset.single_le_sum (fun w _ => Complex.normSq_nonneg _)
    (Finset.mem_univ (Sum.inl q.val.2 : NativeAttenuationCircuit.Wire n k))

/-- Each event profile is bounded by the total input weight. -/
theorem profile_le_total {n : ℕ} (s : Event n) (x : Fin n → ℂ) :
    profile s x ≤ ∑ i, Complex.normSq (x i) := by
  induction s with
  | zero => exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (x i)
  | total => exact le_refl _
  | basis i =>
      exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j))
        (Finset.mem_univ i)
  | attenuation0 q m => exact selected_profile_le_total q (8 * m) x
  | attenuation2 q m => exact selected_profile_le_total q (8 * m + 2) x
  | attenuation4 q m => exact selected_profile_le_total q (8 * m + 4) x
  | attenuation6 q m => exact selected_profile_le_total q (8 * m + 6) x
  | fairMix s t ihs iht =>
      change (profile s x + profile t x) / 2 ≤ _
      linarith

/-- A mathematical consistency witness evaluated at one actual basis input.
This construction is downstream of selection and is not one of its premises.
It asserts no physical preparation or probability actualization. -/
def canonicalProbabilityLaw (n : ℕ) : ProbabilityLaw n where
  prob s := profile s (MixerGeneratedProcessWall.single 0 1)
  zero := rfl
  total := by simp [profile, MixerGeneratedProcessWall.single, apply_ite]
  basisCalibration := by simp [profile, MixerGeneratedProcessWall.single]
  nonnegative s := profile_nonnegative s _
  fairMix _ _ := rfl
  profileSufficiency _ _ h := h _

theorem probabilityLaw_nonempty (n : ℕ) : Nonempty (ProbabilityLaw n) :=
  ⟨canonicalProbabilityLaw n⟩

/-- The selected probability functions agree extensionally on this grammar. -/
theorem probability_unique {n : ℕ} (L M : ProbabilityLaw n) : L.prob = M.prob := by
  funext s
  exact (probability_selected L s).trans (probability_selected M s).symm

/-- All supplied laws inherit the canonical witness's unit-interval bounds. -/
theorem probability_bounds {n : ℕ} (L : ProbabilityLaw n) (s : Event (n + 1)) :
    0 ≤ L.prob s ∧ L.prob s ≤ 1 := by
  have h := congrFun (probability_unique L (canonicalProbabilityLaw n)) s
  change L.prob s = profile s (MixerGeneratedProcessWall.single 0 1) at h
  rw [h]
  refine ⟨profile_nonnegative s _, ?_⟩
  simpa [MixerGeneratedProcessWall.single, apply_ite] using
    profile_le_total s (MixerGeneratedProcessWall.single 0 1)

end
end IDT.QMClosure.NativeEventProbabilityBridge
