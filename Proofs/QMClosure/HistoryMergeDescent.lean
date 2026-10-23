import Proofs.QMClosure.QuarticContextTransport

namespace IDT.QMClosure.HistoryMergeDescent

noncomputable section

/-! Conditional mathematics on one supplied coherent family. Lists provide
unrestricted concatenation; admissibility of physical concatenations is not
derived. Neither amplitudes nor their additive evaluation come from primitives. -/

def eval {H V : Type*} [AddCommMonoid V] (a : H → V) (P : List H) : V :=
  (P.map a).sum

def substitute {H K : Type*} (σ : H → List K) (P : List H) : List K := P.flatMap σ

theorem eval_append {H V : Type*} [AddCommMonoid V] (a : H → V) (P Q : List H) :
    eval a (P ++ Q) = eval a P + eval a Q := by simp [eval]

theorem eval_perm {H V : Type*} [AddCommMonoid V] (a : H → V)
    {P Q : List H} (h : P.Perm Q) : eval a P = eval a Q := by
  exact (h.map a).sum_eq

theorem substitute_append {H K : Type*} (σ : H → List K) (P Q : List H) :
    substitute σ (P ++ Q) = substitute σ P ++ substitute σ Q := by
  simp [substitute]

/-- Exactly the congruence needed to descend a uniform substitution through eval. -/
def Descends {H K V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    (a : H → V) (b : K → W) (σ : H → List K) : Prop :=
  ∀ P Q, eval a P = eval a Q → eval b (substitute σ P) = eval b (substitute σ Q)

theorem descent_iff_unique_factor {H K V W : Type*}
    [AddCommMonoid V] [AddCommMonoid W]
    (a : H → V) (b : K → W) (σ : H → List K)
    (hsurj : Function.Surjective (eval a)) :
    Descends a b σ ↔ ∃! T : V → W, ∀ P, T (eval a P) = eval b (substitute σ P) := by
  constructor
  · intro hd
    let pick : V → List H := fun v => Classical.choose (hsurj v)
    have hpick (v : V) : eval a (pick v) = v := Classical.choose_spec (hsurj v)
    let T : V → W := fun v => eval b (substitute σ (pick v))
    have hT (P : List H) : T (eval a P) = eval b (substitute σ P) :=
      hd _ _ (hpick _)
    refine ⟨T, hT, ?_⟩
    intro S hS
    funext v
    calc
      S v = S (eval a (pick v)) := by rw [hpick]
      _ = T v := hS (pick v)
  · rintro ⟨T, hT, _⟩ P Q hPQ
    rw [← hT, ← hT, hPQ]

/-- Reachable pairs suffice; no assertion that eval covers V is needed here. -/
theorem factor_additive_on_reachable {H K V W : Type*}
    [AddCommMonoid V] [AddCommMonoid W]
    (a : H → V) (b : K → W) (σ : H → List K) (T : V → W)
    (hT : ∀ P, T (eval a P) = eval b (substitute σ P)) (P Q : List H) :
    T (eval a P + eval a Q) = T (eval a P) + T (eval a Q) := by
  rw [← eval_append, hT, substitute_append, eval_append, hT, hT]

theorem factor_additive_of_surjective {H K V W : Type*}
    [AddCommMonoid V] [AddCommMonoid W]
    (a : H → V) (b : K → W) (σ : H → List K) (T : V → W)
    (hT : ∀ P, T (eval a P) = eval b (substitute σ P))
    (hsurj : Function.Surjective (eval a)) : ∀ x y, T (x + y) = T x + T y := by
  intro x y
  obtain ⟨P, rfl⟩ := hsurj x
  obtain ⟨Q, rfl⟩ := hsurj y
  exact factor_additive_on_reachable a b σ T hT P Q

/-- Occurrencewise transformation must respect every equality of history sums. -/
def HistDescends {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    (f : V → W) : Prop :=
  ∀ P Q : List V, P.sum = Q.sum → (P.map f).sum = (Q.map f).sum

theorem hist_descends_iff {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    (f : V → W) : HistDescends f ↔ f 0 = 0 ∧ ∀ x y, f (x + y) = f x + f y := by
  constructor
  · intro h
    constructor
    · simpa using (h [0] [] (by simp))
    · intro x y
      simpa using (h [x + y] [x, y] (by simp))
  · rintro ⟨hzero, hadd⟩
    have hsum (P : List V) : (P.map f).sum = f P.sum := by
      induction P with
      | nil => simpa using hzero.symm
      | cons x P ih => simpa [hadd] using congrArg (fun z => f x + z) ih
    intro P Q hPQ
    rw [hsum, hsum, hPQ]

/-! The reference and the positive comparison port are supplied. They define a
fixed comparison frame, not ordinary projective/ray equivalence. -/

def referenceProbability {V : Type*} [AddCommGroup V]
    (W : V → ℝ) (c : ℝ) (r x : V) : ℝ := W (x + r) / (W (x + r) + c)

def RefEquivalent {V : Type*} [AddCommGroup V]
    (W : V → ℝ) (c : ℝ) (x y : V) : Prop :=
  ∀ r, referenceProbability W c r x = referenceProbability W c r y

theorem reference_equivalent_iff {V : Type*} [AddCommGroup V]
    (W : V → ℝ) (hW : ∀ v, 0 ≤ W v) (hzero : ∀ v, W v = 0 ↔ v = 0)
    (c : ℝ) (hc : 0 < c) (x y : V) : RefEquivalent W c x y ↔ x = y := by
  constructor
  · intro h
    have hden : W (y + -x) + c ≠ 0 := ne_of_gt (by linarith [hW (y + -x)])
    have hh : W (y + -x) / (W (y + -x) + c) = 0 := by
      simpa [referenceProbability, (hzero 0).2 rfl] using (h (-x)).symm
    have hz : W (y + -x) = 0 := (div_eq_zero_iff.mp hh).resolve_right hden
    have he : y + -x = 0 := (hzero _).mp hz
    have : y = x := by simpa using congrArg (fun z => z + x) he
    exact this.symm
  · rintro rfl r
    rfl

theorem every_function_preserves_reference_equivalence {V : Type*} [AddCommGroup V]
    (W : V → ℝ) (hW : ∀ v, 0 ≤ W v) (hzero : ∀ v, W v = 0 ↔ v = 0)
    (c : ℝ) (hc : 0 < c) (f : V → V) (x y : V) (hxy : RefEquivalent W c x y) :
    RefEquivalent W c (f x) (f y) := by
  rw [(reference_equivalent_iff W hW hzero c hc x y).mp hxy]
  intro r
  rfl

theorem cross_pipeline_iff_additive {V : Type*} [AddCommGroup V]
    (W : V → ℝ) (hW : ∀ v, 0 ≤ W v) (hzero : ∀ v, W v = 0 ↔ v = 0)
    (c : ℝ) (hc : 0 < c) (f : V → V) :
    (∀ x y r, referenceProbability W c r (f (x + y)) =
      referenceProbability W c r (f x + f y)) ↔
    ∀ x y, f (x + y) = f x + f y := by
  constructor
  · intro h x y
    exact (reference_equivalent_iff W hW hzero c hc _ _).mp (h x y)
  · intro h x y r
    rw [h x y]

/-! A three-label, atom-weight-preserving relabeling that does not descend. -/

def tinyAmplitude (i : Fin 3) : ℝ := if i.val = 2 then -1 else 1
def tinyRelabel (i : Fin 3) : Fin 3 :=
  if i.val = 0 then 0 else if i.val = 1 then 2 else 1
def tinySubstitution (i : Fin 3) : List (Fin 3) := [tinyRelabel i]

theorem tiny_relabel_involutive : Function.Involutive tinyRelabel := by
  intro i
  fin_cases i <;> norm_num [tinyRelabel]
  rfl

theorem tiny_atomic_weights_preserved (i : Fin 3) :
    tinyAmplitude (tinyRelabel i) ^ 2 = tinyAmplitude i ^ 2 := by
  fin_cases i <;> norm_num [tinyRelabel, tinyAmplitude]

theorem tiny_substitution_involutive (P : List (Fin 3)) :
    substitute tinySubstitution (substitute tinySubstitution P) = P := by
  induction P with
  | nil => rfl
  | cons i P ih =>
    simp only [substitute, List.flatMap_cons, tinySubstitution, List.singleton_append]
    rw [tiny_relabel_involutive]
    exact congrArg (List.cons i) ih

theorem tiny_substitution_not_descending :
    ¬ Descends tinyAmplitude tinyAmplitude tinySubstitution := by
  intro h
  have hh := h [0] [1] (by norm_num [eval, tinyAmplitude])
  norm_num [eval, substitute, tinySubstitution, tinyRelabel, tinyAmplitude] at hh

/-- Atom weights are preserved, coherent event weights are not. -/
theorem tiny_coherent_event_changes :
    eval tinyAmplitude [0, 2] ^ 2 = 0 ∧
    eval tinyAmplitude (substitute tinySubstitution [0, 2]) ^ 2 = 4 := by
  norm_num [eval, substitute, tinySubstitution, tinyRelabel, tinyAmplitude]

/-! Real collinear refinements alone do not imply arbitrary history descent. -/

open IDT.QMClosure.QuarticContextTransport

theorem quartic_collinear_refinement (a b s t : ℝ) (v : Plane) :
    quarticRotate a b (s • v + t • v) =
      quarticRotate a b (s • v) + quarticRotate a b (t • v) := by
  rw [← add_smul, quartic_rotation_homogeneous, quartic_rotation_homogeneous,
    quartic_rotation_homogeneous, add_smul]

theorem quartic_refinement_negative_control :
    (∀ s t : ℝ, ∀ v : Plane,
      quarticRotate (3 / 5) (4 / 5) (s • v + t • v) =
        quarticRotate (3 / 5) (4 / 5) (s • v) +
          quarticRotate (3 / 5) (4 / 5) (t • v)) ∧
    ¬ HistDescends (quarticRotate (3 / 5) (4 / 5)) := by
  refine ⟨quartic_collinear_refinement (3 / 5) (4 / 5), ?_⟩
  intro h
  exact concrete_mixing_not_additive (((hist_descends_iff _).mp h).2 (1, 0) (0, 1))

theorem plane_q4_nonnegative (v : Plane) : 0 ≤ planeQ4 v := by
  unfold planeQ4
  positivity

theorem plane_q4_zero_iff (v : Plane) : planeQ4 v = 0 ↔ v = 0 := by
  constructor
  · intro h
    unfold planeQ4 at h
    have hxnonneg : 0 ≤ v.1 ^ 4 := by positivity
    have hynonneg : 0 ≤ v.2 ^ 4 := by positivity
    have hx : v.1 ^ 4 = 0 := by linarith
    have hy : v.2 ^ 4 = 0 := by linarith
    have hx0 : v.1 = 0 := (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp hx
    have hy0 : v.2 = 0 := (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp hy
    exact Prod.ext hx0 hy0
  · rintro rfl
    norm_num [planeQ4]

theorem quartic_state_equivalence_negative_control :
    (∀ x y : Plane, RefEquivalent planeQ4 1 x y →
      RefEquivalent planeQ4 1 (quarticRotate (3 / 5) (4 / 5) x)
        (quarticRotate (3 / 5) (4 / 5) y)) ∧
    ¬ HistDescends (quarticRotate (3 / 5) (4 / 5)) := by
  exact ⟨fun x y h => every_function_preserves_reference_equivalence
    planeQ4 plane_q4_nonnegative plane_q4_zero_iff 1 (by norm_num) _ x y h,
    quartic_refinement_negative_control.2⟩

/-! False-rejection control: a mode-sensitive linear operation need not descend
through an arbitrarily lossy scalar adapter. It is not an operation on that
already-merged scalar preparation. -/

def phaseFlip (v : Plane) : Plane := (v.1, -v.2)
def scalarTotal (v : Plane) : ℝ := v.1 + v.2

theorem phase_flip_additive (v w : Plane) :
    phaseFlip (v + w) = phaseFlip v + phaseFlip w := by
  apply Prod.ext <;> simp [phaseFlip, add_comm]

theorem phase_flip_homogeneous (t : ℝ) (v : Plane) :
    phaseFlip (t • v) = t • phaseFlip v := by
  apply Prod.ext <;> simp [phaseFlip]

theorem phase_flip_involutive : Function.Involutive phaseFlip := by
  intro v
  apply Prod.ext <;> simp [phaseFlip]

theorem phase_flip_preserves_squares (v : Plane) :
    (phaseFlip v).1 ^ 2 + (phaseFlip v).2 ^ 2 = v.1 ^ 2 + v.2 ^ 2 := by
  simp [phaseFlip]

theorem lossy_adapter_has_no_phase_flip_factor :
    ¬ ∃ F : ℝ → ℝ, ∀ v : Plane, F (scalarTotal v) = scalarTotal (phaseFlip v) := by
  rintro ⟨F, hF⟩
  have h1 := hF (1, 0)
  have h2 := hF (0, 1)
  norm_num [phaseFlip, scalarTotal] at h1 h2
  linarith

/-! Local machine-visible ledger: mathematical results above do not discharge
these physical bridges or alter any manifest/closure status. -/

inductive OpenBridge where
  | physicallyAdmissibleCoherentHistoriesAndConcatenation
  | suppliedAmplitudeCarrierAndAdditiveEvaluation
  | contextActionIsUniformOccurrenceSubstitution
  | evaluationCongruencePreservedBySubstitution
  | equivalenceCompleteForAdmittedContinuationFamily
  | surjectiveReachabilityOfWholeCarrierAndContinuum
  | allReferencesAndFixedPositiveComparisonPortAccessible
  deriving DecidableEq, Repr

def openBridges : List OpenBridge :=
  [.physicallyAdmissibleCoherentHistoriesAndConcatenation,
   .suppliedAmplitudeCarrierAndAdditiveEvaluation,
   .contextActionIsUniformOccurrenceSubstitution,
   .evaluationCongruencePreservedBySubstitution,
   .equivalenceCompleteForAdmittedContinuationFamily,
   .surjectiveReachabilityOfWholeCarrierAndContinuum,
   .allReferencesAndFixedPositiveComparisonPortAccessible]

theorem open_bridge_ledger_has_seven_entries : openBridges.length = 7 := rfl

end
end IDT.QMClosure.HistoryMergeDescent
