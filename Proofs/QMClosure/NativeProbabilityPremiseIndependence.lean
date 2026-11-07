import Proofs.QMClosure.NativeVacuumProbabilityFamily
import Proofs.QMClosure.NativeContextualProbabilityControl

/-!
# Logical irredundance of the six native probability conditions

The predicates below restate the exact six fields of
`NativeVacuumProbabilityFamily.Law`. Their conjunction is equivalent to
inhabiting that law with the specified probability field. For each condition,
an explicit field satisfies the other five and violates that condition.

This is logical irredundance for the supplied scalar normalized-mixer syntax
over all finite wire types. It is not physical minimality, independence for
arbitrary raw models, probability actualization, or full QM closure. In
particular the field violating nonnegativity is not a probability proposal.
-/

namespace IDT.QMClosure.NativeProbabilityPremiseIndependence

noncomputable section
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open scoped BigOperators

abbrev ProbabilityField :=
  {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Native ι → ι → ℝ

inductive Requirement where
  | nonnegative
  | normalized
  | prepared_eq
  | output_perm
  | spectator_pair
  | vacuum
  deriving DecidableEq, Repr

def Nonnegative (P : ProbabilityField) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) i, 0 ≤ P s c i

def Normalized (P : ProbabilityField) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι), ∑ i, P s c i = 1

def PreparedEq (P : ProbabilityField) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c d : Native ι),
    c.eval (source s) = d.eval (source s) → P s c = P s d

def OutputPerm (P : ProbabilityField) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι)
    (e : Equiv.Perm ι) i, P s (.seq c (.permute e)) i = P s c (e i)

def SpectatorPair (P : ProbabilityField) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι)
    (i j k : ι) (hij : i ≠ j),
    k ≠ i → k ≠ j → P s (.seq c (.pair i j hij)) k = P s c k

def Vacuum (P : ProbabilityField) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Native ι) i,
    P (.inl s) (padCircuit κ c) (.inl i) = P s c i

def Holds (P : ProbabilityField) : Requirement → Prop
  | .nonnegative => Nonnegative P
  | .normalized => Normalized P
  | .prepared_eq => PreparedEq P
  | .output_perm => OutputPerm P
  | .spectator_pair => SpectatorPair P
  | .vacuum => Vacuum P

def HoldsExcept (P : ProbabilityField) (missing : Requirement) : Prop :=
  ∀ requirement, requirement ≠ missing → Holds P requirement

def toLaw (P : ProbabilityField) (h : ∀ r, Holds P r) : Law where
  prob := P
  nonnegative := h .nonnegative
  normalized := h .normalized
  prepared_eq := h .prepared_eq
  output_perm := h .output_perm
  spectator_pair := h .spectator_pair
  vacuum := h .vacuum

theorem law_holds (L : Law) : ∀ r, Holds (@Law.prob L) r := by
  intro r
  cases r with
  | nonnegative => exact L.nonnegative
  | normalized => exact L.normalized
  | prepared_eq => exact L.prepared_eq
  | output_perm => exact L.output_perm
  | spectator_pair => exact L.spectator_pair
  | vacuum => exact L.vacuum

/-- This verifies that the independence predicates neither weaken nor strengthen
the established law's conditions. -/
theorem all_holds_iff_law (P : ProbabilityField) :
    (∀ r, Holds P r) ↔ ∃ L : Law, @Law.prob L = @P := by
  constructor
  · intro h
    exact ⟨toLaw P h, rfl⟩
  · rintro ⟨L, rfl⟩
    exact law_holds L

/-! Removing nonnegativity: real amplitudes retain coherent normalization. -/

def realPart : ProbabilityField := fun s c i => (c.eval (source s) i).re

theorem realPart_normalized : Normalized realPart := by
  intro ι _ _ s c
  have hs := c.preserves_sum NativeMixerEventConeExclusion.mixer_transparent
    NativeMixerEventConeExclusion.mixer_square (source s)
  calc
    ∑ i, realPart s c i = (∑ i, c.eval (source s) i).re :=
      (map_sum Complex.reAddGroupHom _ Finset.univ).symm
    _ = 1 := by
      change (coherentSum (c.eval (source s))).re = 1
      rw [hs]
      simp [coherentSum, source, single]

theorem realPart_prepared : PreparedEq realPart := by
  intro ι _ _ s c d h
  funext i
  change (c.eval (source s) i).re = (d.eval (source s) i).re
  rw [h]

theorem realPart_permutation : OutputPerm realPart := by
  intro ι _ _ s c e i
  rfl

theorem realPart_spectator : SpectatorPair realPart := by
  intro ι _ _ s c i j k hij hki hkj
  change (pairReplace NativeMixerEventConeExclusion.mixer i j (c.eval (source s)) k).re = _
  simp [pairReplace, hki, hkj, realPart]

theorem realPart_vacuum : Vacuum realPart := by
  intro ι κ _ _ _ _ s c i
  change ((padCircuit κ c).eval (source (.inl s)) (.inl i)).re = _
  rw [pad_prepared]
  rfl

theorem realPart_negative_witness :
    realPart (0 : Fin 3) NativeMixerEventConeExclusion.cPlus 0 = -1 / 4 := by
  have hs : source (0 : Fin 3) = NativeMixerEventConeExclusion.input 1 0 := by
    funext k
    fin_cases k <;> norm_num [source, single, NativeMixerEventConeExclusion.input]
  change (NativeMixerEventConeExclusion.cPlus.eval (source 0) 0).re = _
  rw [hs, NativeMixerEventConeExclusion.cPlus_selected]
  norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

theorem realPart_not_nonnegative : ¬Nonnegative realPart := by
  intro h
  have hh := h (0 : Fin 3) NativeMixerEventConeExclusion.cPlus 0
  change 0 ≤ realPart (0 : Fin 3) NativeMixerEventConeExclusion.cPlus 0 at hh
  rw [realPart_negative_witness] at hh
  norm_num at hh

theorem realPart_holdsExcept : HoldsExcept realPart .nonnegative := by
  intro r hr
  cases r with
  | nonnegative => exact (hr rfl).elim
  | normalized => exact realPart_normalized
  | prepared_eq => exact realPart_prepared
  | output_perm => exact realPart_permutation
  | spectator_pair => exact realPart_spectator
  | vacuum => exact realPart_vacuum

/-! Removing normalization: the zero field. -/

def zeroField : ProbabilityField := fun _ _ _ => 0

theorem zero_not_normalized : ¬Normalized zeroField := by
  intro h
  have hh := h PUnit.unit (.identity : Native PUnit)
  norm_num [zeroField] at hh

theorem zero_holdsExcept : HoldsExcept zeroField .normalized := by
  intro r hr
  cases r with
  | nonnegative => intro ι _ _ s c i; exact le_rfl
  | normalized => exact (hr rfl).elim
  | prepared_eq => intro ι _ _ s c d _; rfl
  | output_perm => intro ι _ _ s c e i; rfl
  | spectator_pair => intro ι _ _ s c i j k hij hki hkj; rfl
  | vacuum => intro ι κ _ _ _ _ s c i; rfl

/-! Removing prepared-state equivalence: literal stochastic averaging syntax. -/

def averagingGate : (ℝ × ℝ) →+ (ℝ × ℝ) where
  toFun p := ((p.1 + p.2) / 2, (p.1 + p.2) / 2)
  map_zero' := by norm_num
  map_add' p q := by
    apply Prod.ext <;> change ((_ + _) + (_ + _)) / 2 = (_ + _) / 2 + (_ + _) / 2 <;> ring

def averagingCircuit {ι : Type} : Native ι → Circuit (ι := ι) averagingGate
  | .identity => .identity
  | .pair i j hij => .pair i j hij
  | .permute e => .permute e
  | .seq c d => .seq (averagingCircuit c) (averagingCircuit d)

def averaging : ProbabilityField :=
  fun s c i => (averagingCircuit c).eval (single s (1 : ℝ)) i

theorem averaging_eval_nonnegative {ι : Type} [DecidableEq ι]
    (c : Native ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ (averagingCircuit c).eval x i := by
  induction c generalizing x with
  | identity => exact hx
  | pair i j hij =>
      intro k
      change 0 ≤ if k = i then (x i + x j) / 2
        else if k = j then (x i + x j) / 2 else x k
      split_ifs <;> linarith [hx i, hx j, hx k]
  | permute e => exact fun k => hx (e k)
  | seq c d hc hd => exact hd _ (hc x hx)

theorem averaging_nonnegative : Nonnegative averaging := by
  intro ι _ _ s c i
  apply averaging_eval_nonnegative c _ _ i
  intro k
  simp only [single]
  split_ifs <;> norm_num

theorem averaging_normalized : Normalized averaging := by
  intro ι _ _ s c
  have hc : ∀ x y : ℝ, (averagingGate (x, y)).1 + (averagingGate (x, y)).2 = x + y := by
    intro x y
    change (x + y) / 2 + (x + y) / 2 = x + y
    ring
  have h := (averagingCircuit c).preserves_readout (fun x : ℝ => x) hc (single s (1 : ℝ))
  simpa [averaging, totalReadout, single] using h

theorem averaging_permutation : OutputPerm averaging := by
  intro ι _ _ s c e i
  rfl

theorem averaging_spectator : SpectatorPair averaging := by
  intro ι _ _ s c i j k hij hki hkj
  change pairReplace averagingGate i j ((averagingCircuit c).eval (single s (1 : ℝ))) k = _
  simp [pairReplace, hki, hkj, averaging]

def realPad {ι κ : Type} (x : ι → ℝ) : ι ⊕ κ → ℝ := Sum.elim x (fun _ => 0)

theorem averaging_pad_eval {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (c : Native ι) (x : ι → ℝ) :
    (averagingCircuit (padCircuit κ c)).eval (realPad x) =
      realPad ((averagingCircuit c).eval x) := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij =>
      funext w
      cases w <;> simp [averagingCircuit, padCircuit, realPad, Circuit.eval, pairGate, pairReplace]
  | permute e =>
      funext w
      cases w <;> simp [averagingCircuit, padCircuit, realPad, Circuit.eval]
  | seq c d hc hd =>
      change (averagingCircuit (padCircuit κ d)).eval
        ((averagingCircuit (padCircuit κ c)).eval (realPad x)) = _
      rw [hc, hd]
      rfl

theorem averaging_vacuum : Vacuum averaging := by
  intro ι κ _ _ _ _ s c i
  have hs : single (Sum.inl s : ι ⊕ κ) (1 : ℝ) = realPad (single s (1 : ℝ)) := by
    funext k
    cases k <;> simp [single, realPad]
  change (averagingCircuit (padCircuit κ c)).eval (single (.inl s) (1 : ℝ)) (.inl i) = _
  rw [hs, averaging_pad_eval]
  rfl

def pairTwo : Native (Fin 2) := .pair 0 1 (by decide)
def fourth : Native (Fin 2) := .seq (.seq (.seq pairTwo pairTwo) pairTwo) pairTwo

theorem fourth_prepared_identity :
    fourth.eval (source 0) = (Circuit.identity : Native (Fin 2)).eval (source 0) := by
  funext k
  fin_cases k <;> apply Complex.ext <;>
    norm_num [fourth, pairTwo, Circuit.eval, pairGate, pairReplace,
      NativeMixerEventConeExclusion.mixer, NativeMixerEventConeExclusion.Raw,
      CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n_re,
      CompositeProductControls.RawSign.n_im, source, single,
      show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide]

theorem averaging_fourth : averaging (0 : Fin 2) fourth 0 = 1 / 2 := by
  norm_num [averaging, averagingCircuit, fourth, pairTwo, Circuit.eval,
    pairGate, pairReplace, averagingGate, single,
    show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide]

theorem averaging_identity : averaging (0 : Fin 2) .identity 0 = 1 := by
  simp [averaging, averagingCircuit, Circuit.eval, single]

theorem averaging_not_prepared : ¬PreparedEq averaging := by
  intro h
  have hh := congrFun (h (0 : Fin 2) fourth .identity fourth_prepared_identity) 0
  change averaging (0 : Fin 2) fourth 0 = averaging (0 : Fin 2) .identity 0 at hh
  rw [averaging_fourth, averaging_identity] at hh
  norm_num at hh

theorem averaging_holdsExcept : HoldsExcept averaging .prepared_eq := by
  intro r hr
  cases r with
  | nonnegative => exact averaging_nonnegative
  | normalized => exact averaging_normalized
  | prepared_eq => exact (hr rfl).elim
  | output_perm => exact averaging_permutation
  | spectator_pair => exact averaging_spectator
  | vacuum => exact averaging_vacuum

/-! Removing output covariance: keep all mass at the marked source label. -/

def fixedSource : ProbabilityField := fun s _ i => if i = s then 1 else 0

theorem fixedSource_not_permutation : ¬OutputPerm fixedSource := by
  intro h
  have hh := h (0 : Fin 2) .identity (Equiv.swap 0 1) 0
  norm_num [fixedSource, show (1 : Fin 2) ≠ 0 by decide] at hh

theorem fixedSource_holdsExcept : HoldsExcept fixedSource .output_perm := by
  intro r hr
  cases r with
  | nonnegative =>
      intro ι _ _ s c i
      simp only [fixedSource]
      split_ifs <;> norm_num
  | normalized => intro ι _ _ s c; simp [fixedSource]
  | prepared_eq => intro ι _ _ s c d _; rfl
  | output_perm => exact (hr rfl).elim
  | spectator_pair => intro ι _ _ s c i j k hij hki hkj; rfl
  | vacuum => intro ι κ _ _ _ _ s c i; simp [fixedSource]

/-! Removing spectator locality: normalized squared structural weights. -/

def contextual : ProbabilityField :=
  fun s c i => NativeContextualProbabilityControl.circuitProbability s c i

theorem contextual_nonnegative : Nonnegative contextual := by
  intro ι _ _ s c i
  exact (NativeContextualProbabilityControl.circuit_probability_bounds s c i).1

theorem contextual_normalized : Normalized contextual := by
  intro ι _ _ s c
  exact NativeContextualProbabilityControl.circuit_probability_sum s c

theorem contextual_prepared : PreparedEq contextual := by
  intro ι _ _ s c d h
  funext i
  change NativeContextualProbabilityControl.probability (c.eval (source s)) i =
    NativeContextualProbabilityControl.probability (d.eval (source s)) i
  rw [h]

theorem contextual_permutation : OutputPerm contextual := by
  intro ι _ _ s c e i
  exact NativeContextualProbabilityControl.probability_permutation (c.eval (source s)) e i

theorem contextual_vacuum : Vacuum contextual := by
  intro ι κ _ _ _ _ s c i
  change NativeContextualProbabilityControl.probability
    ((padCircuit κ c).eval (source (.inl s))) (.inl i) = _
  rw [pad_prepared]
  exact NativeContextualProbabilityControl.probability_vacuum_data (c.eval (source s)) i

theorem contextual_not_spectator : ¬SpectatorPair contextual := by
  intro h
  have hh := h (0 : Fin 3) NativeContextualProbabilityControl.witnessBefore
    1 2 0 (by decide) (by decide) (by decide)
  change NativeContextualProbabilityControl.circuitProbability
      0 NativeContextualProbabilityControl.witnessAfter 0 =
    NativeContextualProbabilityControl.circuitProbability
      0 NativeContextualProbabilityControl.witnessBefore 0 at hh
  exact NativeContextualProbabilityControl.spectator_operation_changes_probability hh.symm

theorem contextual_holdsExcept : HoldsExcept contextual .spectator_pair := by
  intro r hr
  cases r with
  | nonnegative => exact contextual_nonnegative
  | normalized => exact contextual_normalized
  | prepared_eq => exact contextual_prepared
  | output_perm => exact contextual_permutation
  | spectator_pair => exact (hr rfl).elim
  | vacuum => exact contextual_vacuum

/-! Removing vacuum compatibility: uniform mass depends on total wire count. -/

def uniform : ProbabilityField := fun {ι} _ _ _ _ _ => 1 / (Fintype.card ι : ℝ)

theorem uniform_normalized : Normalized uniform := by
  intro ι _ _ s c
  letI : Nonempty ι := ⟨s⟩
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  simp [uniform, nsmul_eq_mul, div_eq_mul_inv, hn]

theorem uniform_not_vacuum : ¬Vacuum uniform := by
  intro h
  have hh := h (ι := Fin 1) (κ := Fin 1) 0 .identity 0
  norm_num [uniform] at hh

theorem uniform_holdsExcept : HoldsExcept uniform .vacuum := by
  intro r hr
  cases r with
  | nonnegative =>
      intro ι _ _ s c i
      exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  | normalized => exact uniform_normalized
  | prepared_eq => intro ι _ _ s c d _; rfl
  | output_perm => intro ι _ _ s c e i; rfl
  | spectator_pair => intro ι _ _ s c i j k hij hki hkj; rfl
  | vacuum => exact (hr rfl).elim

/-- Each exact scalar native-law condition is independent of the other five. -/
theorem six_conditions_irredundant (missing : Requirement) :
    ∃ P : ProbabilityField, HoldsExcept P missing ∧ ¬Holds P missing := by
  cases missing with
  | nonnegative => exact ⟨realPart, realPart_holdsExcept, realPart_not_nonnegative⟩
  | normalized => exact ⟨zeroField, zero_holdsExcept, zero_not_normalized⟩
  | prepared_eq => exact ⟨averaging, averaging_holdsExcept, averaging_not_prepared⟩
  | output_perm => exact ⟨fixedSource, fixedSource_holdsExcept, fixedSource_not_permutation⟩
  | spectator_pair => exact ⟨contextual, contextual_holdsExcept, contextual_not_spectator⟩
  | vacuum => exact ⟨uniform, uniform_holdsExcept, uniform_not_vacuum⟩

end

end IDT.QMClosure.NativeProbabilityPremiseIndependence
