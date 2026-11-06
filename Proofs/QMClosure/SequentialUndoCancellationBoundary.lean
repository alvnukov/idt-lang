import Proofs.QMClosure.LocalHistoryReadoutOrderWall
import Lean.Elab.Tactic.Omega

namespace IDT.QMClosure.SequentialUndoCancellationBoundary

/-!
# Serial undo, serial darkness, and contextual pair erasure

The supplied pre-cancellation syntax is a four-colour finite bag, bag union,
cyclic serial convolution, and C4 phase rotation. No Gaussian quotient is
assumed for its raw carrier. Stable distinguishability as merge injectivity
and sequential undo do not say that an antipodal bag is observationally empty.

The universal positive control `weight` is calibrated, C4 invariant and serial
multiplicative. Antipodal bags are dark in every serial continuation, but
inserting them beside a coherent reference changes its weight. Thus terminal
or serial darkness does not imply contextual cancellation.

The positive theorem identifies the exact extra bridge: invariance under
insertion of both antipodal pairs is equivalent to unique factorization through
the supplied integer residual map. It does not derive that bridge from native
primitives. Neither this quotient nor the competing augmentation congruence is
selected uniquely by the grammar. No Born, QM, or physical claim is made.
-/

namespace Native
export LocalHistoryReadoutOrderWall
  (Residual merge serial rotate inverseToken quadratic quadratic_nonnegative
    quadratic_rotation quadratic_serial)
end Native
abbrev Residual := Native.Residual

@[ext] structure Raw where
  n0 : ℕ
  n1 : ℕ
  n2 : ℕ
  n3 : ℕ
  deriving DecidableEq

def empty : Raw := ⟨0, 0, 0, 0⟩
def merge (a b : Raw) : Raw :=
  ⟨a.n0 + b.n0, a.n1 + b.n1, a.n2 + b.n2, a.n3 + b.n3⟩
def e0 : Raw := ⟨1, 0, 0, 0⟩
def e1 : Raw := ⟨0, 1, 0, 0⟩
def e2 : Raw := ⟨0, 0, 1, 0⟩
def e3 : Raw := ⟨0, 0, 0, 1⟩

/-- Ordinary cyclic convolution, before imposing antipodal cancellation. -/
def serial (a b : Raw) : Raw :=
  ⟨a.n0*b.n0 + a.n1*b.n3 + a.n2*b.n2 + a.n3*b.n1,
   a.n0*b.n1 + a.n1*b.n0 + a.n2*b.n3 + a.n3*b.n2,
   a.n0*b.n2 + a.n1*b.n1 + a.n2*b.n0 + a.n3*b.n3,
   a.n0*b.n3 + a.n1*b.n2 + a.n2*b.n1 + a.n3*b.n0⟩

def phaseRotate (a : Raw) : Raw := ⟨a.n3, a.n0, a.n1, a.n2⟩
def phaseUnrotate (a : Raw) : Raw := phaseRotate (phaseRotate (phaseRotate a))
def opposite (a : Raw) : Raw := phaseRotate (phaseRotate a)
def augmentation (a : Raw) : ℤ := a.n0 + a.n1 + a.n2 + a.n3
def gamma (a : Raw) : Residual := ((a.n0 : ℤ) - a.n2, (a.n1 : ℤ) - a.n3)
def c0 : Raw := merge e0 e2
def c1 : Raw := merge e1 e3

theorem merge_assoc (a b c : Raw) : merge (merge a b) c = merge a (merge b c) := by
  ext <;> simp [merge, Nat.add_assoc]

theorem merge_comm (a b : Raw) : merge a b = merge b a := by
  ext <;> simp [merge, Nat.add_comm]

@[simp] theorem merge_empty (a : Raw) : merge a empty = a := by
  ext <;> simp [merge, empty]

@[simp] theorem empty_merge (a : Raw) : merge empty a = a := by
  rw [merge_comm, merge_empty]

/-- Raw merge is cancellative without identifying any nonempty bag with empty. -/
theorem merge_cancellative (a b c : Raw) (h : merge a c = merge b c) : a = b := by
  have h0 := congrArg Raw.n0 h
  have h1 := congrArg Raw.n1 h
  have h2 := congrArg Raw.n2 h
  have h3 := congrArg Raw.n3 h
  ext <;> simp only [merge] at h0 h1 h2 h3 <;> omega

theorem serial_assoc (a b c : Raw) : serial (serial a b) c = serial a (serial b c) := by
  ext <;> dsimp [serial] <;> ring

theorem serial_comm (a b : Raw) : serial a b = serial b a := by
  ext <;> dsimp [serial] <;> ring

@[simp] theorem serial_unit (a : Raw) : serial a e0 = a := by
  ext <;> simp [serial, e0]

@[simp] theorem unit_serial (a : Raw) : serial e0 a = a := by
  rw [serial_comm, serial_unit]

@[simp] theorem serial_empty (a : Raw) : serial a empty = empty := by
  ext <;> simp [serial, empty]

@[simp] theorem empty_serial (a : Raw) : serial empty a = empty := by
  rw [serial_comm, serial_empty]

theorem serial_merge (a b c : Raw) :
    serial a (merge b c) = merge (serial a b) (serial a c) := by
  ext <;> dsimp [serial, merge] <;> ring

theorem merge_serial (a b c : Raw) :
    serial (merge a b) c = merge (serial a c) (serial b c) := by
  rw [serial_comm, serial_merge, serial_comm c a, serial_comm c b]

theorem augmentation_merge (a b : Raw) :
    augmentation (merge a b) = augmentation a + augmentation b := by
  simp only [augmentation, merge, Nat.cast_add]
  ring

theorem augmentation_serial (a b : Raw) :
    augmentation (serial a b) = augmentation a * augmentation b := by
  simp only [augmentation, serial, Nat.cast_add, Nat.cast_mul]
  ring

theorem gamma_merge (a b : Raw) : gamma (merge a b) = Native.merge (gamma a) (gamma b) := by
  apply Prod.ext <;> simp only [gamma, merge, Native.merge, Nat.cast_add] <;> ring

theorem gamma_serial (a b : Raw) : gamma (serial a b) = Native.serial (gamma a) (gamma b) := by
  apply Prod.ext <;> simp only [gamma, serial, Native.serial, Nat.cast_add, Nat.cast_mul] <;> ring

theorem phase_order_four (a : Raw) :
    phaseRotate (phaseRotate (phaseRotate (phaseRotate a))) = a := by
  rfl

theorem phase_inverse (a : Raw) :
    phaseUnrotate (phaseRotate a) = a ∧ phaseRotate (phaseUnrotate a) = a := by
  exact ⟨phase_order_four a, phase_order_four a⟩

theorem phase_merge (a b : Raw) :
    phaseRotate (merge a b) = merge (phaseRotate a) (phaseRotate b) := rfl

theorem gamma_phase (a : Raw) : gamma (phaseRotate a) = Native.rotate (gamma a) := by
  apply Prod.ext
  · dsimp [gamma, phaseRotate, Native.rotate]
    ring
  · rfl

theorem serial_phase (a : Raw) : serial a e1 = phaseRotate a := by
  ext <;> simp [serial, e1, phaseRotate]

theorem gamma_opposite (a : Raw) : gamma (opposite a) = Native.inverseToken (gamma a) := by
  apply Prod.ext <;> dsimp [gamma, opposite, phaseRotate, Native.inverseToken]
  all_goals ring

/-- Serial inverses are phase inverses; they are not additive antipodes. -/
theorem singleton_serial_inverses :
    serial e0 e0 = e0 ∧ serial e1 e3 = e0 ∧ serial e2 e2 = e0 ∧
      serial e3 e1 = e0 := by
  decide

theorem sequential_identity_not_empty : e0 ≠ empty := by decide
theorem antipodal_pair_not_empty : c0 ≠ empty := by decide
theorem phase_inverse_not_opposite : e0 ≠ opposite e0 := by decide

/-- A positive serial-dark control retaining raw augmentation information. -/
def weight (a : Raw) : ℤ := augmentation a * Native.quadratic (gamma a)

theorem weight_nonnegative (a : Raw) : 0 ≤ weight a := by
  apply mul_nonneg
  · dsimp [augmentation]
    positivity
  · exact Native.quadratic_nonnegative _

@[simp] theorem weight_empty : weight empty = 0 := by
  norm_num [weight, augmentation, gamma, empty, Native.quadratic]

theorem weight_singletons : weight e0 = 1 ∧ weight e1 = 1 ∧
    weight e2 = 1 ∧ weight e3 = 1 := by
  norm_num [weight, augmentation, gamma, e0, e1, e2, e3, Native.quadratic]

theorem augmentation_phase (a : Raw) : augmentation (phaseRotate a) = augmentation a := by
  dsimp [augmentation, phaseRotate]
  ring

theorem weight_phase (a : Raw) : weight (phaseRotate a) = weight a := by
  simp only [weight, augmentation_phase, gamma_phase, Native.quadratic_rotation]

theorem weight_serial (a b : Raw) : weight (serial a b) = weight a * weight b := by
  simp only [weight, augmentation_serial, gamma_serial, Native.quadratic_serial]
  ring

@[simp] theorem gamma_c0 : gamma c0 = (0, 0) := by decide
@[simp] theorem gamma_c1 : gamma c1 = (0, 0) := by decide
@[simp] theorem weight_c0 : weight c0 = 0 := by decide
@[simp] theorem weight_c1 : weight c1 = 0 := by decide

theorem antipodal_pairs_serial_dark (L R : Raw) :
    weight (serial (serial L c0) R) = 0 ∧ weight (serial (serial L c1) R) = 0 := by
  simp [weight_serial]

theorem insertion_c0 (a : Raw) :
    weight (merge a c0) = weight a + 2 * Native.quadratic (gamma a) := by
  rw [weight, augmentation_merge, gamma_merge, gamma_c0]
  norm_num [augmentation, c0, merge, e0, e2, Native.merge]
  simp only [weight, augmentation]
  ring

theorem insertion_c1 (a : Raw) :
    weight (merge a c1) = weight a + 2 * Native.quadratic (gamma a) := by
  rw [weight, augmentation_merge, gamma_merge, gamma_c1]
  norm_num [augmentation, c1, merge, e1, e3, Native.merge]
  simp only [weight, augmentation]
  ring

theorem coherent_reference_separates_dark_pair :
    weight e0 = 1 ∧ weight (merge e0 c0) = 3 := by decide

theorem weight_does_not_factor : ¬ ∃ f : Residual → ℤ, ∀ a, weight a = f (gamma a) := by
  rintro ⟨f, hf⟩
  have h := (hf e0).trans ((hf (merge e0 c0)).symm)
  norm_num [weight, augmentation, gamma, e0, e2, c0, merge, Native.quadratic] at h

/-- Two coherent references distinguish all four singleton phases. -/
theorem phase_sensitive_reference_table :
    (weight (merge e0 e0), weight (merge e0 e1)) = (8, 4) ∧
    (weight (merge e1 e0), weight (merge e1 e1)) = (4, 8) ∧
    (weight (merge e2 e0), weight (merge e2 e1)) = (0, 4) ∧
    (weight (merge e3 e0), weight (merge e3 e1)) = (4, 0) := by decide

theorem equal_unit_third_difference :
    weight (merge (merge e0 e0) e0) - 3 * weight (merge e0 e0) +
      3 * weight e0 - weight empty = 6 := by decide

/-- Exact observational pair-erasure, an additional bridge rather than darkness. -/
def PairErasure {B : Type*} (F : Raw → B) : Prop :=
  (∀ a, F (merge a c0) = F a) ∧ (∀ a, F (merge a c1) = F a)

def ResidualInvariant {B : Type*} (F : Raw → B) : Prop :=
  ∀ a b, gamma a = gamma b → F a = F b

def balanced (a b : ℕ) : Raw := ⟨a, b, a, b⟩

theorem gamma_zero_iff_balanced (a : Raw) :
    gamma a = (0, 0) ↔ a = balanced a.n0 a.n1 := by
  constructor
  · intro h
    have h0 := congrArg Prod.fst h
    have h1 := congrArg Prod.snd h
    dsimp [gamma] at h0 h1
    ext <;> dsimp [balanced] <;> omega
  · intro h
    rw [h]
    simp [gamma, balanced]

theorem erase_balanced {B : Type*} (F : Raw → B) (h : PairErasure F)
    (n : Raw) (a b : ℕ) : F (merge n (balanced a b)) = F n := by
  induction a with
  | zero =>
    induction b with
    | zero => simp [balanced, merge]
    | succ b ih =>
      have heq : balanced 0 (b + 1) = merge (balanced 0 b) c1 := by
        ext <;> simp [balanced, merge, c1, e1, e3]
      rw [heq, ← merge_assoc, h.2, ih]
  | succ a ih =>
    have heq : balanced (a + 1) b = merge (balanced a b) c0 := by
      ext <;> simp [balanced, merge, c0, e0, e2]
    rw [heq, ← merge_assoc, h.1, ih]

theorem erase_null {B : Type*} (F : Raw → B) (h : PairErasure F)
    (n z : Raw) (hz : gamma z = (0, 0)) : F (merge n z) = F n := by
  rw [(gamma_zero_iff_balanced z).mp hz]
  exact erase_balanced F h n _ _

theorem pair_erasure_iff_residual_invariant {B : Type*} (F : Raw → B) :
    PairErasure F ↔ ResidualInvariant F := by
  constructor
  · intro h n m hnm
    have hm : gamma (merge m (opposite m)) = (0, 0) := by
      rw [gamma_merge, gamma_opposite]
      apply Prod.ext <;> simp [Native.merge, Native.inverseToken]
    have hn : gamma (merge n (opposite m)) = (0, 0) := by
      rw [gamma_merge, hnm, gamma_opposite]
      apply Prod.ext <;> simp [Native.merge, Native.inverseToken]
    calc
      F n = F (merge n (merge m (opposite m))) := (erase_null F h n _ hm).symm
      _ = F (merge m (merge n (opposite m))) := by
        rw [← merge_assoc, merge_comm n m, merge_assoc]
      _ = F m := erase_null F h m _ hn
  · intro h
    constructor <;> intro n <;> apply h <;>
      simp [gamma_merge, Native.merge]

/-- Explicit representatives show the residual map is onto all integer pairs. -/
def representative (z : Residual) : Raw :=
  ⟨z.1.toNat, z.2.toNat, (-z.1).toNat, (-z.2).toNat⟩

theorem gamma_representative (z : Residual) : gamma (representative z) = z := by
  apply Prod.ext <;> dsimp [gamma, representative] <;> omega

theorem gamma_surjective : Function.Surjective gamma := fun z =>
  ⟨representative z, gamma_representative z⟩

theorem residual_invariant_iff_unique_factor {B : Type*} (F : Raw → B) :
    ResidualInvariant F ↔ ∃! f : Residual → B, ∀ n, F n = f (gamma n) := by
  constructor
  · intro h
    let f : Residual → B := fun z => F (representative z)
    have hf (n : Raw) : F n = f (gamma n) :=
      h n (representative (gamma n)) (gamma_representative _).symm
    refine ⟨f, hf, ?_⟩
    intro g hg
    funext z
    calc
      g z = g (gamma (representative z)) := by rw [gamma_representative]
      _ = F (representative z) := (hg _).symm
      _ = f z := rfl
  · rintro ⟨f, hf, _⟩ n m hnm
    rw [hf, hf, hnm]

/-- No positivity, probability, quadraticity, or serial assumption is required. -/
theorem pair_erasure_iff_unique_factor {B : Type*} (F : Raw → B) :
    PairErasure F ↔ ∃! f : Residual → B, ∀ n, F n = f (gamma n) := by
  rw [pair_erasure_iff_residual_invariant, residual_invariant_iff_unique_factor]

/-- Exactly the supplied finite polynomial merge/serial contexts. The hole may
occur repeatedly; no statement about all physically accessible contexts is made. -/
inductive CoherentContext where
  | hole
  | constant (value : Raw)
  | parallel (left right : CoherentContext)
  | sequential (left right : CoherentContext)

def CoherentContext.eval : CoherentContext → Raw → Raw
  | .hole, n => n
  | .constant value, _ => value
  | .parallel left right, n => merge (left.eval n) (right.eval n)
  | .sequential left right, n => serial (left.eval n) (right.eval n)

theorem context_respects_residual (C : CoherentContext) (n m : Raw)
    (h : gamma n = gamma m) : gamma (C.eval n) = gamma (C.eval m) := by
  induction C with
  | hole => exact h
  | constant _ => rfl
  | parallel left right hl hr =>
    simp only [CoherentContext.eval, gamma_merge, hl, hr]
  | sequential left right hl hr =>
    simp only [CoherentContext.eval, gamma_serial, hl, hr]

theorem context_respects_augmentation (C : CoherentContext) (n m : Raw)
    (h : augmentation n = augmentation m) :
    augmentation (C.eval n) = augmentation (C.eval m) := by
  induction C with
  | hole => exact h
  | constant _ => rfl
  | parallel left right hl hr =>
    simp only [CoherentContext.eval, augmentation_merge, hl, hr]
  | sequential left right hl hr =>
    simp only [CoherentContext.eval, augmentation_serial, hl, hr]

/-- The raw grammar admits both observational congruences; neither refines the
other. Selecting the residual congruence requires additional observational input. -/
theorem residual_and_augmentation_incomparable :
    (gamma c0 = gamma empty ∧ augmentation c0 ≠ augmentation empty) ∧
      (augmentation e0 = augmentation e1 ∧ gamma e0 ≠ gamma e1) := by decide

/-- Once pair-erasure is supplied, it is stable throughout this exact grammar. -/
theorem pair_erasure_in_coherent_context {B : Type*} (F : Raw → B)
    (h : PairErasure F) (C : CoherentContext) (n : Raw) :
    F (C.eval (merge n c0)) = F (C.eval n) ∧
      F (C.eval (merge n c1)) = F (C.eval n) := by
  have hf := (pair_erasure_iff_residual_invariant F).mp h
  constructor <;> apply hf <;> apply context_respects_residual <;>
    simp [gamma_merge, Native.merge]

/-- Conversely, contextual erasure includes the bare insertion context. -/
theorem contextual_erasure_iff_pair_erasure {B : Type*} (F : Raw → B) :
    (∀ C : CoherentContext, ∀ n,
      F (C.eval (merge n c0)) = F (C.eval n) ∧
        F (C.eval (merge n c1)) = F (C.eval n)) ↔ PairErasure F := by
  constructor
  · intro h
    exact ⟨fun n => (h .hole n).1, fun n => (h .hole n).2⟩
  · intro h C n
    exact pair_erasure_in_coherent_context F h C n

theorem serial_darkness_does_not_imply_pair_erasure : ¬ PairErasure weight := by
  intro h
  obtain ⟨f, hf, _⟩ := (pair_erasure_iff_unique_factor weight).mp h
  exact weight_does_not_factor ⟨f, hf⟩

/-- This is coherent bag additivity, not additivity over exclusive outcomes. -/
theorem nonnegative_additive_response_cannot_erase_unit_pair
    (F : Raw → ℤ) (hnonnegative : ∀ a, 0 ≤ F a)
    (hadd : ∀ a b, F (merge a b) = F a + F b) (hunit : F e0 = 1) :
    ¬ PairErasure F := by
  intro h
  have hzero : F empty = 0 := by
    have hh := hadd empty empty
    simp only [empty_merge] at hh
    omega
  have hc : F c0 = 0 := by
    have hh := h.1 empty
    simpa [hzero] using hh
  have ha := hadd e0 e2
  have hn := hnonnegative e2
  change F c0 = _ at ha
  omega

/-- Reversible merge translation is a distinct, explicitly additive bridge. -/
theorem reversible_merge_translation_iff (a b : Residual) :
    (∀ s, Native.merge b (Native.merge a s) = s) ↔ Native.merge a b = (0, 0) := by
  constructor
  · intro h
    have hh := h (0, 0)
    apply Prod.ext
    · have hx := congrArg Prod.fst hh
      dsimp [Native.merge] at hx ⊢
      omega
    · have hy := congrArg Prod.snd hh
      dsimp [Native.merge] at hy ⊢
      omega
  · intro h s
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    apply Prod.ext <;> dsimp [Native.merge] at hx hy ⊢ <;> omega

inductive BoundaryRole where
  | supplied | proved | openBridge | excludedInference
  deriving DecidableEq

/-- Data-only boundary ledger; it grants no scientific proof-status upgrade. -/
def boundaryLedger : List (BoundaryRole × String) :=
  [ (.supplied, "Raw finite bags, merge, cyclic serial convolution and C4 syntax."),
    (.proved, "Raw merge cancellation and serial phase undo coexist with nonempty antipodal bags."),
    (.proved, "Positive calibrated C4-invariant serial-multiplicative weight has serial-dark antipodal pairs but reference-sensitive insertion."),
    (.proved, "Pair insertion erasure is exactly arbitrary-codomain unique factorization through the integer residual map."),
    (.openBridge, "Antipodal pair insertion is observationally equivalent to empty in every accessible coherent reference and continuation context."),
    (.excludedInference, "Terminal or serial darkness, serial undo, and merge injectivity do not supply contextual antipodal erasure."),
    (.excludedInference, "No Born, QM, physical detector, or unique observational quotient follows from the raw grammar.") ]

end IDT.QMClosure.SequentialUndoCancellationBoundary
