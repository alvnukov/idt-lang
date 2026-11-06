import Proofs.QMClosure.MedialSwapRoot
import Proofs.QMClosure.OperationalQuadraticReconstruction
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Quot
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace IDT.QMClosure.MedialSwapRoot.Localization

/-!
Injective-port localization for the raw reconstruction stage. Fractions are
preparations with a nonnegative denominator power of the injective endomorphism
H = A ∘ B. No additive or scalar structure is supplied to this construction.
-/

variable {V : Type*} [Zero V] {m : V → V → V} (h : Laws m)

def pow (n : ℕ) (x : V) : V := (portH m)^[n] x

include h in
theorem pow_zero (n : ℕ) : pow (m := m) n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [pow, Function.iterate_succ_apply', portH_zero h] using
      congrArg (portH m) ih

include h in
theorem pow_map (n : ℕ) (x y : V) :
    pow (m := m) n (m x y) = m (pow (m := m) n x) (pow (m := m) n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, portH_map h]

theorem pow_add (n k : ℕ) (x : V) :
    pow (m := m) n (pow (m := m) k x) = pow (m := m) (n + k) x :=
  (Function.iterate_add_apply _ _ _ _).symm

def Rel (p q : V × ℕ) : Prop :=
  pow (m := m) q.2 p.1 = pow (m := m) p.2 q.1

include h in
theorem rel_trans {p q r : V × ℕ} (hpq : Rel (m := m) p q)
    (hqr : Rel (m := m) q r) : Rel (m := m) p r := by
  apply ((portH_injective h).iterate q.2)
  change pow (m := m) q.2 (pow (m := m) r.2 p.1) =
    pow (m := m) q.2 (pow (m := m) p.2 r.1)
  have hh₁ := congrArg (pow (m := m) r.2) hpq
  have hh₂ := congrArg (pow (m := m) p.2) hqr
  simp only [pow_add] at hh₁ hh₂ ⊢
  calc
    _ = pow (m := m) (r.2 + q.2) p.1 := by rw [Nat.add_comm q.2]
    _ = pow (m := m) (r.2 + p.2) q.1 := hh₁
    _ = pow (m := m) (p.2 + r.2) q.1 := by rw [Nat.add_comm r.2]
    _ = pow (m := m) (p.2 + q.2) r.1 := hh₂
    _ = _ := by rw [Nat.add_comm p.2]

def setoid : Setoid (V × ℕ) where
  r := Rel (m := m)
  iseqv := ⟨fun _ => rfl, fun hh => hh.symm, rel_trans h⟩

def Carrier := Quotient (setoid h)

def mk (x : V) (n : ℕ) : Carrier h := Quotient.mk _ (x, n)
def embed (x : V) : Carrier h := mk h x 0

instance : Zero (Carrier h) := ⟨embed h 0⟩

theorem embed_injective : Function.Injective (embed h) := by
  intro x y heq
  exact Quotient.exact heq

theorem mk_raise (x : V) (n k : ℕ) :
    mk h (pow (m := m) k x) (n + k) = mk h x n := by
  apply Quotient.sound
  exact pow_add n k x

theorem mk_promote (x : V) (n N : ℕ) (hle : n ≤ N) :
    mk h (pow (m := m) (N - n) x) N = mk h x n := by
  have hn : n + (N - n) = N := Nat.add_sub_of_le hle
  simpa only [hn] using mk_raise h x n (N - n)

def mixRep (p q : V × ℕ) : V × ℕ :=
  (m (pow (m := m) q.2 p.1) (pow (m := m) p.2 q.1), p.2 + q.2)

include h in
theorem mixRep_respects {p p' q q' : V × ℕ}
    (hp : Rel (m := m) p p') (hq : Rel (m := m) q q') :
    Rel (m := m) (mixRep (m := m) p q) (mixRep (m := m) p' q') := by
  change pow (m := m) (p'.2 + q'.2)
      (m (pow (m := m) q.2 p.1) (pow (m := m) p.2 q.1)) =
    pow (m := m) (p.2 + q.2)
      (m (pow (m := m) q'.2 p'.1) (pow (m := m) p'.2 q'.1))
  rw [pow_map h, pow_map h]
  apply congrArg₂ m
  · have hh := congrArg (pow (m := m) (q.2 + q'.2)) hp
    simpa only [pow_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  · have hh := congrArg (pow (m := m) (p.2 + p'.2)) hq
    simpa only [pow_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

def mix : Carrier h → Carrier h → Carrier h :=
  Quotient.map₂ (mixRep (m := m)) (fun {_ _} hp {_ _} hq => mixRep_respects h hp hq)

theorem mix_mk (x y : V) (n k : ℕ) :
    mix h (mk h x n) (mk h y k) =
      mk h (m (pow (m := m) k x) (pow (m := m) n y)) (n + k) := rfl

theorem mix_same (x y : V) (n : ℕ) :
    mix h (mk h x n) (mk h y n) = mk h (m x y) n := by
  rw [mix_mk, ← pow_map h]
  exact mk_raise h (m x y) n n

theorem embed_mix (x y : V) : mix h (embed h x) (embed h y) = embed h (m x y) := rfl

theorem embed_portA (x : V) : embed h (portA m x) = portA (mix h) (embed h x) := rfl
theorem embed_portB (x : V) : embed h (portB m x) = portB (mix h) (embed h x) := rfl

theorem embed_inverseATerm (x : V) :
    embed h (inverseATerm m x) = inverseATerm (mix h) (embed h x) := rfl

theorem zero_mk (n : ℕ) : (0 : Carrier h) = mk h 0 n := by
  have hh := mk_raise h 0 0 n
  simpa only [Nat.zero_add, pow_zero h] using hh.symm

theorem laws : Laws (mix h) where
  idempotent p := by
    induction p using Quotient.inductionOn with
    | _ p =>
      change mix h (mk h p.1 p.2) (mk h p.1 p.2) = mk h p.1 p.2
      rw [mix_same, h.idempotent]
  medial p q r s := by
    induction p using Quotient.inductionOn with
    | _ p =>
      induction q using Quotient.inductionOn with
      | _ q =>
        induction r using Quotient.inductionOn with
        | _ r =>
          induction s using Quotient.inductionOn with
          | _ s =>
            let N := p.2 + q.2 + r.2 + s.2
            have hp := mk_promote h p.1 p.2 N (by dsimp [N]; omega)
            have hq := mk_promote h q.1 q.2 N (by dsimp [N]; omega)
            have hr := mk_promote h r.1 r.2 N (by dsimp [N]; omega)
            have hs := mk_promote h s.1 s.2 N (by dsimp [N]; omega)
            change mix h (mix h (mk h p.1 p.2) (mk h q.1 q.2))
                (mix h (mk h r.1 r.2) (mk h s.1 s.2)) =
              mix h (mix h (mk h p.1 p.2) (mk h r.1 r.2))
                (mix h (mk h q.1 q.2) (mk h s.1 s.2))
            rw [← hp, ← hq, ← hr, ← hs]
            simp only [mix_same, h.medial]
  bookend p q := by
    induction p using Quotient.inductionOn with
    | _ p =>
      induction q using Quotient.inductionOn with
      | _ q =>
        let N := p.2 + q.2
        have hp := mk_promote h p.1 p.2 N (by dsimp [N]; omega)
        have hq := mk_promote h q.1 q.2 N (by dsimp [N]; omega)
        change mix h (mix h (mk h p.1 p.2) (mk h q.1 q.2))
            (mix h (mk h q.1 q.2) (mk h p.1 p.2)) = mk h q.1 q.2
        rw [← hp, ← hq]
        simp only [mix_same, h.bookend]

theorem portA_mk (x : V) (n : ℕ) :
    portA (mix h) (mk h x n) = mk h (portA m x) n := by
  change mix h (mk h x n) 0 = _
  rw [zero_mk h n, mix_same]
  rfl

theorem portB_mk (x : V) (n : ℕ) :
    portB (mix h) (mk h x n) = mk h (portB m x) n := by
  change mix h 0 (mk h x n) = _
  rw [zero_mk h n, mix_same]
  rfl

theorem portH_mk (x : V) (n : ℕ) :
    portH (mix h) (mk h x n) = mk h (portH m x) n := by
  simp only [portH, portA_mk, portB_mk]

def shift : Carrier h → Carrier h :=
  Quotient.map (fun p => (p.1, p.2 + 1)) (by
    intro p q hpq
    change pow (m := m) (q.2 + 1) p.1 = pow (m := m) (p.2 + 1) q.1
    have hh := congrArg (portH m) hpq
    simpa only [pow, Function.iterate_succ_apply'] using hh)

theorem shift_mk (x : V) (n : ℕ) : shift h (mk h x n) = mk h x (n + 1) := rfl

theorem portH_shift (p : Carrier h) : portH (mix h) (shift h p) = p := by
  induction p using Quotient.inductionOn with
  | _ p =>
    rw [show (Quotient.mk (setoid h) p : Carrier h) = mk h p.1 p.2 from rfl,
      shift_mk, portH_mk]
    exact mk_raise h p.1 p.2 1

theorem portA_bijective : Function.Bijective (portA (mix h)) := by
  refine ⟨portA_injective (laws h), ?_⟩
  intro p
  exact ⟨portB (mix h) (shift h p), portH_shift h p⟩

theorem portB_bijective : Function.Bijective (portB (mix h)) := by
  refine ⟨portB_injective (laws h), ?_⟩
  intro p
  refine ⟨portA (mix h) (shift h p), ?_⟩
  rw [← ports_commute (laws h)]
  exact portH_shift h p

/-- The inverse term is established in the isotope, not by evaluating selected
complex coefficients. The coefficients are the reconstructed endomorphisms. -/
theorem localized_inverseATerm (p : Carrier h) :
    portA (mix h) (inverseATerm (mix h) p) = p := by
  let raw := laws h
  let ba := portA_bijective h
  let bb := portB_bijective h
  letI := isotopeMonoid (raw.idempotent 0) raw.medial ba bb
  let T := isotopeOperation (raw.idempotent 0) raw.medial ba bb
  let A : AddMonoid.End (Carrier h) := TransparentSwapRoot.portA T
  let B : AddMonoid.End (Carrier h) := TransparentSwapRoot.portB T
  have lin (x y : Carrier h) : mix h x y = A x + B y := by
    exact mixer_eq_isotope ba bb x y
  have tr : A + B = 1 := by
    apply AddMonoidHom.ext
    intro x
    change A x + B x = x
    rw [← lin]
    exact raw.idempotent x
  have reconstruction :=
    (bijective_port_reconstruction raw ba bb).1
  have cr : A * B + B * A = 1 := by
    apply AddMonoidHom.ext
    exact reconstruction.cross
  change A (inverseATerm (mix h) p) = p
  rw [inverseATerm_eq_doubleB A B lin tr cr, map_add]
  exact reconstruction.halves p

end IDT.QMClosure.MedialSwapRoot.Localization

namespace IDT.QMClosure.MedialSwapRoot

variable {V : Type*} [Zero V] {m : V → V → V} (h : Laws m)

include h

/-- Original-carrier surjectivity is reflected through the injective raw-term
embedding. Port bijectivity is a conclusion, not an input assumption. -/
theorem portA_inverseATerm (x : V) : portA m (inverseATerm m x) = x := by
  apply Localization.embed_injective h
  rw [Localization.embed_portA, Localization.embed_inverseATerm]
  exact Localization.localized_inverseATerm h (Localization.embed h x)

theorem portB_inverseBTerm (x : V) : portB m (inverseBTerm m x) = x :=
  portA_inverseATerm (oppositeLaws h) x

theorem inverseATerm_portA (x : V) : inverseATerm m (portA m x) = x := by
  apply portA_injective h
  exact portA_inverseATerm h (portA m x)

theorem inverseBTerm_portB (x : V) : inverseBTerm m (portB m x) = x := by
  apply portB_injective h
  exact portB_inverseBTerm h (portB m x)

theorem raw_portA_bijective : Function.Bijective (portA m) :=
  ⟨portA_injective h, fun x => ⟨inverseATerm m x, portA_inverseATerm h x⟩⟩

theorem raw_portB_bijective : Function.Bijective (portB m) :=
  ⟨portB_injective h, fun x => ⟨inverseBTerm m x, portB_inverseBTerm h x⟩⟩

@[reducible] noncomputable def canonicalMonoid : AddCommMonoid V :=
  isotopeMonoid (h.idempotent 0) h.medial (raw_portA_bijective h) (raw_portB_bijective h)

def canonicalAdd (m : V → V → V) (x y : V) : V :=
  m (inverseATerm m x) (inverseBTerm m y)

theorem canonical_add_raw (x y : V) :
    letI := canonicalMonoid h
    x + y = canonicalAdd m x y := by
  change isotopeAdd (raw_portA_bijective h) (raw_portB_bijective h) x y = _
  have ha : (equivA (raw_portA_bijective h)).symm x = inverseATerm m x := by
    apply portA_injective h
    exact ((equivA (raw_portA_bijective h)).apply_symm_apply x).trans
      (portA_inverseATerm h x).symm
  have hb : (equivB (raw_portB_bijective h)).symm y = inverseBTerm m y := by
    apply portB_injective h
    exact ((equivB (raw_portB_bijective h)).apply_symm_apply y).trans
      (portB_inverseBTerm h y).symm
  simp only [isotopeAdd, canonicalAdd, ha, hb]

/-- Uniqueness is relative to the chosen vacuum. The competing addition is a
binary operation; no second additive typeclass instance is installed. -/
theorem canonical_add_unique (plus : V → V → V)
    (rightZero : ∀ x, plus x 0 = x) (leftZero : ∀ x, plus 0 x = x)
    (preserves : ∀ a b c d, m (plus a b) (plus c d) = plus (m a c) (m b d))
    (x y : V) : canonicalAdd m x y = plus x y := by
  have hh := preserves (inverseATerm m x) 0 0 (inverseBTerm m y)
  rw [rightZero, leftZero] at hh
  change canonicalAdd m x y = plus (portA m (inverseATerm m x))
    (portB m (inverseBTerm m y)) at hh
  simpa only [portA_inverseATerm h, portB_inverseBTerm h] using hh

noncomputable def canonicalOperation :
    letI := canonicalMonoid h
    (V × V) →+ (V × V) :=
  isotopeOperation (h.idempotent 0) h.medial (raw_portA_bijective h) (raw_portB_bijective h)

/-- Universal raw reconstruction. Input: only a chosen zero and three raw
operation equations. No additive structure or port bijectivity is assumed. -/
theorem raw_reconstruction :
    letI := canonicalMonoid h
    let T := canonicalOperation h
    TransparentSwapRoot.Reconstruction (TransparentSwapRoot.portA T)
      (TransparentSwapRoot.portB T) ∧
    (T : (V × V) → (V × V)) =
      PhaseMixerCancellation.mixer
        (TransparentSwapRoot.phase (TransparentSwapRoot.portA T))
        (TransparentSwapRoot.half (TransparentSwapRoot.portA T)
          (TransparentSwapRoot.portB T)) :=
  bijective_port_reconstruction h (raw_portA_bijective h) (raw_portB_bijective h)

noncomputable def canonicalPhase (x : V) : V :=
  letI := canonicalMonoid h
  TransparentSwapRoot.phase (TransparentSwapRoot.portA (canonicalOperation h)) x

noncomputable def canonicalHalf (x : V) : V :=
  letI := canonicalMonoid h
  TransparentSwapRoot.half (TransparentSwapRoot.portA (canonicalOperation h))
    (TransparentSwapRoot.portB (canonicalOperation h)) x

theorem canonical_phase_cancellation (x : V) :
    letI := canonicalMonoid h
    x + canonicalPhase h (canonicalPhase h x) = 0 := by
  letI := canonicalMonoid h
  exact (raw_reconstruction h).1.cancellation x

theorem canonical_phase_fourth (x : V) :
    canonicalPhase h (canonicalPhase h (canonicalPhase h (canonicalPhase h x))) = x := by
  letI := canonicalMonoid h
  exact (raw_reconstruction h).1.fourth x

theorem canonical_half_halves (x : V) :
    letI := canonicalMonoid h
    canonicalHalf h x + canonicalHalf h x = x := by
  letI := canonicalMonoid h
  exact (raw_reconstruction h).1.halves x

/-- Additive inverses are constructed from the reconstructed phase. -/
@[reducible] noncomputable def canonicalGroup : AddCommGroup V := by
  letI := canonicalMonoid h
  letI : Neg V := ⟨fun x => canonicalPhase h (canonicalPhase h x)⟩
  exact {
    canonicalMonoid h with
    neg := fun x => canonicalPhase h (canonicalPhase h x)
    zsmul := zsmulRec
    neg_add_cancel := fun x => by
      change canonicalPhase h (canonicalPhase h x) + x = 0
      rw [add_comm]
      exact canonical_phase_cancellation h x }

theorem canonical_phase_square_neg (x : V) :
    letI := canonicalGroup h
    canonicalPhase h (canonicalPhase h x) = -x := rfl

/-- Full-domain positive conserved readout transfers to the existing quadratic
reconstruction theorem after the addition has been derived from the raw laws.
The readout, its positivity and its full-domain conservation remain inputs. -/
theorem raw_positive_readout (W : V → ℝ) (vacuum : W 0 = 0)
    (positive : ∀ x, 0 ≤ W x)
    (conserve : ∀ x y, W (m x y) + W (m y x) = W x + W y) :
    letI := canonicalMonoid h
    OperationalQuadraticReconstruction.Reconstruction (canonicalOperation h) W := by
  letI := canonicalMonoid h
  have tr : ∀ x, canonicalOperation h (x, x) = (x, x) :=
    fun x => Prod.ext (h.idempotent x) (h.idempotent x)
  have sq : ∀ p, canonicalOperation h (canonicalOperation h p) = p.swap :=
    fun p => Prod.ext (h.bookend p.1 p.2) (h.bookend p.2 p.1)
  exact OperationalQuadraticReconstruction.reconstruct_positive_operation
    (canonicalOperation h) tr sq W vacuum positive conserve

inductive RawReconstructionBoundary
  | chosenVacuumInput
  | idempotenceInput
  | medialWholePreparationEqualityInput
  | bookendRootInput
  | derivedPortBijections
  | derivedAdditiveMonoid
  | derivedHalfAndPhaseAndInverses
  | physicalJustificationOpen
  | actualizationOpen
  | fullQMOpen
  deriving DecidableEq, Repr

def rawReconstructionBoundary : List RawReconstructionBoundary :=
  [.chosenVacuumInput, .idempotenceInput, .medialWholePreparationEqualityInput,
    .bookendRootInput, .derivedPortBijections, .derivedAdditiveMonoid,
    .derivedHalfAndPhaseAndInverses, .physicalJustificationOpen,
    .actualizationOpen, .fullQMOpen]

end IDT.QMClosure.MedialSwapRoot

namespace IDT.QMClosure.MedialSwapRoot.DiagonalNormalization

/-!
The diagonal normalization is a mathematical normal form. Its existence does
not establish an experimentally available unary diagonal operation, copying of
an unknown preparation, or additivity of the original operation at the chosen
vacuum. In particular the original diagonal need not fix that vacuum.
-/

structure Laws {V : Type*} (m : V → V → V) : Prop where
  medial : ∀ a b c d, m (m a b) (m c d) = m (m a c) (m b d)
  bookend : ∀ x y, m (m x y) (m y x) = y

variable {V : Type*} {m : V → V → V} (h : Laws m)

def diagonal (m : V → V → V) (x : V) : V := m x x
def normalized (m : V → V → V) (x y : V) : V := diagonal m (m x y)

include h

theorem diagonal_involutive (x : V) : diagonal m (diagonal m x) = x :=
  h.bookend x x

theorem diagonal_map (x y : V) :
    diagonal m (m x y) = m (diagonal m x) (diagonal m y) :=
  h.medial x y x y

theorem normalized_pair (a b c d : V) :
    normalized m (normalized m a b) (normalized m c d) = m (m a b) (m c d) := by
  change diagonal m (m (diagonal m (m a b)) (diagonal m (m c d))) = _
  rw [← diagonal_map h, diagonal_involutive h]

def normalized_laws : MedialSwapRoot.Laws (normalized m) where
  idempotent := diagonal_involutive h
  medial a b c d := by
    rw [normalized_pair h, normalized_pair h, h.medial]
  bookend x y := by
    rw [normalized_pair h]
    exact h.bookend x y

omit h in
theorem diagonal_preserves_readout (W : V → ℝ)
    (conserves : ∀ x y, W (m x y) + W (m y x) = W x + W y) (x : V) :
    W (diagonal m x) = W x := by
  have hh := conserves x x
  change W (diagonal m x) + W (diagonal m x) = W x + W x at hh
  linarith

omit h in
theorem normalized_conserves_readout (W : V → ℝ)
    (conserves : ∀ x y, W (m x y) + W (m y x) = W x + W y) (x y : V) :
    W (normalized m x y) + W (normalized m y x) = W x + W y := by
  simp only [normalized, diagonal_preserves_readout W conserves]
  exact conserves x y

/-- The group is reconstructed for the normalized operation. Its zero is the
chosen zero, irrespective of whether the original diagonal fixes that point. -/
@[reducible] noncomputable def normalizedGroup [Zero V] : AddCommGroup V :=
  canonicalGroup (normalized_laws h)

theorem normalized_positive_readout [Zero V] (W : V → ℝ)
    (vacuum : W 0 = 0) (positive : ∀ x, 0 ≤ W x)
    (conserve : ∀ x y, W (m x y) + W (m y x) = W x + W y) :
    letI := canonicalMonoid (normalized_laws h)
    OperationalQuadraticReconstruction.Reconstruction
      (canonicalOperation (normalized_laws h)) W :=
  raw_positive_readout (normalized_laws h) W vacuum positive
    (normalized_conserves_readout W conserve)

inductive Boundary
  | suppliedMedialWholePreparationEquality
  | suppliedBookendRoot
  | mathematicalDiagonalNormalForm
  | originalDiagonalNeedNotFixVacuum
  | physicalUnaryDiagonalControlOpen
  | unknownPreparationCopyingOpen
  | physicalJustificationOpen
  | actualizationOpen
  | fullQMOpen
  deriving DecidableEq, Repr

def boundary : List Boundary :=
  [.suppliedMedialWholePreparationEquality, .suppliedBookendRoot,
    .mathematicalDiagonalNormalForm, .originalDiagonalNeedNotFixVacuum,
    .physicalUnaryDiagonalControlOpen, .unknownPreparationCopyingOpen,
    .physicalJustificationOpen, .actualizationOpen, .fullQMOpen]

end IDT.QMClosure.MedialSwapRoot.DiagonalNormalization

namespace IDT.QMClosure.MedialSwapRoot.CompleteOperation

/-! End-to-end raw complete-operation front end. Symmetric channels and the
bookend law are conclusions of the exact root law. Diagonal transparency is
not needed for the mathematical normalized operation. -/

variable {V : Type*} [Zero V] (T : (V × V) → (V × V))
    (square : ∀ p, T (T p) = p.swap)
    (medial : ∀ a b c d, firstChannel T (firstChannel T a b) (firstChannel T c d) =
      firstChannel T (firstChannel T a c) (firstChannel T b d))

def normalizedLaws : MedialSwapRoot.Laws (DiagonalNormalization.normalized (firstChannel T)) :=
  DiagonalNormalization.normalized_laws
    ({ medial := medial, bookend := raw_operation_bookend T square } :
      DiagonalNormalization.Laws (firstChannel T))

@[reducible] noncomputable def group : AddCommGroup V :=
  canonicalGroup (normalizedLaws T square medial)

/-- Full-domain readout conservation is transported from the original complete
operation. The reconstructed quadratic readout is on its normalized carrier
addition; no physical availability of normalization is asserted. -/
theorem positive_readout (W : V → ℝ) (vacuum : W 0 = 0)
    (positive : ∀ x, 0 ≤ W x)
    (conserve : ∀ x y, W (T (x, y)).1 + W (T (x, y)).2 = W x + W y) :
    letI := canonicalMonoid (normalizedLaws T square medial)
    OperationalQuadraticReconstruction.Reconstruction
      (canonicalOperation (normalizedLaws T square medial)) W := by
  let h : DiagonalNormalization.Laws (firstChannel T) :=
    { medial := medial, bookend := raw_operation_bookend T square }
  exact DiagonalNormalization.normalized_positive_readout h W vacuum positive
    (raw_operation_conserves_readout T square W conserve)

end IDT.QMClosure.MedialSwapRoot.CompleteOperation
