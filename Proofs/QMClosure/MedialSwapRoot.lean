import Proofs.QMClosure.TransparentSwapRoot
import Mathlib.Logic.Equiv.Defs

namespace IDT.QMClosure.MedialSwapRoot

/-!
Raw preparation laws and the algebra they reconstruct. The input carrier has
only a chosen zero. Mediality is exact equality of complete preparations in
the row and column orders of a two-by-two mixing network. It is a substantial
operational law, not a consequence of locality or no-signalling.

The intermediate isotope construction below explicitly requires bijective
ports. Its existence alone does not discharge the raw reconstruction stage.
No physical inevitability, event actualization, or full QM is claimed.
-/

structure Laws {V : Type*} (m : V → V → V) : Prop where
  idempotent : ∀ x, m x x = x
  medial : ∀ a b c d, m (m a b) (m c d) = m (m a c) (m b d)
  bookend : ∀ x y, m (m x y) (m y x) = y

/-! The symmetric-channel presentation is derived from a complete raw
operation; the operation in this section is a function, not an additive map. -/
def firstChannel {V : Type*} (T : (V × V) → (V × V)) (x y : V) : V := (T (x, y)).1

theorem raw_operation_commutes_swap {V : Type*} (T : (V × V) → (V × V))
    (square : ∀ p, T (T p) = p.swap) (p : V × V) :
    T p.swap = (T p).swap := by
  calc
    _ = T (T (T p)) := congrArg T (square p).symm
    _ = _ := square (T p)

theorem raw_operation_eq_symmetric {V : Type*} (T : (V × V) → (V × V))
    (square : ∀ p, T (T p) = p.swap) (p : V × V) :
    T p = (firstChannel T p.1 p.2, firstChannel T p.2 p.1) := by
  apply Prod.ext
  · rfl
  · exact (congrArg Prod.fst (raw_operation_commutes_swap T square p)).symm

theorem raw_operation_bookend {V : Type*} (T : (V × V) → (V × V))
    (square : ∀ p, T (T p) = p.swap) (x y : V) :
    firstChannel T (firstChannel T x y) (firstChannel T y x) = y := by
  have hh := congrArg Prod.fst (square (x, y))
  rw [raw_operation_eq_symmetric T square (x, y)] at hh
  exact hh

theorem laws_of_complete_operation {V : Type*} (T : (V × V) → (V × V))
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap)
    (medial : ∀ a b c d, firstChannel T (firstChannel T a b) (firstChannel T c d) =
      firstChannel T (firstChannel T a c) (firstChannel T b d)) :
    Laws (firstChannel T) where
  idempotent x := congrArg Prod.fst (transparent x)
  medial := medial
  bookend := raw_operation_bookend T square

theorem raw_operation_conserves_readout {V R : Type*} [Add R]
    (T : (V × V) → (V × V)) (square : ∀ p, T (T p) = p.swap)
    (W : V → R)
    (conserve : ∀ x y, W (T (x, y)).1 + W (T (x, y)).2 = W x + W y) (x y : V) :
    W (firstChannel T x y) + W (firstChannel T y x) = W x + W y := by
  have hh := conserve x y
  rw [raw_operation_eq_symmetric T square (x, y)] at hh
  exact hh

section Raw
variable {V : Type*} [Zero V] {m : V → V → V}

def portA (m : V → V → V) (x : V) : V := m x 0
def portB (m : V → V → V) (x : V) : V := m 0 x
def portH (m : V → V → V) (x : V) : V := portA m (portB m x)

def inverseATerm (m : V → V → V) (x : V) : V :=
  let d := m (portB m x) x
  m (portB m d) (m d x)

def inverseBTerm (m : V → V → V) (x : V) : V :=
  inverseATerm (fun x y => m y x) x

theorem portA_zero (h : Laws m) : portA m 0 = 0 := h.idempotent 0
theorem portB_zero (h : Laws m) : portB m 0 = 0 := h.idempotent 0

theorem portA_map (h : Laws m) (x y : V) :
    portA m (m x y) = m (portA m x) (portA m y) := by
  change m (m x y) 0 = m (m x 0) (m y 0)
  calc
    _ = m (m x y) (m 0 0) := by rw [h.idempotent]
    _ = _ := h.medial x y 0 0

theorem portB_map (h : Laws m) (x y : V) :
    portB m (m x y) = m (portB m x) (portB m y) := by
  change m 0 (m x y) = m (m 0 x) (m 0 y)
  calc
    _ = m (m 0 0) (m x y) := by rw [h.idempotent]
    _ = _ := h.medial 0 0 x y

theorem ports_commute (h : Laws m) (x : V) :
    portA m (portB m x) = portB m (portA m x) := by
  change m (m 0 x) 0 = m 0 (m x 0)
  calc
    _ = m (m 0 x) (m 0 0) := by rw [h.idempotent]
    _ = m (m 0 0) (m x 0) := h.medial 0 x 0 0
    _ = _ := by rw [h.idempotent]

theorem portH_zero (h : Laws m) : portH m 0 = 0 := by
  simp only [portH, portB_zero h, portA_zero h]

theorem portH_map (h : Laws m) (x y : V) :
    portH m (m x y) = m (portH m x) (portH m y) := by
  simp only [portH, portB_map h, portA_map h]

theorem cross_ports (h : Laws m) (x y : V) :
    m (portB m x) (portA m y) = m (portB m y) (portA m x) := by
  exact h.medial 0 x y 0

theorem portA_injective (h : Laws m) : Function.Injective (portA m) := by
  intro x y heq
  let u := m x y
  let v := m y x
  have hx : m (portB m x) (portA m x) = x := h.bookend 0 x
  have hy : m (portB m y) (portA m y) = y := h.bookend 0 y
  have hx_cross : m (portB m x) (portA m y) = x := by rw [← heq]; exact hx
  have hy_cross : m (portB m y) (portA m x) = y := by rw [heq]; exact hy
  have hu : u = m (portB m u) (portA m v) := by
    calc
      u = m (m (portB m x) (portA m y))
          (m (portB m y) (portA m x)) := by rw [hx_cross, hy_cross]
      _ = m (m (portB m x) (portB m y))
          (m (portA m y) (portA m x)) := h.medial _ _ _ _
      _ = _ := by rw [← portB_map h, ← portA_map h]
  have hv : v = m (portB m v) (portA m u) := by
    calc
      v = m (m (portB m y) (portA m x))
          (m (portB m x) (portA m y)) := by rw [hy_cross, hx_cross]
      _ = m (m (portB m y) (portB m x))
          (m (portA m x) (portA m y)) := h.medial _ _ _ _
      _ = _ := by rw [← portB_map h, ← portA_map h]
  have huv : u = v := hu.trans ((cross_ports h u v).trans hv.symm)
  have hx' : x = u := by
    have hh := h.bookend y x
    change m v u = x at hh
    rw [← huv, h.idempotent] at hh
    exact hh.symm
  have hy' : y = u := by
    have hh := h.bookend x y
    change m u v = y at hh
    rw [← huv, h.idempotent] at hh
    exact hh.symm
  exact hx'.trans hy'.symm

def oppositeLaws (h : Laws m) : Laws (fun x y => m y x) where
  idempotent := h.idempotent
  medial a b c d := h.medial d c b a
  bookend x y := h.bookend x y

theorem portB_injective (h : Laws m) : Function.Injective (portB m) :=
  portA_injective (oppositeLaws h)

theorem portH_injective (h : Laws m) : Function.Injective (portH m) :=
  (portA_injective h).comp (portB_injective h)

end Raw

/-! A reusable intermediate theorem: a pointed medial magma with invertible
zero ports has a canonical commutative monoid isotope. -/
section Isotope
variable {V : Type*} [Zero V] {m : V → V → V}
variable (zero : m 0 0 = 0)
variable (medial : ∀ a b c d, m (m a b) (m c d) = m (m a c) (m b d))
variable (bijA : Function.Bijective (portA m))
variable (bijB : Function.Bijective (portB m))

noncomputable def equivA : V ≃ V := Equiv.ofBijective (portA m) bijA
noncomputable def equivB : V ≃ V := Equiv.ofBijective (portB m) bijB

noncomputable def isotopeAdd (x y : V) : V :=
  m ((equivA bijA).symm x) ((equivB bijB).symm y)

include zero medial

private theorem a_map (x y : V) :
    portA m (m x y) = m (portA m x) (portA m y) := by
  change m (m x y) 0 = m (m x 0) (m y 0)
  calc
    _ = m (m x y) (m 0 0) := by rw [zero]
    _ = _ := medial x y 0 0

private theorem b_map (x y : V) :
    portB m (m x y) = m (portB m x) (portB m y) := by
  change m 0 (m x y) = m (m 0 x) (m 0 y)
  calc
    _ = m (m 0 0) (m x y) := by rw [zero]
    _ = _ := medial 0 0 x y

private theorem ab_commute (x : V) : portA m (portB m x) = portB m (portA m x) := by
  change m (m 0 x) 0 = m 0 (m x 0)
  simpa only [zero] using medial 0 x 0 0

omit medial in
theorem equivA_symm_zero : (equivA bijA).symm 0 = 0 := by
  apply bijA.injective
  exact ((equivA bijA).apply_symm_apply 0).trans zero.symm

omit medial in
theorem equivB_symm_zero : (equivB bijB).symm 0 = 0 := by
  apply bijB.injective
  exact ((equivB bijB).apply_symm_apply 0).trans zero.symm

theorem equivA_symm_map (x y : V) :
    (equivA bijA).symm (m x y) =
      m ((equivA bijA).symm x) ((equivA bijA).symm y) := by
  apply bijA.injective
  rw [a_map zero medial]
  exact ((equivA bijA).apply_symm_apply (m x y)).trans
    (congrArg₂ m ((equivA bijA).apply_symm_apply x)
      ((equivA bijA).apply_symm_apply y)).symm

theorem equivB_symm_map (x y : V) :
    (equivB bijB).symm (m x y) =
      m ((equivB bijB).symm x) ((equivB bijB).symm y) := by
  apply bijB.injective
  rw [b_map zero medial]
  exact ((equivB bijB).apply_symm_apply (m x y)).trans
    (congrArg₂ m ((equivB bijB).apply_symm_apply x)
      ((equivB bijB).apply_symm_apply y)).symm

theorem inverse_ports_commute (x : V) :
    (equivA bijA).symm ((equivB bijB).symm x) =
      (equivB bijB).symm ((equivA bijA).symm x) := by
  apply bijB.injective
  apply bijA.injective
  have ea (z : V) : portA m ((equivA bijA).symm z) = z :=
    (equivA bijA).apply_symm_apply z
  have eb (z : V) : portB m ((equivB bijB).symm z) = z :=
    (equivB bijB).apply_symm_apply z
  rw [ab_commute zero medial, ea, eb, eb, ea]

omit medial in
theorem isotope_zero_add (x : V) : isotopeAdd bijA bijB 0 x = x := by
  simp only [isotopeAdd, equivA_symm_zero zero bijA]
  exact (equivB bijB).apply_symm_apply x

omit medial in
theorem isotope_add_zero (x : V) : isotopeAdd bijA bijB x 0 = x := by
  simp only [isotopeAdd, equivB_symm_zero zero bijB]
  exact (equivA bijA).apply_symm_apply x

theorem isotope_medial (a b c d : V) :
    isotopeAdd bijA bijB (isotopeAdd bijA bijB a b) (isotopeAdd bijA bijB c d) =
      isotopeAdd bijA bijB (isotopeAdd bijA bijB a c) (isotopeAdd bijA bijB b d) := by
  simp only [isotopeAdd, equivA_symm_map zero medial bijA,
    equivB_symm_map zero medial bijB]
  rw [medial, inverse_ports_commute zero medial bijA bijB b,
    inverse_ports_commute zero medial bijA bijB c]

theorem isotope_add_comm (x y : V) : isotopeAdd bijA bijB x y = isotopeAdd bijA bijB y x := by
  have h := isotope_medial zero medial bijA bijB 0 x y 0
  simpa only [isotope_zero_add zero bijA bijB, isotope_add_zero zero bijA bijB] using h

theorem isotope_add_assoc (x y z : V) :
    isotopeAdd bijA bijB (isotopeAdd bijA bijB x y) z =
      isotopeAdd bijA bijB x (isotopeAdd bijA bijB y z) := by
  have h := isotope_medial zero medial bijA bijB x y 0 z
  simpa only [isotope_zero_add zero bijA bijB, isotope_add_zero zero bijA bijB] using h

/-- The chosen zero is preserved literally; no additive structure is supplied. -/
@[reducible] noncomputable def isotopeMonoid : AddCommMonoid V := by
  letI : Add V := ⟨isotopeAdd bijA bijB⟩
  exact {
    add := isotopeAdd bijA bijB
    zero := 0
    add_assoc := isotope_add_assoc zero medial bijA bijB
    zero_add := isotope_zero_add zero bijA bijB
    add_zero := isotope_add_zero zero bijA bijB
    add_comm := isotope_add_comm zero medial bijA bijB
    nsmul := nsmulRec }

omit zero medial in
theorem mixer_eq_isotope (x y : V) :
    m x y = isotopeAdd bijA bijB (portA m x) (portB m y) := by
  simp only [isotopeAdd]
  exact (congrArg₂ m ((equivA bijA).symm_apply_apply x)
    ((equivB bijB).symm_apply_apply y)).symm

theorem mixer_isotope_add (x x' y y' : V) :
    m (isotopeAdd bijA bijB x x') (isotopeAdd bijA bijB y y') =
      isotopeAdd bijA bijB (m x y) (m x' y') := by
  simp only [isotopeAdd, equivA_symm_map zero medial bijA,
    equivB_symm_map zero medial bijB]
  exact medial _ _ _ _

noncomputable def isotopeOperation :
    letI := isotopeMonoid zero medial bijA bijB
    (V × V) →+ (V × V) := by
  letI := isotopeMonoid zero medial bijA bijB
  exact {
    toFun := fun p => (m p.1 p.2, m p.2 p.1)
    map_zero' := Prod.ext zero zero
    map_add' := fun p q => Prod.ext
      (mixer_isotope_add zero medial bijA bijB p.1 q.1 p.2 q.2)
      (mixer_isotope_add zero medial bijA bijB p.2 q.2 p.1 q.1) }

end Isotope

/-- A checked intermediate theorem must retain its explicit port-bijection
hypotheses. The raw theorem requires deriving those hypotheses first. -/
theorem bijective_port_reconstruction {V : Type*} [Zero V] {m : V → V → V}
    (h : Laws m) (bijA : Function.Bijective (portA m))
    (bijB : Function.Bijective (portB m)) :
    letI := isotopeMonoid (h.idempotent 0) h.medial bijA bijB
    let T := isotopeOperation (h.idempotent 0) h.medial bijA bijB
    TransparentSwapRoot.Reconstruction (TransparentSwapRoot.portA T)
      (TransparentSwapRoot.portB T) ∧
    (T : (V × V) → (V × V)) =
      PhaseMixerCancellation.mixer
        (TransparentSwapRoot.phase (TransparentSwapRoot.portA T))
        (TransparentSwapRoot.half (TransparentSwapRoot.portA T)
          (TransparentSwapRoot.portB T)) := by
  letI := isotopeMonoid (h.idempotent 0) h.medial bijA bijB
  apply TransparentSwapRoot.reconstruct_operation
  · intro x
    exact Prod.ext (h.idempotent x) (h.idempotent x)
  · intro p
    exact Prod.ext (h.bookend p.1 p.2) (h.bookend p.2 p.1)

section AdditiveInverse
variable {V : Type*} [AddCommMonoid V] {m : V → V → V}

/-- A polynomial identity used only after constructing the isotope. -/
theorem inverseATerm_eq_doubleB (A B : AddMonoid.End V)
    (lin : ∀ x y, m x y = A x + B y)
    (transparent : A + B = 1) (cross : A * B + B * A = 1) (x : V) :
    inverseATerm m x = B x + B x := by
  let D : AddMonoid.End V := A * B + B
  have hc : A * (B * D) + B * (A * D + B) = B + B := by
    calc
      _ = (A * B + B * A) * D + B * B := by noncomm_ring
      _ = D + B * B := by rw [cross, one_mul]
      _ = (A + B) * B + B := by dsimp [D]; noncomm_ring
      _ = _ := by rw [transparent, one_mul]
  have hx := DFunLike.congr_fun hc x
  change A (B (D x)) + B (A (D x) + B x) = B x + B x at hx
  simpa only [inverseATerm, portB, lin, map_zero, zero_add, D,
    AddMonoidHom.add_apply] using hx

end AdditiveInverse

inductive ReconstructionStage
  | rawPortInjectivity
  | bijectivePortIsotope
  | rawPortSurjectivityObligation
  | physicalJustificationOpen
  deriving DecidableEq, Repr

def reconstructionStages : List ReconstructionStage :=
  [.rawPortInjectivity, .bijectivePortIsotope, .rawPortSurjectivityObligation,
    .physicalJustificationOpen]

end IDT.QMClosure.MedialSwapRoot
