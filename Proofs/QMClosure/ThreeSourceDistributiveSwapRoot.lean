import Proofs.QMClosure.MedialSwapRoot
import Proofs.QMClosure.RawNetworkMedialWall

namespace IDT.QMClosure.ThreeSourceDistributiveSwapRoot

/-!
Three-source distributivity, transparency and the swap-square bookend law
force both translations to be bijective on an arbitrary carrier. The inverses
below are operation terms. No finiteness or division structure is supplied.
The process laws remain explicit hypotheses, with physical justification open.
Three-source counts independent preparation values. Distributivity repeats an
input, so a realization needs repeatable preparation or explicit replay. These
are additional overlapping-network conditions, with no derivation from disjoint
locality, and they do not supply readout conservation. With transparency and
bookends they are equivalent to the medial and complete-network exchange
presentations below.
-/

structure Laws {V : Type*} (m : V → V → V) : Prop where
  idempotent : ∀ x, m x x = x
  bookend : ∀ x y, m (m x y) (m y x) = y
  left_distributive : ∀ x y z, m x (m y z) = m (m x y) (m x z)
  right_distributive : ∀ x y z, m (m x y) z = m (m x z) (m y z)

section Algebra
variable {V : Type*} {m : V → V → V}

def oppositeLaws (h : Laws m) : Laws (fun x y => m y x) where
  idempotent := h.idempotent
  bookend x y := h.bookend x y
  left_distributive x y z := h.right_distributive z y x
  right_distributive x y z := h.left_distributive z y x

theorem elastic (h : Laws m) (a b : V) : m (m a b) a = m (m b a) b := by
  calc
    _ = m (m a b) (m (m b a) (m a b)) := by rw [h.bookend b a]
    _ = m (m (m a b) (m b a)) (m (m a b) (m a b)) :=
      h.left_distributive _ _ _
    _ = m b (m a b) := by rw [h.bookend, h.idempotent]
    _ = m (m b a) (m b b) := h.left_distributive _ _ _
    _ = _ := by rw [h.idempotent]

theorem left_injective (h : Laws m) (a : V) : Function.Injective (m a) := by
  intro b c heq
  let p := m a b
  let t := m c b
  have hat : m a t = p := by
    dsimp [t, p]
    rw [h.left_distributive, ← heq, h.idempotent]
  have hpt : m p t = m p b := by
    have hh := h.right_distributive a c b
    rw [← heq] at hh
    exact hh.symm
  have ht : t = b := by
    calc
      t = m p (m t a) := by rw [← hat, h.bookend]
      _ = m (m p t) (m p a) := h.left_distributive _ _ _
      _ = m (m p b) (m p a) := by rw [hpt]
      _ = m p (m b a) := (h.left_distributive _ _ _).symm
      _ = b := h.bookend a b
  have hc : c = b := by
    calc
      c = m (m b c) (m c b) := (h.bookend b c).symm
      _ = m (m b c) b := by change m (m b c) t = _; rw [ht]
      _ = m (m b b) (m c b) := h.right_distributive _ _ _
      _ = b := by rw [h.idempotent]; change m b t = b; rw [ht, h.idempotent]
  exact hc.symm

theorem right_injective (h : Laws m) (a : V) :
    Function.Injective (fun x => m x a) :=
  left_injective (oppositeLaws h) a

/-- A term solving `m x a = b`, with the fixed input listed first. -/
def rightDivisionTerm (m : V → V → V) (a b : V) : V :=
  let d := m (m a b) b
  m (m a d) (m d b)

/-- A term solving `m a x = b`, obtained by reversing every operation. -/
def leftDivisionTerm (m : V → V → V) (a b : V) : V :=
  rightDivisionTerm (fun x y => m y x) a b

theorem rightDivisionTerm_apply (h : Laws m) (a b : V) :
    m (rightDivisionTerm m a b) a = b := by
  let p := m a b
  let q := m b a
  let d := m p b
  let r := m d a
  have hdq : m d q = m b (m b q) := by
    change m (m p b) q = _
    rw [h.right_distributive]
    change m (m (m a b) (m b a)) (m b q) = _
    rw [h.bookend]
  have hr : r = m (m b q) b := by
    calc
      r = m (m p a) (m b a) := h.right_distributive _ _ _
      _ = m (m q b) q := by rw [show m p a = m q b from elastic h a b]
      _ = m (m b q) b := elastic h q b
  change m (m (m a d) (m d b)) a = b
  calc
    _ = m (m (m a d) a) (m (m d b) a) := h.right_distributive _ _ _
    _ = m (m r d) (m r q) := by
      rw [elastic h a d, h.right_distributive d b a]
    _ = m r (m d q) := (h.left_distributive _ _ _).symm
    _ = m (m (m b q) b) (m b (m b q)) := by rw [hr, hdq]
    _ = b := h.bookend _ _

theorem leftDivisionTerm_apply (h : Laws m) (a b : V) :
    m a (leftDivisionTerm m a b) = b :=
  rightDivisionTerm_apply (oppositeLaws h) a b

theorem rightDivisionTerm_reverse (h : Laws m) (a b : V) :
    rightDivisionTerm m a (m b a) = b := by
  apply right_injective h a
  exact rightDivisionTerm_apply h a (m b a)

theorem leftDivisionTerm_reverse (h : Laws m) (a b : V) :
    leftDivisionTerm m a (m a b) = b := by
  apply left_injective h a
  exact leftDivisionTerm_apply h a (m a b)

theorem right_bijective (h : Laws m) (a : V) :
    Function.Bijective (fun x => m x a) :=
  ⟨right_injective h a, fun b => ⟨rightDivisionTerm m a b, rightDivisionTerm_apply h a b⟩⟩

theorem left_bijective (h : Laws m) (a : V) : Function.Bijective (m a) :=
  ⟨left_injective h a, fun b => ⟨leftDivisionTerm m a b, leftDivisionTerm_apply h a b⟩⟩

theorem flexible (h : Laws m) (x y : V) : m x (m y x) = m (m x y) x := by
  rw [h.left_distributive, h.idempotent]

/-- A three-input exchange identity preceding the four-input medial law. -/
theorem cyclic_exchange (h : Laws m) (a b c : V) :
    m (m c a) (m b c) = m (m a b) a := by
  let k := m (m a b) a
  let u := m c a
  let t := m u k
  have hk : k = m (m b a) b := elastic h a b
  have hbc : m (m b c) k = m k u := by
    calc
      _ = m (m b c) (m a (m b a)) := by rw [flexible h a b]
      _ = m (m (m b c) a) (m (m b c) (m b a)) := h.left_distributive _ _ _
      _ = m (m (m b a) (m c a)) (m b (m c a)) := by
        rw [h.right_distributive b c a, ← h.left_distributive b c a]
      _ = m (m (m b a) b) (m c a) := (h.right_distributive _ _ _).symm
      _ = m k u := by rw [hk]
  apply right_injective h t
  change m (m u (m b c)) (m u k) = m k (m u k)
  calc
    _ = m u (m (m b c) k) := (h.left_distributive _ _ _).symm
    _ = m u (m k u) := by rw [hbc]
    _ = m (m u k) u := flexible h u k
    _ = m (m k u) k := elastic h u k
    _ = _ := (flexible h k u).symm

theorem alterability (h : Laws m) (x y z w : V) (heq : m x y = m z w) :
    m y z = m w x := by
  apply left_injective h (m z x)
  calc
    _ = m (m x y) x := cyclic_exchange h x y z
    _ = m (m z w) x := by rw [heq]
    _ = _ := h.right_distributive _ _ _

theorem medial (h : Laws m) (x y z w : V) :
    m (m x y) (m z w) = m (m x z) (m y w) := by
  have hexchange : m (m z w) (m x z) = m (m y w) (m x y) := by
    calc
      _ = m (m w x) w := cyclic_exchange h w x z
      _ = _ := (cyclic_exchange h w x y).symm
  exact (alterability h (m z w) (m x z) (m y w) (m x y) hexchange).symm

def toMedialSwapRootLaws (h : Laws m) : MedialSwapRoot.Laws m where
  idempotent := h.idempotent
  medial := medial h
  bookend := h.bookend

def ofMedialSwapRootLaws (h : MedialSwapRoot.Laws m) : Laws m where
  idempotent := h.idempotent
  bookend := h.bookend
  left_distributive x y z := by
    simpa only [h.idempotent] using h.medial x x y z
  right_distributive x y z := by
    simpa only [h.idempotent] using h.medial x y z z

/-- With transparency and bookends, the two presentations have equal strength. -/
theorem laws_iff_medialSwapRootLaws : Laws m ↔ MedialSwapRoot.Laws m :=
  ⟨toMedialSwapRootLaws, ofMedialSwapRootLaws⟩

end Algebra

/-- Complete-operation hypotheses supply transparency and bookends directly. -/
theorem laws_of_complete_operation {V : Type*} (T : (V × V) → (V × V))
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap)
    (left_distributive : ∀ x y z,
      MedialSwapRoot.firstChannel T x (MedialSwapRoot.firstChannel T y z) =
      MedialSwapRoot.firstChannel T (MedialSwapRoot.firstChannel T x y)
        (MedialSwapRoot.firstChannel T x z))
    (right_distributive : ∀ x y z,
      MedialSwapRoot.firstChannel T (MedialSwapRoot.firstChannel T x y) z =
      MedialSwapRoot.firstChannel T (MedialSwapRoot.firstChannel T x z)
        (MedialSwapRoot.firstChannel T y z)) :
    Laws (MedialSwapRoot.firstChannel T) where
  idempotent x := congrArg Prod.fst (transparent x)
  bookend := MedialSwapRoot.raw_operation_bookend T square
  left_distributive := left_distributive
  right_distributive := right_distributive

def rowGate {V : Type*} (T : (V × V) → (V × V))
    (p : (V × V) × (V × V)) : (V × V) × (V × V) :=
  (T p.1, T p.2)

def transpose {V : Type*} (p : (V × V) × (V × V)) : (V × V) × (V × V) :=
  ((p.1.1, p.2.1), (p.1.2, p.2.2))

def columnGate {V : Type*} (T : (V × V) → (V × V))
    (p : (V × V) × (V × V)) : (V × V) × (V × V) :=
  transpose (rowGate T (transpose p))

/-- Four wires carry three independent values, with the first value repeated. -/
def RestrictedExchange {V : Type*} (T : (V × V) → (V × V)) : Prop :=
  ∀ x y z, rowGate T (columnGate T ((x, x), (y, z))) =
    columnGate T (rowGate T ((x, x), (y, z)))

def CompleteExchange {V : Type*} (T : (V × V) → (V × V)) : Prop :=
  ∀ p, rowGate T (columnGate T p) = columnGate T (rowGate T p)

/-- The existing network contract uses the reverse equality orientation. -/
theorem completeExchange_iff_rowColumnCommutes {V : Type*}
    (T : (V × V) → (V × V)) :
    CompleteExchange T ↔ RawNetworkMedialWall.RowColumnCommutes T := by
  constructor
  · intro h p
    exact (h p).symm
  · intro h p
    exact (h p).symm

/-- Equality includes all four output coordinates of the repeated-input network. -/
theorem restrictedExchange_iff_laws {V : Type*} (T : (V × V) → (V × V))
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap) :
    RestrictedExchange T ↔ Laws (MedialSwapRoot.firstChannel T) := by
  have idem (x : V) : MedialSwapRoot.firstChannel T x x = x :=
    congrArg Prod.fst (transparent x)
  constructor
  · intro heq
    apply laws_of_complete_operation T transparent square
    · intro x y z
      have hh := congrArg (fun p => p.1.1) (heq x y z)
      simpa only [rowGate, columnGate, transpose,
        MedialSwapRoot.raw_operation_eq_symmetric T square, idem] using hh.symm
    · intro x y z
      have hh := congrArg (fun p => p.2.1) (heq z x y)
      simpa only [rowGate, columnGate, transpose,
        MedialSwapRoot.raw_operation_eq_symmetric T square, idem] using hh.symm
  · intro h x y z
    simp only [rowGate, columnGate, transpose,
      MedialSwapRoot.raw_operation_eq_symmetric T square, h.idempotent,
      ← h.left_distributive, ← h.right_distributive]

theorem completeExchange_iff_medial {V : Type*} (T : (V × V) → (V × V))
    (square : ∀ p, T (T p) = p.swap) :
    CompleteExchange T ↔
      (∀ a b c d, MedialSwapRoot.firstChannel T
        (MedialSwapRoot.firstChannel T a b) (MedialSwapRoot.firstChannel T c d) =
        MedialSwapRoot.firstChannel T
          (MedialSwapRoot.firstChannel T a c) (MedialSwapRoot.firstChannel T b d)) :=
  (completeExchange_iff_rowColumnCommutes T).trans
    (RawNetworkMedialWall.rowColumnCommutes_iff_medial T square)

/-- Under the base laws, repeating one input is already equivalent to full exchange. -/
theorem restrictedExchange_iff_completeExchange {V : Type*}
    (T : (V × V) → (V × V))
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap) :
    RestrictedExchange T ↔ CompleteExchange T := by
  constructor
  · intro h
    exact (completeExchange_iff_medial T square).mpr
      (medial ((restrictedExchange_iff_laws T transparent square).mp h))
  · intro h x y z
    exact h ((x, x), (y, z))

end IDT.QMClosure.ThreeSourceDistributiveSwapRoot
