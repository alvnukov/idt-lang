import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Bool.Basic

/-!
# Port identification and separated frame maps

These are pure function theorems. A square-root routing law contains a chosen
identification of the two port types. Full both-output covariance transports
that identification; it does not physically generate aligned references or make
the maps executable. A common map is necessary in literal common-carrier root
comparisons, not sufficient for arbitrary gate intertwining.

Independent changes of frames transform both the gate and the alignment. A
claim that the same literal swap remains unchanged under arbitrary independent
frames is unsupported. Partial-domain conclusions apply only to values in the
stated jointly legal two-step pairs; individual reachability supplies no joint
domain fullness. Coarse-readout equality is not full covariance. Port labels
are preparation interfaces, not particle identities. No physical availability,
sector selection, matter applicability or QM claim is established.
-/

namespace IDT.QMClosure.PortFrameAlignment

variable {A B C E V W X Y : Type*}

/-- Swap relative to an explicitly chosen identification of port types. -/
def alignedSwap (kappa : A ≃ B) (p : A × B) : A × B :=
  (kappa.symm p.2, kappa p.1)

theorem alignedSwap_involutive (kappa : A ≃ B) : Function.Involutive (alignedSwap kappa) := by
  rintro ⟨a, b⟩
  apply Prod.ext <;> simp only [alignedSwap, kappa.symm_apply_apply, kappa.apply_symm_apply]

/-- Compatibility with the chosen port identification is exactly swap covariance. -/
theorem alignedSwap_map_iff (kappa : A ≃ B) (lambda : C ≃ E)
    (f : A → C) (g : B → E) :
    alignedSwap lambda ∘ Prod.map f g = Prod.map f g ∘ alignedSwap kappa ↔
      ∀ a, g (kappa a) = lambda (f a) := by
  constructor
  · intro h a
    have he := congrArg Prod.snd (congrFun h (a, kappa a))
    exact he.symm
  · intro h
    funext p
    rcases p with ⟨a, b⟩
    apply Prod.ext
    · change lambda.symm (g b) = f (kappa.symm b)
      apply lambda.injective
      simpa only [lambda.apply_symm_apply, kappa.apply_symm_apply] using h (kappa.symm b)
    · exact (h a).symm

/-- Squaring full two-output intertwining forces alignment compatibility. -/
theorem root_alignment_compatible (kappa : A ≃ B) (lambda : C ≃ E)
    (T : A × B → A × B) (S : C × E → C × E) (f : A → C) (g : B → E)
    (hT : ∀ p, T (T p) = alignedSwap kappa p)
    (hS : ∀ q, S (S q) = alignedSwap lambda q)
    (hcov : ∀ p, S (Prod.map f g p) = Prod.map f g (T p)) :
    ∀ a, g (kappa a) = lambda (f a) := by
  apply (alignedSwap_map_iff kappa lambda f g).mp
  funext p
  calc
    alignedSwap lambda (Prod.map f g p) = S (S (Prod.map f g p)) := (hS _).symm
    _ = S (Prod.map f g (T p)) := congrArg S (hcov p)
    _ = Prod.map f g (T (T p)) := hcov (T p)
    _ = Prod.map f g (alignedSwap kappa p) := congrArg (Prod.map f g) (hT p)

/-- Literal swaps on common source and target carriers force one common map. -/
theorem literal_root_forces_common_map
    (T : V × V → V × V) (S : W × W → W × W) (f g : V → W)
    (hT : ∀ p, T (T p) = p.swap) (hS : ∀ q, S (S q) = q.swap)
    (hcov : ∀ p, S (Prod.map f g p) = Prod.map f g (T p)) : f = g := by
  have h := root_alignment_compatible (Equiv.refl V) (Equiv.refl W) T S f g hT hS hcov
  funext x
  exact (h x).symm

/-- One joint pair requires covariance only at that pair and its next gate output. -/
theorem partial_swap_intertwining
    (T : V × V → V × V) (S : W × W → W × W) (f g : V → W) (p : V × V)
    (hT : T (T p) = p.swap)
    (hS : S (S (Prod.map f g p)) = (Prod.map f g p).swap)
    (hp : S (Prod.map f g p) = Prod.map f g (T p))
    (hnext : S (Prod.map f g (T p)) = Prod.map f g (T (T p))) :
    Prod.map f g p.swap = (Prod.map f g p).swap := by
  calc
    Prod.map f g p.swap = Prod.map f g (T (T p)) := congrArg (Prod.map f g) hT.symm
    _ = S (Prod.map f g (T p)) := hnext.symm
    _ = S (S (Prod.map f g p)) := congrArg S hp.symm
    _ = (Prod.map f g p).swap := hS

theorem partial_pair_agreement
    (T : V × V → V × V) (S : W × W → W × W) (f g : V → W) (p : V × V)
    (hT : T (T p) = p.swap)
    (hS : S (S (Prod.map f g p)) = (Prod.map f g p).swap)
    (hp : S (Prod.map f g p) = Prod.map f g (T p))
    (hnext : S (Prod.map f g (T p)) = Prod.map f g (T (T p))) :
    f p.1 = g p.1 ∧ f p.2 = g p.2 := by
  have h := partial_swap_intertwining T S f g p hT hS hp hnext
  exact ⟨(congrArg Prod.snd h).symm, congrArg Prod.fst h⟩

/-- A mathematical change of complete interface coordinates. -/
def conjugateGate (D : X ≃ Y) (T : X → X) : Y → Y := D ∘ T ∘ D.symm

theorem conjugateGate_square (D : X ≃ Y) (T R : X → X)
    (hT : ∀ p, T (T p) = R p) (q : Y) :
    conjugateGate D T (conjugateGate D T q) = conjugateGate D R q := by
  simp only [conjugateGate, Function.comp_apply, D.symm_apply_apply, hT]

/-- Independent port frames transport the alignment as well as the gate. -/
def transformedAlignment (kappa : A ≃ B) (f : A ≃ C) (g : B ≃ E) : C ≃ E :=
  (f.symm.trans kappa).trans g

theorem conjugate_alignedSwap (kappa : A ≃ B) (f : A ≃ C) (g : B ≃ E) (q : C × E) :
    conjugateGate (f.prodCongr g) (alignedSwap kappa) q =
      alignedSwap (transformedAlignment kappa f g) q := rfl

theorem conjugated_root_square (kappa : A ≃ B) (f : A ≃ C) (g : B ≃ E)
    (T : A × B → A × B) (hT : ∀ p, T (T p) = alignedSwap kappa p) (q : C × E) :
    conjugateGate (f.prodCongr g) T (conjugateGate (f.prodCongr g) T q) =
      alignedSwap (transformedAlignment kappa f g) q :=
  (conjugateGate_square (f.prodCongr g) T (alignedSwap kappa) hT q).trans
    (conjugate_alignedSwap kappa f g q)

def twistedSwap (f g : V ≃ W) (p : W × W) : W × W :=
  (f (g.symm p.2), g (f.symm p.1))

theorem conjugate_literal_swap (f g : V ≃ W) (q : W × W) :
    conjugateGate (f.prodCongr g) (Prod.swap : V × V → V × V) q = twistedSwap f g q := rfl

theorem twistedSwap_eq_swap_iff (f g : V ≃ W) :
    twistedSwap f g = (Prod.swap : W × W → W × W) ↔ f = g := by
  constructor
  · intro h
    apply Equiv.ext
    intro a
    have he := congrArg Prod.fst (congrFun h (f a, g a))
    change f (g.symm (g a)) = g a at he
    simpa only [g.symm_apply_apply] using he
  · intro h
    subst g
    funext p
    rcases p with ⟨x, y⟩
    apply Prod.ext <;> simp only [twistedSwap, f.apply_symm_apply, Prod.swap]

/-- Expanding cross-local double routing twice determines fourfold routing. -/
theorem cross_square_fourfold (T : A × B → A × B) (u : B → A) (v : A → B)
    (h2 : ∀ p, T (T p) = (u p.2, v p.1)) (p : A × B) :
    T (T (T (T p))) = (u (v p.1), v (u p.2)) := by
  rw [h2, h2]

/-- Four-use return supplies both crossmap inverse laws even for empty types. -/
theorem fourfold_iff_cross_return (T : A × B → A × B) (u : B → A) (v : A → B)
    (h2 : ∀ p, T (T p) = (u p.2, v p.1)) :
    (∀ p, T (T (T (T p))) = p) ↔
      (∀ a, u (v a) = a) ∧ (∀ b, v (u b) = b) := by
  constructor
  · intro h4
    constructor
    · intro a
      have hp := congrArg Prod.fst (h4 (a, v a))
      rw [cross_square_fourfold T u v h2] at hp
      exact hp
    · intro b
      have hp := congrArg Prod.snd (h4 (u b, b))
      rw [cross_square_fourfold T u v h2] at hp
      exact hp
  · rintro ⟨hu, hv⟩ p
    rw [cross_square_fourfold T u v h2]
    exact Prod.ext (hu p.1) (hv p.2)

/-- The crossmaps themselves are unique; four-use return is not needed. -/
theorem crossmaps_unique (T : A × B → A × B) (u u' : B → A) (v v' : A → B)
    (h2 : ∀ p, T (T p) = (u p.2, v p.1))
    (h2' : ∀ p, T (T p) = (u' p.2, v' p.1)) : u = u' ∧ v = v' := by
  have he (p : A × B) : (u p.2, v p.1) = (u' p.2, v' p.1) :=
    (h2 p).symm.trans (h2' p)
  constructor
  · funext b
    exact congrArg Prod.fst (he (u b, b))
  · funext a
    exact congrArg Prod.snd (he (a, v a))

/-- Construct the alignment without choice: its forward and inverse maps are v and u. -/
def alignmentOfCrossReturn (T : A × B → A × B) (u : B → A) (v : A → B)
    (h2 : ∀ p, T (T p) = (u p.2, v p.1))
    (h4 : ∀ p, T (T (T (T p))) = p) : A ≃ B where
  toFun := v
  invFun := u
  left_inv := ((fourfold_iff_cross_return T u v h2).mp h4).1
  right_inv := ((fourfold_iff_cross_return T u v h2).mp h4).2

@[simp] theorem alignmentOfCrossReturn_apply
    (T : A × B → A × B) (u : B → A) (v : A → B)
    (h2 : ∀ p, T (T p) = (u p.2, v p.1))
    (h4 : ∀ p, T (T (T (T p))) = p) (a : A) :
    alignmentOfCrossReturn T u v h2 h4 a = v a := rfl

@[simp] theorem alignmentOfCrossReturn_symm_apply
    (T : A × B → A × B) (u : B → A) (v : A → B)
    (h2 : ∀ p, T (T p) = (u p.2, v p.1))
    (h4 : ∀ p, T (T (T (T p))) = p) (b : B) :
    (alignmentOfCrossReturn T u v h2 h4).symm b = u b := rfl

/-- Cross-locality plus four-use return is a presentation of an aligned-root law. -/
theorem square_eq_alignmentOfCrossReturn
    (T : A × B → A × B) (u : B → A) (v : A → B)
    (h2 : ∀ p, T (T p) = (u p.2, v p.1))
    (h4 : ∀ p, T (T (T (T p))) = p) (p : A × B) :
    T (T p) = alignedSwap (alignmentOfCrossReturn T u v h2 h4) p := h2 p

namespace WithoutSquareControl

def gate : Bool × Bool → Bool × Bool := id
def leftMap : Bool → Bool := id
def rightMap : Bool → Bool := Bool.not

theorem full_covariance (p : Bool × Bool) :
    gate (Prod.map leftMap rightMap p) = Prod.map leftMap rightMap (gate p) := rfl

theorem maps_differ : leftMap ≠ rightMap := by
  intro h
  have he := congrFun h false
  change false = true at he
  cases he

theorem gate_transparent (x : Bool) : gate (x, x) = (x, x) := rfl

theorem gate_bijective : Function.Bijective gate :=
  ⟨fun _ _ h => h, fun p => ⟨p, rfl⟩⟩

theorem square_is_not_swap : ¬ ∀ p, gate (gate p) = p.swap := by
  intro h
  have he := congrArg Prod.fst (h (false, true))
  change false = true at he
  cases he

end WithoutSquareControl

namespace FirstOutputControl

abbrev Port := Bool × Bool

/-- Exact four-coordinate routing; its square is the literal port swap. -/
def gate (p : Port × Port) : Port × Port :=
  ((p.1.2, p.2.1), (p.2.2, p.1.1))

def leftMap : Port → Port := id
def rightMap (p : Port) : Port := (p.1, Bool.not p.2)

theorem gate_square (p : Port × Port) : gate (gate p) = p.swap := by
  rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rfl

theorem first_output_covariance (x y : Port) :
    (gate (leftMap x, rightMap y)).1 =
      (Prod.map leftMap rightMap (gate (x, y))).1 := rfl

theorem second_output_left_witness :
    (gate (leftMap (false, false), rightMap (false, false))).2 = (true, false) := rfl

theorem second_output_right_witness :
    (Prod.map leftMap rightMap (gate ((false, false), (false, false)))).2 =
      (false, true) := rfl

theorem not_full_covariance :
    ¬ ∀ p, gate (Prod.map leftMap rightMap p) = Prod.map leftMap rightMap (gate p) := by
  intro h
  have he := congrArg (fun z : Port × Port => z.2.1)
    (h ((false, false), (false, false)))
  change true = false at he
  cases he

theorem maps_differ : leftMap ≠ rightMap := by
  intro h
  have he := congrArg Prod.snd (congrFun h (false, false))
  change false = true at he
  cases he

end FirstOutputControl

namespace WithoutFourthControl

abbrev Port := Bool × Bool

/-- This bijective routing has cross-local square but not four-use return. -/
def gate (p : Port × Port) : Port × Port :=
  ((Bool.not p.1.2, p.2.1), (p.2.2, p.1.1))

def transferBack (p : Port) : Port := (Bool.not p.1, p.2)
def transferForward (p : Port) : Port := (p.1, Bool.not p.2)

theorem gate_square (p : Port × Port) :
    gate (gate p) = (transferBack p.2, transferForward p.1) := by
  rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rfl

def inverseGate (q : Port × Port) : Port × Port :=
  ((q.2.2, Bool.not q.1.1), (q.1.2, q.2.1))

theorem inverseGate_gate (p : Port × Port) : inverseGate (gate p) = p := by
  rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  cases b <;> rfl

theorem gate_inverseGate (q : Port × Port) : gate (inverseGate q) = q := by
  rcases q with ⟨⟨e, f⟩, ⟨g, h⟩⟩
  cases e <;> rfl

theorem gate_bijective : Function.Bijective gate := by
  constructor
  · intro p q hpq
    simpa only [inverseGate_gate] using congrArg inverseGate hpq
  · intro q
    exact ⟨inverseGate q, gate_inverseGate q⟩

theorem gate_fourfold (p : Port × Port) :
    gate (gate (gate (gate p))) =
      ((Bool.not p.1.1, Bool.not p.1.2), (Bool.not p.2.1, Bool.not p.2.2)) := by
  rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rfl

theorem gate_fourfold_false_witness :
    gate (gate (gate (gate ((false, false), (false, false))))) =
      ((true, true), (true, true)) := rfl

theorem not_fourfold_identity : ¬ ∀ p, gate (gate (gate (gate p))) = p := by
  intro h
  have he := congrArg (fun q : Port × Port => q.1.1)
    (h ((false, false), (false, false)))
  change true = false at he
  cases he

theorem transferBack_transferForward (p : Port) :
    transferBack (transferForward p) = (Bool.not p.1, Bool.not p.2) := rfl

theorem transferForward_transferBack (p : Port) :
    transferForward (transferBack p) = (Bool.not p.1, Bool.not p.2) := rfl

theorem transferBack_comp_transferForward_ne_id : transferBack ∘ transferForward ≠ id := by
  intro h
  have he := congrArg Prod.fst (congrFun h (false, false))
  change true = false at he
  cases he

theorem transferForward_comp_transferBack_ne_id : transferForward ∘ transferBack ≠ id := by
  intro h
  have he := congrArg Prod.fst (congrFun h (false, false))
  change true = false at he
  cases he

end WithoutFourthControl

end IDT.QMClosure.PortFrameAlignment
