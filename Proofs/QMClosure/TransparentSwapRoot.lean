import Proofs.QMClosure.PhaseMixerCancellation
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Tactic.NoncommRing

namespace IDT.QMClosure.TransparentSwapRoot

/-!
# Transparent additive roots of port exchange

This is a universal reparameterization theorem inside a specified additive
model, not a proof that its assumptions are inevitable IDT primitives or
physically realized. A complete additive two-port operation, transparency on
equal inputs, and its exact square being port exchange derive symmetric channel
action, genuine additive halving, a phase satisfying G⁴ = id, antipodal
cancellation, and the previously selected routing. The identity x + G(G x) = 0
supplies an additive inverse for every input, so the carrier admits an additive
commutative group structure; this file does not package an AddCommGroup instance.
No group, scalars, phase, half, topology,
detector response, or actualization is assumed on the input carrier.

The natural-number routing controls below are classical countermodels to
dropping either operational law; they are distinct from the universal theorem.
Physical justification, serial multiplicative detector response, actualization,
and full QM remain open. No manifest or scientific status is upgraded here.
-/

private theorem cancel_with_inverse {R : Type*} [AddCommMonoid R]
    {s t x y : R} (hinv : s + t = 0) (heq : s + x = s + y) : x = y := by
  have hh := congrArg (fun z => z + t) heq
  have hx : s + x + t = x + (s + t) := by ac_rfl
  have hy : s + y + t = y + (s + t) := by ac_rfl
  simpa only [hx, hy, hinv, add_zero] using hh

/-- Semiring algebra without additive cancellation or commutative multiplication. -/
private theorem coefficient_algebra {R : Type*} [Semiring R] (a b : R)
    (transparent : a + b = 1) (same : a * a + b * b = 0)
    (cross : a * b + b * a = 1) :
    a * b = b * a ∧
    (a * b) + (a * b) = 1 ∧
    let g := a * a + a * a
    let k := b * b + b * b
    g * g + 1 = 0 ∧ g * g * g * g = 1 ∧ g * g * g = k ∧
      a + a = 1 + g ∧ b + b = 1 + g * g * g := by
  have hab : a * b = b * a := by
    apply cancel_with_inverse same
    calc
      a * a + a * b = a * (a + b) := (mul_add _ _ _).symm
      _ = a := by rw [transparent, mul_one]
      _ = (a + b) * a := by rw [transparent, one_mul]
      _ = a * a + b * a := add_mul _ _ _
  have half : a * b + a * b = 1 := by simpa only [hab] using cross
  refine ⟨hab, half, ?_⟩
  dsimp only
  let g := a * a + a * a
  let k := b * b + b * b
  have hgk : g + k = 0 := by
    calc
      g + k = (a * a + b * b) + (a * a + b * b) := by dsimp [g, k]; ac_rfl
      _ = 0 := by rw [same, zero_add]
  have aabb : (a * a) * (b * b) = (a * b) * (a * b) := by
    calc
      _ = a * (a * b) * b := by simp only [mul_assoc]
      _ = a * (b * a) * b := by rw [hab]
      _ = _ := by simp only [mul_assoc]
  have hgkmul : g * k = 1 := by
    calc
      _ = (a * b + a * b) * (a * b + a * b) := by
        dsimp [g, k]
        simp only [add_mul, mul_add, aabb]
      _ = 1 := by rw [half, one_mul]
  have hg2 : g * g + 1 = 0 := by
    calc
      _ = g * g + g * k := by rw [hgkmul]
      _ = g * (g + k) := (mul_add _ _ _).symm
      _ = 0 := by rw [hgk, mul_zero]
  have hg4plus : g * g * g * g + g * g = 0 := by
    calc
      _ = (g * g) * (g * g + 1) := by noncomm_ring
      _ = 0 := by rw [hg2, mul_zero]
  have hg4 : g * g * g * g = 1 := by
    calc
      _ = g * g * g * g + (g * g + 1) := by rw [hg2, add_zero]
      _ = (g * g * g * g + g * g) + 1 := (add_assoc _ _ _).symm
      _ = 1 := by rw [hg4plus, zero_add]
  have hg3 : g * g * g = k := by
    calc
      _ = (g * g * g) * (g * k) := by rw [hgkmul, mul_one]
      _ = (g * g * g * g) * k := by simp only [mul_assoc]
      _ = k := by rw [hg4, one_mul]
  have ha : a + a = 1 + g := by
    calc
      _ = (a + a) * (a + b) := by rw [transparent, mul_one]
      _ = (a * b + a * b) + g := by dsimp [g]; noncomm_ring
      _ = _ := by rw [half]
  have hb : b + b = 1 + g * g * g := by
    calc
      _ = (a + b) * (b + b) := by rw [transparent, one_mul]
      _ = (a * b + a * b) + k := by dsimp [k]; noncomm_ring
      _ = _ := by rw [half, hg3]
  exact ⟨hg2, hg4, hg3, ha, hb⟩

section Additive
variable {V : Type*} [AddCommMonoid V]

abbrev End := AddMonoid.End V

def mixer (A B : End (V := V)) (p : V × V) : V × V :=
  (A p.1 + B p.2, B p.1 + A p.2)

def half (A B : End (V := V)) : End (V := V) := A * B
def phase (A : End (V := V)) : End (V := V) := A * A + A * A

structure Reconstruction (A B : End (V := V)) : Prop where
  same : ∀ x, A (A x) + B (B x) = 0
  cross : ∀ x, A (B x) + B (A x) = x
  commute : ∀ x, A (B x) = B (A x)
  halves : ∀ x, half A B x + half A B x = x
  fourth : ∀ x, phase A (phase A (phase A (phase A x))) = x
  cancellation : ∀ x, x + phase A (phase A x) = 0
  coefficientA : ∀ x, A x = half A B (x + phase A x)
  coefficientB : ∀ x, B x = half A B (x + phase A (phase A (phase A x)))

/-- The exact root and transparency laws force the selected coefficients. -/
theorem reconstruct (A B : End (V := V))
    (transparent : ∀ x, A x + B x = x)
    (square : ∀ p, mixer A B (mixer A B p) = (p.2, p.1)) :
    Reconstruction A B := by
  have same : A * A + B * B = 0 := by
    apply AddMonoidHom.ext
    intro x
    simpa only [mixer, map_zero, add_zero] using congrArg Prod.fst (square (x, 0))
  have cross : A * B + B * A = 1 := by
    apply AddMonoidHom.ext
    intro x
    simpa only [mixer, map_zero, add_zero, zero_add, add_comm] using
      congrArg Prod.snd (square (x, 0))
  have tr : A + B = 1 := AddMonoidHom.ext transparent
  obtain ⟨comm, hh, gg, gf, _g3, aa, bb⟩ := coefficient_algebra A B tr same cross
  have recA : half A B * (1 + phase A) = A := by
    change (A * B) * (1 + (A * A + A * A)) = A
    rw [← aa, mul_add, ← add_mul, hh, one_mul]
  have recB : half A B * (1 + phase A * phase A * phase A) = B := by
    change (A * B) * (1 + (A * A + A * A) * (A * A + A * A) *
      (A * A + A * A)) = B
    rw [← bb, mul_add, ← add_mul, hh, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact DFunLike.congr_fun same x
  · intro x; exact DFunLike.congr_fun cross x
  · intro x; exact DFunLike.congr_fun comm x
  · intro x; exact DFunLike.congr_fun hh x
  · intro x; exact DFunLike.congr_fun gf x
  · intro x
    have hx := DFunLike.congr_fun gg x
    change phase A (phase A x) + x = 0 at hx
    simpa only [add_comm] using hx
  · intro x; exact (DFunLike.congr_fun recA x).symm
  · intro x; exact (DFunLike.congr_fun recB x).symm

theorem mixer_eq_selected (A B : End (V := V)) (r : Reconstruction A B) :
    mixer A B = PhaseMixerCancellation.mixer (phase A) (half A B) := by
  funext p
  change (A p.1 + B p.2, B p.1 + A p.2) =
    (half A B (p.1 + phase A p.1) +
      half A B (p.2 + phase A (phase A (phase A p.2))),
     half A B (p.1 + phase A (phase A (phase A p.1))) +
      half A B (p.2 + phase A p.2))
  rw [r.coefficientA p.1, r.coefficientA p.2, r.coefficientB p.1, r.coefficientB p.2]

theorem mixer_fourth_identity (A B : End (V := V))
    (square : ∀ p, mixer A B (mixer A B p) = (p.2, p.1)) (p : V × V) :
    mixer A B (mixer A B (mixer A B (mixer A B p))) = p := by
  rw [square, square]

theorem mixer_bijective (A B : End (V := V))
    (square : ∀ p, mixer A B (mixer A B p) = (p.2, p.1)) :
    Function.Bijective (mixer A B) := by
  constructor
  · intro p q heq
    have h := congrArg (mixer A B) heq
    rw [square, square] at h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro p
    exact ⟨mixer A B (mixer A B (mixer A B p)), mixer_fourth_identity A B square p⟩

def inverseMixer (A B : End (V := V)) (p : V × V) : V × V :=
  mixer A B (mixer A B (mixer A B p))

theorem mixer_inverse_cube (A B : End (V := V))
    (square : ∀ p, mixer A B (mixer A B p) = (p.2, p.1)) (p : V × V) :
    inverseMixer A B (mixer A B p) = p ∧
    mixer A B (inverseMixer A B p) = p :=
  ⟨mixer_fourth_identity A B square p, mixer_fourth_identity A B square p⟩

theorem selected_transparent (G h : V →+ V)
    (halves : ∀ x, h x + h x = x)
    (cancel : ∀ x, x + G (G x) = 0) (x : V) :
    PhaseMixerCancellation.coefficientA G h x +
      PhaseMixerCancellation.coefficientB G h x = x := by
  apply PhaseMixerCancellation.doubling_injective h halves
  change (_ + _) + (_ + _) = x + x
  calc
    _ = (PhaseMixerCancellation.coefficientA G h x +
          PhaseMixerCancellation.coefficientA G h x) +
        (PhaseMixerCancellation.coefficientB G h x +
          PhaseMixerCancellation.coefficientB G h x) := by ac_rfl
    _ = (x + G x) + (x + G (G (G x))) := by
      rw [PhaseMixerCancellation.doubled_coefficientA G h halves,
        PhaseMixerCancellation.doubled_coefficientB G h halves]
    _ = (x + x) + (G x + G (G (G x))) := by ac_rfl
    _ = x + x := by rw [cancel (G x), add_zero]

/-- Exact equivalence inside the additive symmetric-channel model. -/
theorem transparent_square_iff_selected (A B : End (V := V)) :
    ((∀ x, A x + B x = x) ∧
      (∀ p, mixer A B (mixer A B p) = (p.2, p.1))) ↔
    ∃ G h : V →+ V, (∀ x, h x + h x = x) ∧
      (∀ x, G (G (G (G x))) = x) ∧
      (∀ x, x + G (G x) = 0) ∧
      mixer A B = PhaseMixerCancellation.mixer G h := by
  constructor
  · rintro ⟨tr, sq⟩
    let r := reconstruct A B tr sq
    exact ⟨phase A, half A B, r.halves, r.fourth, r.cancellation,
      mixer_eq_selected A B r⟩
  · rintro ⟨G, h, hh, h4, hc, hm⟩
    constructor
    · intro x
      have hx := congrArg Prod.fst (congrFun hm (x, x))
      change A x + B x = PhaseMixerCancellation.coefficientA G h x +
        PhaseMixerCancellation.coefficientB G h x at hx
      exact hx.trans (selected_transparent G h hh hc x)
    · rw [hm]
      exact PhaseMixerCancellation.mixer_squared_swap G h hh h4 hc

/-! Symmetry follows when the input is a single complete additive operation. -/
def portA (T : (V × V) →+ (V × V)) : V →+ V where
  toFun x := (T (x, 0)).1
  map_zero' := by change (T 0).1 = 0; rw [map_zero]; rfl
  map_add' x y := by
    have heq : (x + y, (0 : V)) = (x, 0) + (y, 0) := by simp
    simp only [heq, map_add, Prod.fst_add]

def portB (T : (V × V) →+ (V × V)) : V →+ V where
  toFun x := (T (x, 0)).2
  map_zero' := by change (T 0).2 = 0; rw [map_zero]; rfl
  map_add' x y := by
    have heq : (x + y, (0 : V)) = (x, 0) + (y, 0) := by simp
    simp only [heq, map_add, Prod.snd_add]

theorem commutes_with_swap (T : (V × V) →+ (V × V))
    (square : ∀ p, T (T p) = p.swap) (p : V × V) :
    T p.swap = (T p).swap := by
  calc
    _ = T (T (T p)) := congrArg T (square p).symm
    _ = _ := square (T p)

theorem operation_eq_symmetric_mixer (T : (V × V) →+ (V × V))
    (square : ∀ p, T (T p) = p.swap) :
    (T : (V × V) → (V × V)) = mixer (portA T) (portB T) := by
  funext p
  rcases p with ⟨x, y⟩
  have hswap := commutes_with_swap T square (y, 0)
  change T (0, y) = ((T (y, 0)).2, (T (y, 0)).1) at hswap
  have hdecomp : (x, y) = (x, (0 : V)) + (0, y) := by simp
  calc
    T (x, y) = T (x, 0) + T (0, y) := by rw [hdecomp, map_add]
    _ = mixer (portA T) (portB T) (x, y) := by
      rw [hswap]
      rfl

/-- The only supplied operation laws are additivity, transparency, and exact square-swap. -/
theorem reconstruct_operation (T : (V × V) →+ (V × V))
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap) :
    Reconstruction (portA T) (portB T) ∧
      (T : (V × V) → (V × V)) =
        PhaseMixerCancellation.mixer (phase (portA T)) (half (portA T) (portB T)) := by
  have hm := operation_eq_symmetric_mixer T square
  have tr : ∀ x, portA T x + portB T x = x := by
    intro x
    have hx := congrArg Prod.fst (transparent x)
    rw [congrFun hm] at hx
    exact hx
  have sq : ∀ p, mixer (portA T) (portB T) (mixer (portA T) (portB T) p) =
      (p.2, p.1) := by
    intro p
    simpa only [← hm] using square p
  let r := reconstruct (portA T) (portB T) tr sq
  exact ⟨r, hm.trans (mixer_eq_selected _ _ r)⟩

end Additive

namespace Controls

/-- Classical coordinate routing on a carrier with no inverse for (1,0). -/
def natA : (ℕ × ℕ) →+ (ℕ × ℕ) where
  toFun x := (x.2, 0)
  map_zero' := rfl
  map_add' x y := by ext <;> simp

def natB : (ℕ × ℕ) →+ (ℕ × ℕ) where
  toFun x := (0, x.1)
  map_zero' := rfl
  map_add' x y := by ext <;> simp

def classicalRouting : ((ℕ × ℕ) × (ℕ × ℕ)) →+ ((ℕ × ℕ) × (ℕ × ℕ)) where
  toFun p := ((p.1.2, p.2.1), (p.2.2, p.1.1))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem nat_mixer_eq_routing :
    mixer natA natB = (classicalRouting : _ → _) := by
  funext p
  change ((p.1.2 + 0, 0 + p.2.1), (0 + p.2.2, p.1.1 + 0)) =
    ((p.1.2, p.2.1), (p.2.2, p.1.1))
  simp

theorem classical_square_swap (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    classicalRouting (classicalRouting p) = p.swap := rfl

theorem classical_fourth_identity (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    classicalRouting (classicalRouting (classicalRouting (classicalRouting p))) = p := rfl

theorem classical_bijective : Function.Bijective classicalRouting := by
  rw [← nat_mixer_eq_routing]
  apply mixer_bijective
  intro p
  simpa only [nat_mixer_eq_routing] using classical_square_swap p

theorem classical_not_transparent :
    ¬ ∀ x : ℕ × ℕ, natA x + natB x = x := by
  intro h
  have heq := congrArg Prod.fst (h (1, 0))
  norm_num [natA, natB] at heq

theorem nat_pair_has_no_inverse : ¬ ∃ y : ℕ × ℕ, (1, 0) + y = 0 := by
  rintro ⟨y, hy⟩
  have heq := congrArg Prod.fst hy
  change 1 + y.1 = 0 at heq
  omega

/-- Transparency and bijectivity without square-swap also permit no antipodal
cancellation/additive inverse; ordinary additive cancellation holds on ℕ. -/
theorem identity_transparent : ∀ x : ℕ, (1 : AddMonoid.End ℕ) x + (0 : AddMonoid.End ℕ) x = x :=
  fun x => add_zero x

theorem identity_mixer :
    mixer (1 : AddMonoid.End ℕ) 0 = id := by
  funext p
  simp [mixer]

theorem identity_mixer_bijective :
    Function.Bijective (mixer (1 : AddMonoid.End ℕ) 0) := by
  rw [identity_mixer]
  exact Function.bijective_id

theorem identity_not_square_swap :
    ¬ ∀ p : ℕ × ℕ, mixer (1 : AddMonoid.End ℕ) 0
      (mixer (1 : AddMonoid.End ℕ) 0 p) = p.swap := by
  intro hs
  have heq := congrArg Prod.fst (hs (1, 0))
  norm_num [identity_mixer] at heq

theorem nat_has_no_inverse : ¬ ∃ y : ℕ, 1 + y = 0 := by omega

end Controls

/-- Machine-visible scope: supplied model laws, conclusions, and open physical bridges. -/
inductive BoundaryRole
  | suppliedAdditiveCoherentSuperposition
  | suppliedCompleteTwoPortOutputs
  | suppliedCommonInputTransparency
  | suppliedExactRootOfSwap
  | suppliedCarrierClosure
  | symmetricChannelActionFollows
  | genuineHalfFollows
  | phaseFourthIterateIdentityFollows
  | antipodalCancellationFollows
  | selectedRoutingReconstructed
  | openPhysicalJustification
  | openSerialMultiplicativeDetectorResponse
  | openActualization
  | openFullQM
  | modelEquivalenceOnly
  | noPrimitiveInevitabilityClaim
  | noScientificStatusUpgrade
  | classicalControlsDistinctFromUniversalTheorem
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole :=
  [.suppliedAdditiveCoherentSuperposition, .suppliedCompleteTwoPortOutputs,
   .suppliedCommonInputTransparency, .suppliedExactRootOfSwap, .suppliedCarrierClosure,
   .symmetricChannelActionFollows, .genuineHalfFollows, .phaseFourthIterateIdentityFollows,
   .antipodalCancellationFollows, .selectedRoutingReconstructed,
   .openPhysicalJustification, .openSerialMultiplicativeDetectorResponse,
   .openActualization, .openFullQM, .modelEquivalenceOnly,
   .noPrimitiveInevitabilityClaim, .noScientificStatusUpgrade,
   .classicalControlsDistinctFromUniversalTheorem]

end IDT.QMClosure.TransparentSwapRoot
