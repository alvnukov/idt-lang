import Proofs.QMClosure.RawPairPlaneExtension
import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.Nat.Basic

/-!
# Completion through countably many stages

The direct limit preserves every finite-stage weight and coordinate. A tower
that covers each old distinct pair at its next stage therefore yields a complete
atlas, with no global linear structure assumed.
-/

namespace IDT.QMClosure.RawPairPlaneAtlas

universe u

/-- A chain of injective extensions that covers each pair one stage later. -/
structure AtlasTower where
  stage : ℕ → PartialAtlas.{u}
  step : ∀ n, Extension (stage n) (stage (n + 1))
  pair_covered_next : ∀ n (r s : (stage n).Ray), r ≠ s →
    ∃ p a b, (stage (n + 1)).coord p a = (step n).ray r ∧
      (stage (n + 1)).coord p b = (step n).ray s

namespace AtlasTower

variable (T : AtlasTower.{u})

def rayTransition (n m : ℕ) (h : n ≤ m) : (T.stage n).Ray → (T.stage m).Ray :=
  Nat.leRecOn h (fun {k} => (T.step k).ray)

def planeTransition (n m : ℕ) (h : n ≤ m) : (T.stage n).Plane → (T.stage m).Plane :=
  Nat.leRecOn h (fun {k} => (T.step k).plane)

theorem rayTransition_injective (n m : ℕ) (h : n ≤ m) :
    Function.Injective (T.rayTransition n m h) :=
  Nat.leRecOn_injective h _ (fun k => (T.step k).ray.injective)

theorem planeTransition_injective (n m : ℕ) (h : n ≤ m) :
    Function.Injective (T.planeTransition n m h) :=
  Nat.leRecOn_injective h _ (fun k => (T.step k).plane.injective)

instance rayDirectedSystem : DirectedSystem (fun n => (T.stage n).Ray)
    (fun {n m} h => T.rayTransition n m h) where
  map_self {_} x := by
    exact Nat.leRecOn_self (C := fun n => (T.stage n).Ray)
      (next := fun {k} r => (T.step k).ray r) x
  map_map {_ _ _} h k x := by
    exact (Nat.leRecOn_trans (C := fun n => (T.stage n).Ray)
      (next := fun {k} r => (T.step k).ray r) h k x).symm

instance planeDirectedSystem : DirectedSystem (fun n => (T.stage n).Plane)
    (fun {n m} h => T.planeTransition n m h) where
  map_self {_} x := by
    exact Nat.leRecOn_self (C := fun n => (T.stage n).Plane)
      (next := fun {k} p => (T.step k).plane p) x
  map_map {_ _ _} h k x := by
    exact (Nat.leRecOn_trans (C := fun n => (T.stage n).Plane)
      (next := fun {k} p => (T.step k).plane p) h k x).symm

theorem weight_transition (n m : ℕ) (h : n ≤ m) (r : (T.stage n).Ray) :
    (T.stage m).weight (T.rayTransition n m h r) = (T.stage n).weight r := by
  induction h with
  | refl => simp [rayTransition, Nat.leRecOn_self]
  | @step m h ih =>
    rw [rayTransition, Nat.leRecOn_succ h, (T.step m).weight_map]
    exact ih

theorem coord_transition (n m : ℕ) (h : n ≤ m) (p : (T.stage n).Plane)
    (t : Option ℂ) :
    (T.stage m).coord (T.planeTransition n m h p) t =
      T.rayTransition n m h ((T.stage n).coord p t) := by
  induction h with
  | refl => simp [rayTransition, planeTransition, Nat.leRecOn_self]
  | @step m h ih =>
    rw [planeTransition, Nat.leRecOn_succ h, (T.step m).coord_map,
      rayTransition, Nat.leRecOn_succ h]
    exact congrArg (T.step m).ray ih

/-- The canonical extension between two comparable finite stages. -/
def transition (n m : ℕ) (h : n ≤ m) : Extension (T.stage n) (T.stage m) where
  ray := ⟨T.rayTransition n m h, T.rayTransition_injective n m h⟩
  plane := ⟨T.planeTransition n m h, T.planeTransition_injective n m h⟩
  weight_map := T.weight_transition n m h
  coord_map := T.coord_transition n m h

def rayMap (n m : ℕ) (h : n ≤ m) : (T.stage n).Ray ↪ (T.stage m).Ray :=
  (T.transition n m h).ray

def planeMap (n m : ℕ) (h : n ≤ m) : (T.stage n).Plane ↪ (T.stage m).Plane :=
  (T.transition n m h).plane

instance rayMapDirectedSystem : DirectedSystem (fun n => (T.stage n).Ray)
    (fun {n m} h => T.rayMap n m h) := T.rayDirectedSystem

instance planeMapDirectedSystem : DirectedSystem (fun n => (T.stage n).Plane)
    (fun {n m} h => T.planeMap n m h) := T.planeDirectedSystem

abbrev RayLimit := DirectLimit (fun n => (T.stage n).Ray) T.rayMap
abbrev PlaneLimit := DirectLimit (fun n => (T.stage n).Plane) T.planeMap

def rayIn (n : ℕ) : (T.stage n).Ray ↪ T.RayLimit :=
  ⟨fun r => ⟦⟨n, r⟩⟧, DirectLimit.mk_injective T.rayMap
    (T.rayTransition_injective) n⟩

def planeIn (n : ℕ) : (T.stage n).Plane ↪ T.PlaneLimit :=
  ⟨fun p => ⟦⟨n, p⟩⟧, DirectLimit.mk_injective T.planeMap
    (T.planeTransition_injective) n⟩

theorem rayIn_transition (n m : ℕ) (h : n ≤ m) (r : (T.stage n).Ray) :
    T.rayIn m (T.rayTransition n m h r) = T.rayIn n r :=
  (DirectLimit.eq_of_le (F := fun n => (T.stage n).Ray)
    (f := T.rayMap) ⟨n, r⟩ m h).symm

theorem planeIn_transition (n m : ℕ) (h : n ≤ m) (p : (T.stage n).Plane) :
    T.planeIn m (T.planeTransition n m h p) = T.planeIn n p :=
  (DirectLimit.eq_of_le (F := fun n => (T.stage n).Plane)
    (f := T.planeMap) ⟨n, p⟩ m h).symm

def limitWeight : T.RayLimit → ℝ :=
  DirectLimit.lift T.rayMap (fun n => (T.stage n).weight)
    (fun n m h r => (T.weight_transition n m h r).symm)

def limitCoord (p : T.PlaneLimit) (t : Option ℂ) : T.RayLimit :=
  DirectLimit.map T.planeMap T.rayMap
    (fun n p => (T.stage n).coord p t)
    (fun n m h p => (T.coord_transition n m h p t).symm) p

@[simp] theorem limitWeight_rayIn (n : ℕ) (r : (T.stage n).Ray) :
    T.limitWeight (T.rayIn n r) = (T.stage n).weight r := rfl

@[simp] theorem limitCoord_planeIn (n : ℕ) (p : (T.stage n).Plane) (t : Option ℂ) :
    T.limitCoord (T.planeIn n p) t = T.rayIn n ((T.stage n).coord p t) := rfl

theorem limitCoord_injective (p : T.PlaneLimit) :
    Function.Injective (T.limitCoord p) := by
  refine DirectLimit.induction T.planeMap (fun n p => ?_) p
  intro s t h
  exact ((T.stage n).coord p).injective ((T.rayIn n).injective h)

/-- The direct-limit atlas retains the finite-stage intersection restriction. -/
def limitPartialAtlas : PartialAtlas.{u} where
  Ray := T.RayLimit
  Plane := T.PlaneLimit
  weight := T.limitWeight
  weight_pos r := by
    refine DirectLimit.induction T.rayMap (fun n r => ?_) r
    exact (T.stage n).weight_pos r
  coord p := ⟨T.limitCoord p, T.limitCoord_injective p⟩
  weight_coord p t := by
    refine DirectLimit.induction T.planeMap (fun n p => ?_) p
    exact (T.stage n).weight_coord p t
  two_points p q := by
    refine DirectLimit.induction₂ T.planeMap (fun n p q => ?_) p q
    intro s t s' t' hst hs ht
    have hpq := (T.stage n).two_points p q s t s' t' hst
      ((T.rayIn n).injective hs) ((T.rayIn n).injective ht)
    exact congrArg (T.planeIn n) hpq

/-- Every finite stage embeds canonically into the direct-limit atlas. -/
def inclusion (n : ℕ) : Extension (T.stage n) T.limitPartialAtlas where
  ray := T.rayIn n
  plane := T.planeIn n
  weight_map _ := rfl
  coord_map _ _ := rfl

theorem inclusion_ray_compat (n m : ℕ) (h : n ≤ m) (r : (T.stage n).Ray) :
    (T.inclusion m).ray ((T.transition n m h).ray r) = (T.inclusion n).ray r :=
  T.rayIn_transition n m h r

theorem inclusion_plane_compat (n m : ℕ) (h : n ≤ m) (p : (T.stage n).Plane) :
    (T.inclusion m).plane ((T.transition n m h).plane p) = (T.inclusion n).plane p :=
  T.planeIn_transition n m h p

theorem limit_pair_covered (r s : T.RayLimit) (hrs : r ≠ s) :
    ∃ p a b, T.limitCoord p a = r ∧ T.limitCoord p b = s := by
  obtain ⟨n, r, s, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ T.rayMap r s
  have hne : r ≠ s := fun h => hrs (congrArg (T.rayIn n) h)
  obtain ⟨p, a, b, ha, hb⟩ := T.pair_covered_next n r s hne
  refine ⟨T.planeIn (n + 1) p, a, b, ?_, ?_⟩
  · rw [T.limitCoord_planeIn, ha]
    simpa [rayTransition, Nat.leRecOn_succ'] using
      T.rayIn_transition n (n + 1) (Nat.le_succ n) r
  · rw [T.limitCoord_planeIn, hb]
    simpa [rayTransition, Nat.leRecOn_succ'] using
      T.rayIn_transition n (n + 1) (Nat.le_succ n) s

/-- A nontrivial seed gives a genuinely nontrivial complete atlas. -/
def completeAtlas [Nontrivial (T.stage 0).Ray] : CompleteAtlas.{u} where
  toPartialAtlas := T.limitPartialAtlas
  ray_nontrivial := Function.Injective.nontrivial (T.rayIn 0).injective
  pair_covered := T.limit_pair_covered

end AtlasTower

noncomputable section

/-- Three initial rays of unit weight, before any planes are adjoined. -/
def threeRaySeed : PartialAtlas where
  Ray := Fin 3
  Plane := Empty
  weight _ := 1
  weight_pos _ := zero_lt_one
  coord p := Empty.elim p
  weight_coord p := Empty.elim p
  two_points p := Empty.elim p

def completionStage : ℕ → PartialAtlas
  | 0 => threeRaySeed
  | n + 1 => nextAtlas (completionStage n)

/-- The actual iterative pair-adjunction tower from three independent rays. -/
def threeRayTower : AtlasTower where
  stage := completionStage
  step n := stepExtension (completionStage n)
  pair_covered_next n r s h := pair_covered_next (completionStage n) r s h

instance threeRayTower_seed_nontrivial : Nontrivial (threeRayTower.stage 0).Ray :=
  inferInstanceAs (Nontrivial (Fin 3))

/-- A constructed inhabitant of the complete weighted pair-plane atlas interface. -/
def constructedCompleteAtlas : CompleteAtlas := threeRayTower.completeAtlas

/-- All construction stages retain their exact coordinates and weights. -/
def completionInclusion (n : ℕ) :
    Extension (completionStage n) constructedCompleteAtlas.toPartialAtlas :=
  threeRayTower.inclusion n

end

end IDT.QMClosure.RawPairPlaneAtlas
