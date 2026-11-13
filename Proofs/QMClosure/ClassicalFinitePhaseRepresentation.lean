import Proofs.QMClosure.SharpPhaseTomography
import Proofs.QMClosure.CnotPhaseDefectTransfer
import Mathlib.Data.Fintype.BigOperators

/-! A positive classical representation of the finite phase/destructive algebra.

The ambient states are all nonnegative rational distributions of total one on
four classical points. Six selected preparations form a separately specified
family and are mixtures in that full simplex. No restriction of the local base
is imposed while constructing the two-wire permutation representation.

The artifact tests finite algebraic selection alone. Ball geometry, rich SO(d)
controls, a consistent restricted toy-composite family and all-reference
pure-marginal atomicity remain separate obligations.
-/

namespace IDT.QMClosure.ClassicalFinitePhaseRepresentation

noncomputable section

open SharpPhaseTomography

abbrev Ω := Bool × Bool
abbrev Distribution (S : Type*) := S → ℚ
abbrev Local := Distribution Ω
abbrev Joint := Distribution (Ω × Ω)

def nonnegative {S : Type*} (ρ : Distribution S) : Prop := ∀ s, 0 ≤ ρ s

def total {S : Type*} [Fintype S] (ρ : Distribution S) : ℚ := ∑ s, ρ s

def normalized {S : Type*} [Fintype S] (ρ : Distribution S) : Prop :=
  nonnegative ρ ∧ total ρ = 1

def permutationAction {S : Type*} (e : S ≃ S) :
    Distribution S ≃ₗ[ℚ] Distribution S where
  toFun ρ s := ρ (e.symm s)
  invFun ρ s := ρ (e s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv ρ := by funext s; simp only [Equiv.symm_apply_apply]
  right_inv ρ := by funext s; simp only [Equiv.apply_symm_apply]

theorem permutation_positive {S : Type*} (e : S ≃ S)
    (ρ : Distribution S) (hρ : nonnegative ρ) : nonnegative (permutationAction e ρ) :=
  fun s => hρ (e.symm s)

theorem permutation_total {S : Type*} [Fintype S] (e : S ≃ S)
    (ρ : Distribution S) : total (permutationAction e ρ) = total ρ :=
  e.symm.sum_comp ρ

theorem permutation_normalized {S : Type*} [Fintype S] (e : S ≃ S)
    (ρ : Distribution S) (hρ : normalized ρ) : normalized (permutationAction e ρ) :=
  ⟨permutation_positive e ρ hρ.1, (permutation_total e ρ).trans hρ.2⟩

theorem permutation_inverse_normalized {S : Type*} [Fintype S] (e : S ≃ S)
    (ρ : Distribution S) (hρ : normalized ρ) :
    normalized ((permutationAction e).symm ρ) := permutation_normalized e.symm ρ hρ

def flipQ : Ω ≃ Ω where
  toFun s := (!s.1, s.2)
  invFun s := (!s.1, s.2)
  left_inv := by rintro ⟨q, p⟩; cases q <;> rfl
  right_inv := by rintro ⟨q, p⟩; cases q <;> rfl

def flipP : Ω ≃ Ω where
  toFun s := (s.1, !s.2)
  invFun s := (s.1, !s.2)
  left_inv := by rintro ⟨q, p⟩; cases p <;> rfl
  right_inv := by rintro ⟨q, p⟩; cases p <;> rfl

def flipBoth : Ω ≃ Ω where
  toFun s := (!s.1, !s.2)
  invFun s := (!s.1, !s.2)
  left_inv := by rintro ⟨q, p⟩; cases q <;> cases p <;> rfl
  right_inv := by rintro ⟨q, p⟩; cases q <;> cases p <;> rfl

theorem flipQ_symm_apply (s : Ω) : flipQ.symm s = (!s.1, s.2) := rfl
theorem flipP_symm_apply (s : Ω) : flipP.symm s = (s.1, !s.2) := rfl
theorem flipBoth_symm_apply (s : Ω) : flipBoth.symm s = (!s.1, !s.2) := rfl

def Jx : Module.End ℚ Local := (permutationAction flipQ).toLinearMap
def Jy : Module.End ℚ Local := (permutationAction flipBoth).toLinearMap
def Jz : Module.End ℚ Local := (permutationAction flipP).toLinearMap

def average {S : Type*} (e : S ≃ S) : Module.End ℚ (Distribution S) :=
  (1 / 2 : ℚ) • (1 + (permutationAction e).toLinearMap)

theorem average_apply {S : Type*} (e : S ≃ S) (ρ : Distribution S) (s : S) :
    average e ρ s = (1 / 2 : ℚ) * (ρ s + ρ (e.symm s)) := rfl

theorem average_positive {S : Type*} (e : S ≃ S)
    (ρ : Distribution S) (hρ : nonnegative ρ) : nonnegative (average e ρ) := by
  intro s
  change 0 ≤ (1 / 2 : ℚ) * (ρ s + ρ (e.symm s))
  exact mul_nonneg (by norm_num) (add_nonneg (hρ s) (hρ _))

theorem average_total {S : Type*} [Fintype S] (e : S ≃ S)
    (ρ : Distribution S) : total (average e ρ) = total ρ := by
  change (∑ s, (1 / 2 : ℚ) * (ρ s + ρ (e.symm s))) = ∑ s, ρ s
  rw [← Finset.mul_sum, Finset.sum_add_distrib, e.symm.sum_comp]
  ring

def common : Module.End ℚ Local := (1 / 4 : ℚ) • (1 + Jx + Jy + Jz)

theorem common_apply (ρ : Local) (s : Ω) :
    common ρ s = (1 / 4 : ℚ) *
      (ρ s + ρ (!s.1, s.2) + ρ (!s.1, !s.2) + ρ (s.1, !s.2)) := rfl

set_option maxHeartbeats 2000000 in
def destructive : DestructiveAlgebra (Module.End ℚ Local) := by
  refine {
    ex := average flipQ, ey := average flipBoth, ez := average flipP,
    common := common, xx := ?_, yy := ?_, zz := ?_, xy := ?_, yx := ?_,
    xz := ?_, zx := ?_, yz := ?_, zy := ?_, xr := ?_, rx := ?_, yr := ?_,
    ry := ?_, zr := ?_, rz := ?_, rr := ?_ }
  all_goals
    apply LinearMap.ext
    intro ρ
    funext ⟨q, p⟩
    cases q <;> cases p <;>
      simp only [Module.End.mul_apply, average_apply, common_apply,
        flipQ_symm_apply, flipP_symm_apply, flipBoth_symm_apply, Bool.not_false, Bool.not_true] <;> ring

theorem common_uniform (ρ : Local) (s : Ω) : common ρ s = total ρ / 4 := by
  rcases s with ⟨q, p⟩
  cases q <;> cases p <;>
    simp [common, total, Jx, Jy, Jz, permutationAction, flipQ, flipP, flipBoth,
      Fintype.sum_prod_type] <;> ring

theorem local_phase_x : phase destructive.ex = Jx := by
  apply LinearMap.ext
  intro ρ
  funext s
  simp [phase, destructive, average, Jx]

theorem local_phase_y : phase destructive.ey = Jy := by
  apply LinearMap.ext
  intro ρ
  funext s
  simp [phase, destructive, average, Jy]

theorem local_phase_z : phase destructive.ez = Jz := by
  apply LinearMap.ext
  intro ρ
  funext s
  simp [phase, destructive, average, Jz]

theorem local_projector_total : projector destructive = 1 := by
  apply LinearMap.ext
  intro ρ
  funext s
  simp [projector, destructive, average, common, Jx, Jy, Jz]
  ring

theorem local_phase_package :
    Jx * Jx = 1 ∧ Jy * Jy = 1 ∧ Jz * Jz = 1 ∧
      Jx * Jy = Jy * Jx ∧ Jx * Jz = Jz * Jx ∧ Jy * Jz = Jz * Jy ∧
      Jx * Jy * Jz = 1 := by
  obtain ⟨hxx, hyy, hzz, hxy, hxz, hyz, hprod, _⟩ := complete_phase_package destructive
  simp only [local_phase_x, local_phase_y, local_phase_z, local_projector_total] at *
  norm_num at hprod
  exact ⟨hxx, hyy, hzz, hxy, hxz, hyz, hprod⟩

theorem local_phases_normalized (ρ : Local) (hρ : normalized ρ) :
    normalized (Jx ρ) ∧ normalized (Jy ρ) ∧ normalized (Jz ρ) :=
  ⟨permutation_normalized flipQ ρ hρ, permutation_normalized flipBoth ρ hρ,
    permutation_normalized flipP ρ hρ⟩

def liftA : Module.End ℚ Local →+* Module.End ℚ Joint where
  toFun M := {
    toFun ρ s := M (fun a => ρ (a, s.2)) s.1
    map_add' := by
      intro ρ σ
      funext s
      exact congrArg (fun f : Local => f s.1)
        (M.map_add (fun a => ρ (a, s.2)) (fun a => σ (a, s.2)))
    map_smul' := by
      intro c ρ
      funext s
      exact congrArg (fun f : Local => f s.1) (M.map_smul c (fun a => ρ (a, s.2))) }
  map_zero' := by apply LinearMap.ext; intro ρ; funext s; rfl
  map_one' := by apply LinearMap.ext; intro ρ; funext s; rfl
  map_add' _ _ := by apply LinearMap.ext; intro ρ; funext s; rfl
  map_mul' _ _ := by apply LinearMap.ext; intro ρ; funext s; rfl

def liftB : Module.End ℚ Local →+* Module.End ℚ Joint where
  toFun M := {
    toFun ρ s := M (fun b => ρ (s.1, b)) s.2
    map_add' := by
      intro ρ σ
      funext s
      exact congrArg (fun f : Local => f s.2)
        (M.map_add (fun b => ρ (s.1, b)) (fun b => σ (s.1, b)))
    map_smul' := by
      intro c ρ
      funext s
      exact congrArg (fun f : Local => f s.2) (M.map_smul c (fun b => ρ (s.1, b))) }
  map_zero' := by apply LinearMap.ext; intro ρ; funext s; rfl
  map_one' := by apply LinearMap.ext; intro ρ; funext s; rfl
  map_add' _ _ := by apply LinearMap.ext; intro ρ; funext s; rfl
  map_mul' _ _ := by apply LinearMap.ext; intro ρ; funext s; rfl

def mapDestructive {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (d : DestructiveAlgebra R) : DestructiveAlgebra S := {
  ex := f d.ex, ey := f d.ey, ez := f d.ez, common := f d.common
  xx := by simpa only [map_mul] using congrArg f d.xx
  yy := by simpa only [map_mul] using congrArg f d.yy
  zz := by simpa only [map_mul] using congrArg f d.zz
  xy := by simpa only [map_mul] using congrArg f d.xy
  yx := by simpa only [map_mul] using congrArg f d.yx
  xz := by simpa only [map_mul] using congrArg f d.xz
  zx := by simpa only [map_mul] using congrArg f d.zx
  yz := by simpa only [map_mul] using congrArg f d.yz
  zy := by simpa only [map_mul] using congrArg f d.zy
  xr := by simpa only [map_mul] using congrArg f d.xr
  rx := by simpa only [map_mul] using congrArg f d.rx
  yr := by simpa only [map_mul] using congrArg f d.yr
  ry := by simpa only [map_mul] using congrArg f d.ry
  zr := by simpa only [map_mul] using congrArg f d.zr
  rz := by simpa only [map_mul] using congrArg f d.rz
  rr := by simpa only [map_mul] using congrArg f d.rr }

theorem mapped_phase {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (E : R) :
    phase (f E) = f (phase E) := by simp only [phase, two_mul, map_sub, map_add, map_one]

def destructiveA := mapDestructive liftA destructive
def destructiveB := mapDestructive liftB destructive

def cnotPermutation : (Ω × Ω) ≃ (Ω × Ω) where
  toFun s := ((s.1.1, Bool.xor s.1.2 s.2.2), (Bool.xor s.2.1 s.1.1, s.2.2))
  invFun s := ((s.1.1, Bool.xor s.1.2 s.2.2), (Bool.xor s.2.1 s.1.1, s.2.2))
  left_inv := by
    rintro ⟨⟨qA, pA⟩, ⟨qB, pB⟩⟩
    cases qA <;> cases pA <;> cases qB <;> cases pB <;> rfl
  right_inv := by
    rintro ⟨⟨qA, pA⟩, ⟨qB, pB⟩⟩
    cases qA <;> cases pA <;> cases qB <;> cases pB <;> rfl

def G : Module.End ℚ Joint := (permutationAction cnotPermutation).toLinearMap

theorem G_normalized (ρ : Joint) (hρ : normalized ρ) : normalized (G ρ) :=
  permutation_normalized cnotPermutation ρ hρ

theorem G_involutive : G * G = 1 := by
  apply LinearMap.ext
  intro ρ
  funext ⟨⟨qA, pA⟩, ⟨qB, pB⟩⟩
  cases qA <;> cases pA <;> cases qB <;> cases pB <;> rfl

def conjugation : Module.End ℚ Joint →* Module.End ℚ Joint where
  toFun M := G * M * G
  map_one' := by simp only [mul_one, G_involutive]
  map_mul' M N := by
    symm
    calc
      (G * M * G) * (G * N * G) = G * M * (G * G) * N * G := by simp only [mul_assoc]
      _ = G * (M * N) * G := by rw [G_involutive]; simp only [mul_one, mul_assoc]

theorem conjugate_xA : conjugation (liftA Jx) = liftA Jx * liftB Jx := by
  apply LinearMap.ext
  intro ρ
  funext ⟨⟨qA, pA⟩, ⟨qB, pB⟩⟩
  cases qA <;> cases pA <;> cases qB <;> cases pB <;> rfl

theorem conjugate_zB : conjugation (liftB Jz) = liftA Jz * liftB Jz := by
  apply LinearMap.ext
  intro ρ
  funext ⟨⟨qA, pA⟩, ⟨qB, pB⟩⟩
  cases qA <;> cases pA <;> cases qB <;> cases pB <;> rfl

theorem conjugate_xA_zB : conjugation (liftA Jx * liftB Jz) = liftA Jy * liftB Jy := by
  apply LinearMap.ext
  intro ρ
  funext ⟨⟨qA, pA⟩, ⟨qB, pB⟩⟩
  cases qA <;> cases pA <;> cases qB <;> cases pB <;> rfl

theorem required_cross_commutations :
    Commute (liftA Jy) (liftB Jx) ∧ Commute (liftA Jy) (liftB Jz) ∧
      Commute (liftA Jy) (liftB Jy) ∧ Commute (liftB Jx) (liftA Jz) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply LinearMap.ext
    intro ρ
    funext s
    rfl

/-- The actual operator representation consumes the existing CNOT transfer theorem. -/
theorem actual_cnot_defects_equal :
    CnotPhaseDefectTransfer.phaseDefect destructiveA =
      CnotPhaseDefectTransfer.phaseDefect destructiveB := by
  obtain ⟨hYX, hYZ, hYY, hXZ⟩ := required_cross_commutations
  apply CnotPhaseDefectTransfer.destructive_defects_equal destructiveA destructiveB conjugation
  · simpa only [destructiveA, destructiveB, mapDestructive, mapped_phase, local_phase_x] using conjugate_xA
  · simpa only [destructiveA, destructiveB, mapDestructive, mapped_phase, local_phase_z] using conjugate_zB
  · simpa only [destructiveA, destructiveB, mapDestructive, mapped_phase,
      local_phase_x, local_phase_y, local_phase_z] using conjugate_xA_zB
  · simpa only [destructiveA, destructiveB, mapDestructive, mapped_phase,
      local_phase_x, local_phase_y] using hYX
  · simpa only [destructiveA, destructiveB, mapDestructive, mapped_phase,
      local_phase_y, local_phase_z] using hYZ
  · simpa only [destructiveA, destructiveB, mapDestructive, mapped_phase, local_phase_y] using hYY
  · simpa only [destructiveA, destructiveB, mapDestructive, mapped_phase,
      local_phase_x, local_phase_z] using hXZ

def axisValue (axis : Fin 3) (s : Ω) : Bool := ![s.2, Bool.xor s.1 s.2, s.1] axis

def sign (b : Bool) : ℚ := if b then -1 else 1

def preparation (axis : Fin 3) (outcome : Bool) : Local :=
  fun s => if axisValue axis s = outcome then 1 / 2 else 0

def coordinates (ρ : Local) : Fin 3 → ℚ :=
  fun axis => ∑ s, sign (axisValue axis s) * ρ s

def uniform : Local := fun _ => 1 / 4

theorem preparation_normalized (axis : Fin 3) (outcome : Bool) :
    normalized (preparation axis outcome) := by
  constructor
  · intro s
    simp only [preparation]
    split_ifs <;> norm_num
  · fin_cases axis <;> cases outcome <;>
      norm_num [total, preparation, axisValue, Fintype.sum_prod_type, Fintype.sum_bool]

theorem preparation_coordinates (axis i : Fin 3) (outcome : Bool) :
    coordinates (preparation axis outcome) i = if i = axis then sign outcome else 0 := by
  fin_cases axis <;> fin_cases i <;> cases outcome <;>
    norm_num [coordinates, preparation, axisValue, sign, Fintype.sum_prod_type, Fintype.sum_bool]

theorem preparation_common_midpoint (axis : Fin 3) :
    (1 / 2 : ℚ) • (preparation axis false + preparation axis true) = uniform := by
  funext s
  change (1 / 2 : ℚ) * (preparation axis false s + preparation axis true s) = 1 / 4
  cases h : axisValue axis s <;> norm_num [preparation, h]

def pointMass (s : Ω) : Local := fun t => if t = s then 1 else 0

theorem pointMass_normalized (s : Ω) : normalized (pointMass s) := by
  constructor
  · intro t
    simp only [pointMass]
    split_ifs <;> norm_num
  · simp [total, pointMass]

/-- Each selected preparation is mixed in the full classical simplex. -/
theorem preparation_two_point_mixture (axis : Fin 3) (outcome : Bool) :
    ∃ s t : Ω, s ≠ t ∧ preparation axis outcome =
      (1 / 2 : ℚ) • (pointMass s + pointMass t) := by
  fin_cases axis <;> cases outcome <;> decide +kernel

/-- The full classical distribution cone violates the unit quadratic bound
in these character coordinates. This states the tested coordinate exclusion. -/
theorem point_mass_violates_unit_quadratic_bound :
    normalized (pointMass (false, false)) ∧
      (∑ i : Fin 3, (coordinates (pointMass (false, false)) i) ^ 2) = 3 ∧
      1 < ∑ i : Fin 3, (coordinates (pointMass (false, false)) i) ^ 2 := by
  have hcoord (i : Fin 3) : coordinates (pointMass (false, false)) i = 1 := by
    fin_cases i <;>
      norm_num [coordinates, pointMass, axisValue, sign, Fintype.sum_prod_type, Fintype.sum_bool]
  have hsum : (∑ i : Fin 3, (coordinates (pointMass (false, false)) i) ^ 2) = 3 := by
    simp only [hcoord, one_pow]
    norm_num
  exact ⟨pointMass_normalized _, hsum, by rw [hsum]; norm_num⟩

end

end IDT.QMClosure.ClassicalFinitePhaseRepresentation
