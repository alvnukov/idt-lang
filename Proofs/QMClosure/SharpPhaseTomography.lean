import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic

/-! Algebraic consequences of a supplied complete destructive-map algebra.
The operational origin of these equations, CNOT conjugation, and reference
extension laws remains an external proof obligation. -/

namespace IDT.QMClosure.SharpPhaseTomography

section Ring

variable {A : Type*} [Ring A]

/-- Complete multiplication table for three destructive maps and their common part. -/
structure DestructiveAlgebra (A : Type*) [Ring A] where
  ex : A
  ey : A
  ez : A
  common : A
  xx : ex * ex = ex
  yy : ey * ey = ey
  zz : ez * ez = ez
  xy : ex * ey = common
  yx : ey * ex = common
  xz : ex * ez = common
  zx : ez * ex = common
  yz : ey * ez = common
  zy : ez * ey = common
  xr : ex * common = common
  rx : common * ex = common
  yr : ey * common = common
  ry : common * ey = common
  zr : ez * common = common
  rz : common * ez = common
  rr : common * common = common

def phase (e : A) : A := 2 * e - 1

def projector (d : DestructiveAlgebra A) : A := d.ex + d.ey + d.ez - 2 * d.common

theorem phase_involution (e : A) (he : e * e = e) : phase e * phase e = 1 := by
  unfold phase
  noncomm_ring [he]

theorem phase_commute (e f : A) (h : e * f = f * e) :
    phase e * phase f = phase f * phase e := by
  unfold phase
  noncomm_ring [h]

theorem three_phase_product (d : DestructiveAlgebra A) :
    phase d.ex * phase d.ey * phase d.ez = 2 * projector d - 1 := by
  unfold phase projector
  noncomm_ring [d.xy, d.xz, d.yz, d.rz]

theorem projector_idempotent (d : DestructiveAlgebra A) :
    projector d * projector d = projector d := by
  unfold projector
  noncomm_ring [d.xx, d.yy, d.zz, d.xy, d.yx, d.xz, d.zx, d.yz, d.zy,
    d.xr, d.rx, d.yr, d.ry, d.zr, d.rz, d.rr]

/-- The entire phase package follows from the supplied multiplication table. -/
theorem complete_phase_package (d : DestructiveAlgebra A) :
    phase d.ex * phase d.ex = 1 ∧ phase d.ey * phase d.ey = 1 ∧
    phase d.ez * phase d.ez = 1 ∧
    phase d.ex * phase d.ey = phase d.ey * phase d.ex ∧
    phase d.ex * phase d.ez = phase d.ez * phase d.ex ∧
    phase d.ey * phase d.ez = phase d.ez * phase d.ey ∧
    phase d.ex * phase d.ey * phase d.ez = 2 * projector d - 1 ∧
    projector d * projector d = projector d := by
  exact ⟨phase_involution _ d.xx, phase_involution _ d.yy, phase_involution _ d.zz,
    phase_commute _ _ (d.xy.trans d.yx.symm),
    phase_commute _ _ (d.xz.trans d.zx.symm),
    phase_commute _ _ (d.yz.trans d.zy.symm),
    three_phase_product d, projector_idempotent d⟩

end Ring

section Group

variable {G : Type*} [CommGroup G]

/-- A supplied conjugation homomorphism with the three CNOT phase identities
forces cancellation of the two local phase defects. -/
theorem cnot_defect_cancellation (φ : G →* G) (xA yA zA xB yB zB : G)
    (hx : φ xA = xA * xB) (hz : φ zB = zA * zB)
    (hjoint : φ (xA * zB) = yA * yB)
    (hyA : yA * yA = 1) (hyB : yB * yB = 1) :
    (xA * yA * zA) * (xB * yB * zB) = 1 := by
  have h : (xA * xB) * (zA * zB) = yA * yB := by
    simpa only [map_mul, hx, hz] using hjoint
  calc
    (xA * yA * zA) * (xB * yB * zB) =
        ((xA * xB) * (zA * zB)) * (yA * yB) := by ac_rfl
    _ = (yA * yB) * (yA * yB) := by rw [h]
    _ = (yA * yA) * (yB * yB) := by ac_rfl
    _ = 1 := by rw [hyA, hyB, one_mul]

end Group

section Reference

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- The old system V is arbitrary, so it may already include spectators. -/
theorem fresh_reference_erasure (append : V →ₗ[ℝ] W) (discard : W →ₗ[ℝ] V)
    (localDefect : Module.End ℝ V) (oldDefect freshDefect : Module.End ℝ W)
    (retract : discard.comp append = LinearMap.id)
    (equalDefects : oldDefect = freshDefect)
    (freshFixed : freshDefect.comp append = append)
    (oldAction : oldDefect.comp append = append.comp localDefect) :
    localDefect = LinearMap.id := by
  have h : append.comp localDefect = append := by
    rw [← oldAction, equalDefects, freshFixed]
  ext v
  have hv := congrArg (fun f : V →ₗ[ℝ] W => discard (f v)) h
  have hr (u : V) : discard (append u) = u :=
    LinearMap.congr_fun retract u
  simpa only [LinearMap.comp_apply, hr, LinearMap.id_apply] using hv

theorem projector_total_of_defect_identity (p : Module.End ℝ V)
    (h : 2 * p - 1 = 1) : p = 1 := by
  have htwo : (2 : Module.End ℝ V) * p = 1 + 1 := sub_eq_iff_eq_add.mp h
  ext v
  have hv := LinearMap.congr_fun htwo v
  simp only [Module.End.mul_apply, Module.End.ofNat_apply, two_smul,
    LinearMap.add_apply, Module.End.one_apply] at hv
  exact (smul_right_injective V (by norm_num : (2 : ℝ) ≠ 0)) (by simpa [two_smul] using hv)

/-- Fresh-reference erasure closes the projector only after all extension laws
and the local phase-defect formula have been supplied. -/
theorem fresh_reference_projector_total
    (append : V →ₗ[ℝ] W) (discard : W →ₗ[ℝ] V)
    (p localDefect : Module.End ℝ V) (oldDefect freshDefect : Module.End ℝ W)
    (retract : discard.comp append = LinearMap.id)
    (equalDefects : oldDefect = freshDefect)
    (freshFixed : freshDefect.comp append = append)
    (oldAction : oldDefect.comp append = append.comp localDefect)
    (formula : localDefect = 2 * p - 1) : p = 1 := by
  apply projector_total_of_defect_identity
  rw [← formula]
  exact fresh_reference_erasure append discard localDefect oldDefect freshDefect
    retract equalDefects freshFixed oldAction

end Reference

end IDT.QMClosure.SharpPhaseTomography
