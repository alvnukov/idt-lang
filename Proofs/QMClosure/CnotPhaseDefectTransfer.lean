import Proofs.QMClosure.SharpPhaseTomography

/-! Finite phase-commutation interface for CNOT defect transfer.

The monoid calculation applies to noncommutative operator rings. The supplied
homomorphism and its three phase identities form an algebraic contract. Their
realization by an operational conjugation, destructive processes, and natural
fresh-reference extensions remains an explicit external obligation.
-/

namespace IDT.QMClosure.CnotPhaseDefectTransfer

open SharpPhaseTomography

section Monoid

variable {A : Type*} [Monoid A]

/-- A product of two commuting involutions is involutive. -/
theorem commuting_involutions_mul (x y : A) (hxy : Commute x y)
    (hxx : x * x = 1) (hyy : y * y = 1) :
    (x * y) * (x * y) = 1 := by
  calc
    (x * y) * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
    _ = (x * x) * (y * y) := by rw [hxy.symm.eq]; simp only [mul_assoc]
    _ = 1 := by rw [hxx, hyy, one_mul]

/-- Only the three stated local commutations are used for a local defect. -/
theorem three_phase_involution (x y z : A)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (hxx : x * x = 1) (hyy : y * y = 1) (hzz : z * z = 1) :
    (x * y * z) * (x * y * z) = 1 := by
  exact commuting_involutions_mul (x * y) z (hxz.mul_left hyz)
    (commuting_involutions_mul x y hxy hxx hyy) hzz

/-- The CNOT phase equations cancel defects using six explicit commutations.
No commutative structure on the ambient monoid or operator ring is required. -/
theorem cnot_defect_cancellation (φ : A →* A)
    (xA yA zA xB yB zB : A)
    (hx : φ xA = xA * xB) (hz : φ zB = zA * zB)
    (hjoint : φ (xA * zB) = yA * yB)
    (hyA : yA * yA = 1) (hyB : yB * yB = 1)
    (hyAzA : Commute yA zA) (hyAxB : Commute yA xB)
    (hyAzB : Commute yA zB) (hyAyB : Commute yA yB)
    (hyBzB : Commute yB zB) (hxBzA : Commute xB zA) :
    (xA * yA * zA) * (xB * yB * zB) = 1 := by
  have h : (xA * xB) * (zA * zB) = yA * yB := by
    simpa only [map_mul, hx, hz] using hjoint
  have hreorder : (xA * yA * zA) * (xB * yB * zB) =
      ((xA * xB) * (zA * zB)) * (yA * yB) := by
    simp only [mul_assoc]
    rw [hyAzA.left_comm, hyAxB.left_comm, hxBzA.symm.left_comm,
      hyBzB.eq, hyAzB.left_comm]
  rw [hreorder, h]
  exact commuting_involutions_mul yA yB hyAyB hyA hyB

/-- Cancellation and involutivity of the second defect give equality of defects. -/
theorem defects_equal_of_cancel (KA KB : A)
    (hcancel : KA * KB = 1) (hKB : KB * KB = 1) : KA = KB := by
  calc
    KA = KA * (KB * KB) := by rw [hKB, mul_one]
    _ = (KA * KB) * KB := by rw [mul_assoc]
    _ = KB := by rw [hcancel, one_mul]

end Monoid

section Ring

variable {A : Type*} [Ring A]

def phaseDefect (d : DestructiveAlgebra A) : A :=
  phase d.ex * phase d.ey * phase d.ez

/-- Local involutions and local commutations come from the destructive tables.
The four cross-system phase commutations and three homomorphism equations remain
explicit inputs. Together they derive the equality required for reference erasure. -/
theorem destructive_defects_equal
    (dOld dFresh : DestructiveAlgebra A) (φ : A →* A)
    (hx : φ (phase dOld.ex) = phase dOld.ex * phase dFresh.ex)
    (hz : φ (phase dFresh.ez) = phase dOld.ez * phase dFresh.ez)
    (hjoint : φ (phase dOld.ex * phase dFresh.ez) =
      phase dOld.ey * phase dFresh.ey)
    (hyAxB : Commute (phase dOld.ey) (phase dFresh.ex))
    (hyAzB : Commute (phase dOld.ey) (phase dFresh.ez))
    (hyAyB : Commute (phase dOld.ey) (phase dFresh.ey))
    (hxBzA : Commute (phase dFresh.ex) (phase dOld.ez)) :
    phaseDefect dOld = phaseDefect dFresh := by
  obtain ⟨_, hyA, _, _, _, hyAzA, _, _⟩ := complete_phase_package dOld
  obtain ⟨hxB, hyB, hzB, hxByB, hxBzB, hyBzB, _, _⟩ :=
    complete_phase_package dFresh
  have hcancel : phaseDefect dOld * phaseDefect dFresh = 1 :=
    cnot_defect_cancellation φ _ _ _ _ _ _ hx hz hjoint hyA hyB
      hyAzA hyAxB hyAzB hyAyB hyBzB hxBzA
  have hFresh : phaseDefect dFresh * phaseDefect dFresh = 1 :=
    three_phase_involution _ _ _ hxByB hxBzB hyBzB hxB hyB hzB
  exact defects_equal_of_cancel _ _ hcancel hFresh

end Ring

section Reference

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- The operator-level phase calculation derives equal defects before applying
fresh-reference projector totality. The append/discard and intertwining laws,
the local defect formula, and the phase-homomorphism contract are supplied. -/
theorem cnot_fresh_reference_projector_total
    (dOld dFresh : DestructiveAlgebra (Module.End ℝ W))
    (φ : Module.End ℝ W →* Module.End ℝ W)
    (hx : φ (phase dOld.ex) = phase dOld.ex * phase dFresh.ex)
    (hz : φ (phase dFresh.ez) = phase dOld.ez * phase dFresh.ez)
    (hjoint : φ (phase dOld.ex * phase dFresh.ez) =
      phase dOld.ey * phase dFresh.ey)
    (hyAxB : Commute (phase dOld.ey) (phase dFresh.ex))
    (hyAzB : Commute (phase dOld.ey) (phase dFresh.ez))
    (hyAyB : Commute (phase dOld.ey) (phase dFresh.ey))
    (hxBzA : Commute (phase dFresh.ex) (phase dOld.ez))
    (append : V →ₗ[ℝ] W) (discard : W →ₗ[ℝ] V)
    (p localDefect : Module.End ℝ V)
    (retract : discard.comp append = LinearMap.id)
    (freshFixed : (phaseDefect dFresh).comp append = append)
    (oldAction : (phaseDefect dOld).comp append = append.comp localDefect)
    (formula : localDefect = 2 * p - 1) : p = 1 := by
  have equalDefects := destructive_defects_equal dOld dFresh φ hx hz hjoint
    hyAxB hyAzB hyAyB hxBzA
  exact fresh_reference_projector_total append discard p localDefect
    (phaseDefect dOld) (phaseDefect dFresh) retract equalDefects freshFixed oldAction formula

end Reference

end IDT.QMClosure.CnotPhaseDefectTransfer
