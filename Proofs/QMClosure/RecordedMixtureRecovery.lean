import Proofs.QMClosure.PositiveMixtureRecoveryObstruction
import Mathlib.LinearAlgebra.Prod

/-! Positive recovery of a mixture with its branch label retained.

The recorded channel encodes into a larger classical-record space and has a
positive normalized left recovery. Reversibility on the original carrier and
physical origins of the supplied reversible branch remain separate questions.
The concrete bit family supplies exact recorded recovery and a positive-recovery
obstruction after the record is discarded.
-/

namespace IDT.QMClosure.RecordedMixtureRecovery

noncomputable section

open Set

section Record

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def recordMap (J : V ≃ₗ[ℝ] V) (a b : ℝ) : V →ₗ[ℝ] V × V :=
  (a • (LinearMap.id : V →ₗ[ℝ] V)).prod (b • J.toLinearMap)

def recoveryMap (J : V ≃ₗ[ℝ] V) : V × V →ₗ[ℝ] V :=
  LinearMap.fst ℝ V V + J.symm.toLinearMap.comp (LinearMap.snd ℝ V V)

def discardMap : V × V →ₗ[ℝ] V := LinearMap.fst ℝ V V + LinearMap.snd ℝ V V

def jointUnit (u : V →ₗ[ℝ] ℝ) : V × V →ₗ[ℝ] ℝ :=
  u.comp (LinearMap.fst ℝ V V) + u.comp (LinearMap.snd ℝ V V)

/-- Retaining the label permits exact recovery by the supplied inverse branch. -/
theorem recovery_record_identity (J : V ≃ₗ[ℝ] V) (a b : ℝ) (hsum : a + b = 1) :
    (recoveryMap J).comp (recordMap J a b) = LinearMap.id := by
  ext x
  change a • x + J.symm (b • J x) = x
  rw [map_smul, J.symm_apply_apply, ← add_smul, hsum, one_smul]

theorem record_positive
    (K : Set V) (J : V ≃ₗ[ℝ] V) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ K, r • x ∈ K)
    (hJ : MapsTo J K K) : MapsTo (recordMap J a b) K (K.prod K) := by
  intro x hx
  exact ⟨hscale a ha x hx, hscale b hb (J x) (hJ hx)⟩

theorem recovery_positive
    (K : Set V) (J : V ≃ₗ[ℝ] V)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hinv : MapsTo J.symm K K) : MapsTo (recoveryMap J) (K.prod K) K := by
  intro z hz
  exact hadd z.1 hz.1 (J.symm z.2) (hinv hz.2)

theorem discard_positive
    (K : Set V) (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) :
    MapsTo (discardMap : V × V →ₗ[ℝ] V) (K.prod K) K := by
  intro z hz
  exact hadd z.1 hz.1 z.2 hz.2

theorem record_unit_preserving
    (J : V ≃ₗ[ℝ] V) (u : V →ₗ[ℝ] ℝ) (a b : ℝ) (hsum : a + b = 1)
    (hunit : u.comp J.toLinearMap = u) :
    (jointUnit u).comp (recordMap J a b) = u := by
  ext x
  have hu : u (J x) = u x := DFunLike.congr_fun hunit x
  change u (a • x) + u (b • J x) = u x
  simp only [map_smul, smul_eq_mul]
  rw [hu, ← add_mul, hsum, one_mul]

theorem recovery_unit_preserving
    (J : V ≃ₗ[ℝ] V) (u : V →ₗ[ℝ] ℝ) (hunit : u.comp J.toLinearMap = u) :
    u.comp (recoveryMap J) = jointUnit u := by
  have hinv (y : V) : u (J.symm y) = u y := by
    have h := DFunLike.congr_fun hunit (J.symm y)
    change u (J (J.symm y)) = u (J.symm y) at h
    rw [J.apply_symm_apply] at h
    exact h.symm
  apply LinearMap.ext
  intro z
  change u (z.1 + J.symm z.2) = u z.1 + u z.2
  rw [map_add, hinv]

theorem discard_unit_preserving (u : V →ₗ[ℝ] ℝ) :
    u.comp (discardMap : V × V →ₗ[ℝ] V) = jointUnit u := by
  apply LinearMap.ext
  intro z
  exact u.map_add z.1 z.2

/-- Discarding the label gives the original mixture of the two branches. -/
theorem discard_record_mixture (J : V ≃ₗ[ℝ] V) (a b : ℝ) :
    (discardMap : V × V →ₗ[ℝ] V).comp (recordMap J a b) =
      a • LinearMap.id + b • J.toLinearMap := by
  ext x
  rfl

theorem record_normalized_state
    (K : Set V) (J : V ≃ₗ[ℝ] V) (u : V →ₗ[ℝ] ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b = 1)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ K, r • x ∈ K)
    (hJ : MapsTo J K K) (hunit : u.comp J.toLinearMap = u) :
    MapsTo (recordMap J a b) {x | x ∈ K ∧ u x = 1}
      {z | z ∈ K.prod K ∧ jointUnit u z = 1} := by
  intro x hx
  refine ⟨record_positive K J a b ha hb hscale hJ hx.1, ?_⟩
  have h := DFunLike.congr_fun (record_unit_preserving J u a b hsum hunit) x
  exact h.trans hx.2

theorem recovery_normalized_state
    (K : Set V) (J : V ≃ₗ[ℝ] V) (u : V →ₗ[ℝ] ℝ)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hinv : MapsTo J.symm K K) (hunit : u.comp J.toLinearMap = u) :
    MapsTo (recoveryMap J) {z | z ∈ K.prod K ∧ jointUnit u z = 1}
      {x | x ∈ K ∧ u x = 1} := by
  intro z hz
  refine ⟨recovery_positive K J hadd hinv hz.1, ?_⟩
  have h := DFunLike.congr_fun (recovery_unit_preserving J u hunit) z
  exact h.trans hz.2

theorem discard_normalized_state
    (K : Set V) (u : V →ₗ[ℝ] ℝ)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) :
    MapsTo (discardMap : V × V →ₗ[ℝ] V)
      {z | z ∈ K.prod K ∧ jointUnit u z = 1} {x | x ∈ K ∧ u x = 1} := by
  intro z hz
  refine ⟨discard_positive K hadd hz.1, ?_⟩
  have h := DFunLike.congr_fun (discard_unit_preserving u) z
  exact h.trans hz.2

end Record

namespace ClassicalBit

abbrev Bit := ℝ × ℝ

def cone : Set Bit := {x | 0 ≤ x.1 ∧ 0 ≤ x.2}

def swap : Bit ≃ₗ[ℝ] Bit := LinearEquiv.prodComm ℝ ℝ ℝ

def unit : Bit →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ

def readout : Bit →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ

def e0 : Bit := (1, 0)
def e1 : Bit := (0, 1)

def a (η : ℝ) : ℝ := (1 + η) / 2
def b (η : ℝ) : ℝ := (1 - η) / 2

def forgotten (η : ℝ) : Bit →ₗ[ℝ] Bit :=
  discardMap.comp (recordMap swap (a η) (b η))

theorem weights (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    0 < a η ∧ 0 < b η ∧ a η + b η = 1 := by
  dsimp [a, b]
  constructor
  · linarith
  constructor
  · linarith
  · ring

theorem cone_add (x : Bit) (hx : x ∈ cone) (y : Bit) (hy : y ∈ cone) :
    x + y ∈ cone := ⟨add_nonneg hx.1 hy.1, add_nonneg hx.2 hy.2⟩

theorem cone_scale (r : ℝ) (hr : 0 ≤ r) (x : Bit) (hx : x ∈ cone) :
    r • x ∈ cone := ⟨mul_nonneg hr hx.1, mul_nonneg hr hx.2⟩

theorem swap_positive : MapsTo swap cone cone := by
  intro x hx
  exact ⟨hx.2, hx.1⟩

theorem swap_inverse_positive : MapsTo swap.symm cone cone := by
  intro x hx
  exact ⟨hx.2, hx.1⟩

theorem swap_unit : unit.comp swap.toLinearMap = unit := by
  apply LinearMap.ext
  intro x
  change x.2 + x.1 = x.1 + x.2
  ring

theorem forgotten_zero (η : ℝ) : forgotten η e0 = a η • e0 + b η • e1 := rfl

theorem forgotten_one (η : ℝ) : forgotten η e1 = b η • e0 + a η • e1 := by
  change a η • e1 + b η • e0 = b η • e0 + a η • e1
  rw [add_comm]

theorem forgotten_normalized_state (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    MapsTo (forgotten η) {x | x ∈ cone ∧ unit x = 1} {x | x ∈ cone ∧ unit x = 1} := by
  obtain ⟨ha, hb, hsum⟩ := weights η hη hη1
  intro x hx
  exact discard_normalized_state cone unit cone_add
    (record_normalized_state cone swap unit _ _ ha.le hb.le hsum cone_scale
      swap_positive swap_unit hx)

/-- Forgetting the label prevents positive linear recovery even on both pointers. -/
theorem forgotten_no_positive_pointer_recovery (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ¬ ∃ R : Bit →ₗ[ℝ] Bit, PositiveMixtureRecoveryObstruction.PositiveOn cone R ∧
      R (forgotten η e0) = e0 ∧ R (forgotten η e1) = e1 := by
  obtain ⟨ha, hb, _⟩ := weights η hη hη1
  exact PositiveMixtureRecoveryObstruction.no_positive_two_state_recovery
    cone e0 e1 (by norm_num [cone, e0]) (by norm_num [cone, e1])
    readout (fun x hx => hx.2) rfl rfl (a η) (b η) ha hb
    (forgotten η) (forgotten_zero η) (forgotten_one η)

/-- Strictly positive branch weights retain an exact positive normalized recovery
when the extra classical label is available. -/
theorem recorded_bit_recovery (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    (recoveryMap swap).comp (recordMap swap (a η) (b η)) = LinearMap.id ∧
      MapsTo (recordMap swap (a η) (b η)) {x | x ∈ cone ∧ unit x = 1}
        {z | z ∈ cone.prod cone ∧ jointUnit unit z = 1} ∧
      MapsTo (recoveryMap swap) {z | z ∈ cone.prod cone ∧ jointUnit unit z = 1}
        {x | x ∈ cone ∧ unit x = 1} := by
  obtain ⟨ha, hb, hsum⟩ := weights η hη hη1
  exact ⟨recovery_record_identity swap _ _ hsum,
    record_normalized_state cone swap unit _ _ ha.le hb.le hsum cone_scale swap_positive swap_unit,
    recovery_normalized_state cone swap unit cone_add swap_inverse_positive swap_unit⟩

end ClassicalBit

end

end IDT.QMClosure.RecordedMixtureRecovery
