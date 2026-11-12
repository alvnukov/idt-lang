import Proofs.QMClosure.IdentityChannelExtremality
import Mathlib.Tactic

/-! Conditional sharp-phase echo kernel. The main endpoint derives residual
positivity and normalization from explicit cone/effect and visible/hidden sector
premises. Deriving those structural premises from an operational natural-extension
principle remains outside this file. This module supplies no derivation of a
quantum representation or physical origin. -/

namespace IDT.QMClosure

section Algebra

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- Two pointer sectors and their transverse complement. -/
structure EchoPointerSplit (R : Type*) [Ring R] [Algebra ℝ R] where
  left : R
  right : R
  transverse : R
  total : left + right + transverse = 1
  left_sq : left * left = left
  right_sq : right * right = right
  transverse_sq : transverse * transverse = transverse
  left_right : left * right = 0
  right_left : right * left = 0
  left_transverse : left * transverse = 0
  transverse_left : transverse * left = 0
  right_transverse : right * transverse = 0
  transverse_right : transverse * right = 0

def EchoPointerSplit.canonical (d : EchoPointerSplit R) (p q s : ℝ) : R :=
  p • d.left + q • d.right + s • d.transverse

/-- Complementary canonical branches have a scalar two-sided product. -/
theorem EchoPointerSplit.canonical_mul (d : EchoPointerSplit R)
    (p q s : ℝ) (hpq : p * q = s * s) :
    d.canonical p q s * d.canonical q p s = (s * s) • (1 : R) := by
  unfold EchoPointerSplit.canonical
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    d.left_sq, d.right_sq, d.transverse_sq, d.left_right, d.right_left,
    d.left_transverse, d.transverse_left, d.right_transverse,
    d.transverse_right, smul_zero, add_zero, zero_add, smul_smul]
  rw [mul_comm q p, hpq, ← smul_add, ← smul_add, d.total]

/-- The local pointer and transverse equations force the sum of inverse-normalized
branches. The equations are stated on the output sectors, so sector preservation
must be established by the operational caller. -/
theorem EchoPointerSplit.normalized_sum (d : EchoPointerSplit R)
    (A B : R) (p q s : ℝ) (hs : s ≠ 0) (hpq : p * q = s * s)
    (hPA : d.left * A = p • d.left)
    (hPB : d.left * B = q • d.left)
    (hQA : d.right * A = q • d.right)
    (hQB : d.right * B = p • d.right)
    (hH : d.transverse * A + d.transverse * B = (2 * s) • d.transverse) :
    (s * s)⁻¹ • (d.canonical q p s * A) +
      (s * s)⁻¹ • (d.canonical p q s * B) = (2 : ℝ) • (1 : R) := by
  have hraw : d.canonical q p s * A + d.canonical p q s * B =
      (2 * (s * s)) • (1 : R) := by
    unfold EchoPointerSplit.canonical
    simp only [add_mul, smul_mul_assoc, hPA, hPB, hQA, hQB, smul_smul]
    calc
      _ = (2 * (p * q)) • d.left + (2 * (p * q)) • d.right +
          s • (d.transverse * A + d.transverse * B) := by module
      _ = (2 * (s * s)) • (d.left + d.right + d.transverse) := by
        rw [hH, hpq]
        module
      _ = _ := by rw [d.total]
  rw [← smul_add, hraw, smul_smul]
  congr 1
  field_simp [hs]

/-- Component equations identify a branch on the full direct sum. -/
theorem EchoPointerSplit.eq_canonical (d : EchoPointerSplit R)
    (X : R) (p q s : ℝ)
    (hP : X * d.left = p • d.left)
    (hQ : X * d.right = q • d.right)
    (hH : X * d.transverse = s • d.transverse) :
    X = d.canonical p q s := by
  calc
    X = X * (d.left + d.right + d.transverse) := by rw [d.total, mul_one]
    _ = _ := by simp only [mul_add, hP, hQ, hH, EchoPointerSplit.canonical]

/-- A pointer-swapping involution conjugates the opposite branch onto one pointer. -/
theorem phase_conjugate_pointer (J B P Q : R) (p : ℝ)
    (hJJ : J * J = 1) (hJP : J * P = Q * J) (hJQ : J * Q = P * J)
    (hBQ : B * Q = p • Q) :
    (J * B * J) * P = p • P := by
  calc
    (J * B * J) * P = J * (B * (J * P)) := by noncomm_ring
    _ = J * ((B * Q) * J) := by rw [hJP]; noncomm_ring
    _ = p • (J * Q * J) := by
      rw [hBQ]
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = p • P := by rw [hJQ, mul_assoc, hJJ, mul_one]

omit [Algebra ℝ R] in
/-- The negative transverse phase cancels under conjugation of a sector-preserving branch. -/
theorem phase_conjugate_transverse (J B H : R)
    (hJH : J * H = -H) (hBH : B * H = H * B) :
    (J * B * J) * H = B * H := by
  calc
    (J * B * J) * H = J * (B * (J * H)) := by noncomm_ring
    _ = -(J * (B * H)) := by rw [hJH]; simp
    _ = -(J * H) * B := by rw [hBH]; noncomm_ring
    _ = B * H := by rw [hJH]; simpa using hBH.symm

/-- Algebraic negative-complement control. This hypothesis makes the whole
complement negative. A physical phase with visible transverse directions requires
the distinct visible/hidden theorem below. -/
theorem EchoPointerSplit.negative_complement_phase_average (d : EchoPointerSplit R)
    (A B J : R) (p q s : ℝ)
    (hJJ : J * J = 1)
    (hJP : J * d.left = d.right * J)
    (hJQ : J * d.right = d.left * J)
    (hJH : J * d.transverse = -d.transverse)
    (hAP : A * d.left = p • d.left)
    (hAQ : A * d.right = q • d.right)
    (hBP : B * d.left = q • d.left)
    (hBQ : B * d.right = p • d.right)
    (hBH : B * d.transverse = d.transverse * B)
    (hH : A * d.transverse + B * d.transverse = (2 * s) • d.transverse) :
    (1 / 2 : ℝ) • (A + J * B * J) = d.canonical p q s := by
  apply d.eq_canonical
  · rw [smul_mul_assoc, add_mul, hAP,
      phase_conjugate_pointer J B d.left d.right p hJJ hJP hJQ hBQ]
    module
  · rw [smul_mul_assoc, add_mul, hAQ,
      phase_conjugate_pointer J B d.right d.left q hJJ hJQ hJP hBP]
    module
  · rw [smul_mul_assoc, add_mul,
      phase_conjugate_transverse J B d.transverse hJH hBH, hH]
    module

/-- A phase preserves a visible sector on which the branch is already canonical. -/
theorem phase_conjugate_visible (J B T : R) (s : ℝ)
    (hJJ : J * J = 1) (hJT : J * T = T * J)
    (hBT : B * T = s • T) :
    (J * B * J) * T = s • T := by
  calc
    (J * B * J) * T = J * ((B * T) * J) := by rw [mul_assoc, mul_assoc, hJT]; noncomm_ring
    _ = s • (J * T * J) := by
      rw [hBT]
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = s • T := by rw [hJT, mul_assoc, hJJ, mul_one]

/-- Visible transverse directions and product-invisible directions are separate.
The phase commutes with the visible sector and is negative only on the hidden
sector. Local canonicality supplies the visible action of both branches. -/
theorem EchoPointerSplit.phase_average_visible_hidden (d : EchoPointerSplit R)
    (A B J T H : R) (p q s : ℝ)
    (hTH : T + H = d.transverse)
    (hJJ : J * J = 1)
    (hJP : J * d.left = d.right * J)
    (hJQ : J * d.right = d.left * J)
    (hJT : J * T = T * J) (hJH : J * H = -H)
    (hAP : A * d.left = p • d.left)
    (hAQ : A * d.right = q • d.right)
    (hBP : B * d.left = q • d.left)
    (hBQ : B * d.right = p • d.right)
    (hAT : A * T = s • T) (hBT : B * T = s • T)
    (hBH : B * H = H * B)
    (hH : A * H + B * H = (2 * s) • H) :
    (1 / 2 : ℝ) • (A + J * B * J) = d.canonical p q s := by
  apply d.eq_canonical
  · rw [smul_mul_assoc, add_mul, hAP,
      phase_conjugate_pointer J B d.left d.right p hJJ hJP hJQ hBQ]
    module
  · rw [smul_mul_assoc, add_mul, hAQ,
      phase_conjugate_pointer J B d.right d.left q hJJ hJQ hJP hBP]
    module
  · have hT : ((1 / 2 : ℝ) • (A + J * B * J)) * T = s • T := by
      rw [smul_mul_assoc, add_mul, hAT, phase_conjugate_visible J B T s hJJ hJT hBT]
      module
    have hHidden : ((1 / 2 : ℝ) • (A + J * B * J)) * H = s • H := by
      rw [smul_mul_assoc, add_mul, phase_conjugate_transverse J B H hJH hBH, hH]
      module
    rw [← hTH, mul_add, hT, hHidden, smul_add]

end Algebra

section Rigidity

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- Cone preservation and an exact unit-effect identity imply preservation of the
normalized base. Any cone axioms needed to prove positivity belong to the caller. -/
theorem mapsTo_normalized_base_of_positive_unit
    (K : Set V) (u : V →ₗ[ℝ] ℝ) (F : V →ₗ[ℝ] V)
    (hpositive : MapsTo F K K) (hunit : u.comp F = u) :
    MapsTo F {x | x ∈ K ∧ u x = 1} {x | x ∈ K ∧ u x = 1} := by
  intro x hx
  refine ⟨hpositive hx.1, ?_⟩
  change u (F x) = 1
  have hu : u (F x) = u x := DFunLike.congr_fun hunit x
  exact hu.trans hx.2

/-- Positive normalized residual noise disappears when its average is identity.
The base-preservation hypotheses expose the precise operational bridge. -/
theorem normalized_noise_rigidity
    {Ω : Set V} (hc : IsCompact Ω) (hv : Convex ℝ Ω)
    (hspan : Submodule.span ℝ Ω = ⊤)
    (C D A B N M : Module.End ℝ V)
    (hAN : A = C * N) (hBM : B = D * M)
    (hN : MapsTo N Ω Ω) (hM : MapsTo M Ω Ω)
    (hsum : N + M = (2 : ℝ) • (1 : Module.End ℝ V)) :
    A = C ∧ B = D := by
  have havg : (1 / 2 : ℝ) • (N + M) = LinearMap.id := by
    rw [hsum, smul_smul]
    norm_num
    rfl
  obtain ⟨hNi, hMi⟩ := identity_channel_extreme hc hv hspan N M hN hM havg
  constructor
  · simpa [hNi] using hAN
  · simpa [hMi] using hBM

/-- Echo transfer from explicit pointer equations and normalized-noise positivity.
The residual maps are computed from the canonical inverses, rather than supplied
as arbitrary factorizations. Their preservation of Ω is the operational
positivity/normalization premise still required from a GPT-level construction. -/
theorem sharp_phase_echo_transfer
    {Ω : Set V} (hc : IsCompact Ω) (hv : Convex ℝ Ω)
    (hspan : Submodule.span ℝ Ω = ⊤)
    (d : EchoPointerSplit (Module.End ℝ V))
    (A B : Module.End ℝ V) (p q s : ℝ) (hs : s ≠ 0)
    (hpq : p * q = s * s)
    (hPA : d.left * A = p • d.left)
    (hPB : d.left * B = q • d.left)
    (hQA : d.right * A = q • d.right)
    (hQB : d.right * B = p • d.right)
    (hH : d.transverse * A + d.transverse * B = (2 * s) • d.transverse)
    (hN : MapsTo ((s * s)⁻¹ • (d.canonical q p s * A)) Ω Ω)
    (hM : MapsTo ((s * s)⁻¹ • (d.canonical p q s * B)) Ω Ω) :
    A = d.canonical p q s ∧ B = d.canonical q p s ∧
      A * B = (s * s) • (1 : Module.End ℝ V) ∧
      B * A = (s * s) • (1 : Module.End ℝ V) := by
  let C := d.canonical p q s
  let D := d.canonical q p s
  have hCD : C * D = (s * s) • (1 : Module.End ℝ V) :=
    d.canonical_mul p q s hpq
  have hDC : D * C = (s * s) • (1 : Module.End ℝ V) :=
    d.canonical_mul q p s (by simpa [mul_comm] using hpq)
  have hinv : (s * s)⁻¹ * (s * s) = 1 := inv_mul_cancel₀ (mul_ne_zero hs hs)
  have hAN : A = C * ((s * s)⁻¹ • (D * A)) := by
    rw [mul_smul_comm, ← mul_assoc, hCD, smul_mul_assoc, one_mul,
      smul_smul, hinv, one_smul]
  have hBM : B = D * ((s * s)⁻¹ • (C * B)) := by
    rw [mul_smul_comm, ← mul_assoc, hDC, smul_mul_assoc, one_mul,
      smul_smul, hinv, one_smul]
  obtain ⟨ha, hb⟩ := normalized_noise_rigidity hc hv hspan C D A B
    _ _ hAN hBM hN hM (d.normalized_sum A B p q s hs hpq hPA hPB hQA hQB hH)
  exact ⟨ha, hb, by rw [ha, hb]; exact hCD, by rw [ha, hb]; exact hDC⟩

omit [FiniteDimensional ℝ V] in
/-- The unit effect of an inverse-normalized canonical composite follows from
pointer effects alone. The unit effect vanishes on the full transverse complement. -/
theorem normalized_canonical_composite_unit
    (d : EchoPointerSplit (Module.End ℝ V)) (u : V →ₗ[ℝ] ℝ)
    (hunit : u.comp d.left + u.comp d.right = u)
    (X : Module.End ℝ V) (a b s : ℝ) (hs : s ≠ 0)
    (hab : a * b = s * s)
    (hPX : d.left * X = a • d.left)
    (hQX : d.right * X = b • d.right) :
    u.comp ((s * s)⁻¹ • (d.canonical b a s * X)) = u := by
  have hnorm (x : V) : u (d.left x) + u (d.right x) = u x :=
    DFunLike.congr_fun hunit x
  have hzero (x : V) : u (d.transverse x) = 0 := by
    have ht := DFunLike.congr_fun d.total x
    change d.left x + d.right x + d.transverse x = x at ht
    have hu := congrArg u ht
    simp only [map_add] at hu
    linarith [hnorm x]
  ext x
  have hPx := DFunLike.congr_fun hPX x
  have hQx := DFunLike.congr_fun hQX x
  change d.left (X x) = a • d.left x at hPx
  change d.right (X x) = b • d.right x at hQx
  have hscaled : u (d.canonical b a s (X x)) = (s * s) * u x := by
    calc
      _ = (a * b) * (u (d.left x) + u (d.right x)) := by
        simp only [EchoPointerSplit.canonical, LinearMap.add_apply, LinearMap.smul_apply,
          map_add, map_smul, hPx, hQx, hzero, smul_eq_mul, mul_zero, add_zero]
        ring
      _ = _ := by rw [hab, hnorm]
  change u ((s * s)⁻¹ • (d.canonical b a s (X x))) = u x
  rw [map_smul, smul_eq_mul, hscaled, ← mul_assoc,
    inv_mul_cancel₀ (mul_ne_zero hs hs), one_mul]

/-- End-to-end phase echo on a supplied four-sector split and cone/effect bridge.
Visible transverse canonicality and hidden destructive comparison are distinct.
Positivity and normalization of residual maps are derived inside this theorem. -/
theorem sharp_phase_echo_transfer_with_involution
    (K : Set V) (u : V →ₗ[ℝ] ℝ)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hsmul : ∀ (t : ℝ), 0 ≤ t → ∀ x ∈ K, t • x ∈ K)
    (hc : IsCompact {x | x ∈ K ∧ u x = 1})
    (hv : Convex ℝ {x | x ∈ K ∧ u x = 1})
    (hspan : Submodule.span ℝ {x | x ∈ K ∧ u x = 1} = ⊤)
    (d : EchoPointerSplit (Module.End ℝ V))
    (A B J T H : Module.End ℝ V) (p q s : ℝ) (hs : 0 < s)
    (hpq : p * q = s * s)
    (hTH : T + H = d.transverse)
    (hJJ : J * J = 1)
    (hJP : J * d.left = d.right * J)
    (hJQ : J * d.right = d.left * J)
    (hJT : J * T = T * J) (hJH : J * H = -H)
    (hAP : A * d.left = p • d.left)
    (hAQ : A * d.right = q • d.right)
    (hBP : B * d.left = q • d.left)
    (hBQ : B * d.right = p • d.right)
    (hPA : Commute d.left A) (hQA : Commute d.right A)
    (hPB : Commute d.left B) (hQB : Commute d.right B)
    (hAT : A * T = s • T) (hBT : B * T = s • T)
    (hTA : T * A = s • T) (hTB : T * B = s • T)
    (hAH : A * H = H * A) (hBH : B * H = H * B)
    (hH : A * H + B * H = (2 * s) • H)
    (hA : MapsTo A K K) (hB : MapsTo B K K) (hJ : MapsTo J K K)
    (hunit : u.comp d.left + u.comp d.right = u) :
    A = (1 / 2 : ℝ) • (A + J * B * J) ∧
      B = (1 / 2 : ℝ) • (B + J * A * J) ∧
      A * B = (s * s) • (1 : Module.End ℝ V) ∧
      B * A = (s * s) • (1 : Module.End ℝ V) := by
  have hphaseA := d.phase_average_visible_hidden A B J T H p q s hTH hJJ hJP hJQ
    hJT hJH hAP hAQ hBP hBQ hAT hBT hBH hH
  have hphaseB := d.phase_average_visible_hidden B A J T H q p s hTH hJJ hJP hJQ
    hJT hJH hBP hBQ hAP hAQ hBT hAT hAH (by simpa [add_comm] using hH)
  have hC : MapsTo (d.canonical p q s) K K := by
    rw [← hphaseA]
    intro x hx
    change (1 / 2 : ℝ) • (A x + J (B (J x))) ∈ K
    exact hsmul _ (by norm_num) _ (hadd _ (hA hx) _ (hJ (hB (hJ hx))))
  have hD : MapsTo (d.canonical q p s) K K := by
    rw [← hphaseB]
    intro x hx
    change (1 / 2 : ℝ) • (B x + J (A (J x))) ∈ K
    exact hsmul _ (by norm_num) _ (hadd _ (hB hx) _ (hJ (hA (hJ hx))))
  have hNpos : MapsTo ((s * s)⁻¹ • (d.canonical q p s * A)) K K := by
    intro x hx
    exact hsmul _ (inv_nonneg.mpr (mul_nonneg hs.le hs.le)) _ (hD (hA hx))
  have hMpos : MapsTo ((s * s)⁻¹ • (d.canonical p q s * B)) K K := by
    intro x hx
    exact hsmul _ (inv_nonneg.mpr (mul_nonneg hs.le hs.le)) _ (hC (hB hx))
  have hNunit := normalized_canonical_composite_unit d u hunit A p q s (ne_of_gt hs)
    hpq (hPA.eq.trans hAP) (hQA.eq.trans hAQ)
  have hMunit := normalized_canonical_composite_unit d u hunit B q p s (ne_of_gt hs)
    (by simpa [mul_comm] using hpq) (hPB.eq.trans hBP) (hQB.eq.trans hBQ)
  have hN := mapsTo_normalized_base_of_positive_unit K u _ hNpos hNunit
  have hM := mapsTo_normalized_base_of_positive_unit K u _ hMpos hMunit
  have hfull : d.transverse * A + d.transverse * B = (2 * s) • d.transverse := by
    rw [← hTH, add_mul, add_mul, hTA, hTB, ← hAH, ← hBH]
    calc
      _ = (2 * s) • T + (A * H + B * H) := by module
      _ = _ := by rw [hH]; module
  obtain ⟨ha, hb, hab, hba⟩ := sharp_phase_echo_transfer hc hv hspan d A B p q s
    (ne_of_gt hs) hpq
    (hPA.eq.trans hAP) (hPB.eq.trans hBP)
    (hQA.eq.trans hAQ) (hQB.eq.trans hBQ) hfull hN hM
  exact ⟨ha.trans hphaseA.symm, hb.trans hphaseB.symm, hab, hba⟩

end Rigidity

end IDT.QMClosure
