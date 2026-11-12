import Proofs.QMClosure.ComplementaryPowerEnvelope

/-! Separate invariant submodules with complementary operator power envelopes
have zero intersection when the complementary scalar norm exceeds the sum of
the rates. The argument concerns the intersection of supplied submodules.
Physical identification of a common hidden carrier remains a separate question.
-/

namespace IDT.QMClosure.FibreIntersectionObstruction

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Scalar complementarity transfers invariance to the other operator. -/
theorem complementary_preserves_submodule
    (A B : E →L[𝕜] E) (c : 𝕜)
    (hcomp : A + B = c • ContinuousLinearMap.id 𝕜 E)
    (S : Submodule 𝕜 E) (hA : ∀ x ∈ S, A x ∈ S) :
    ∀ x ∈ S, B x ∈ S := by
  intro x hx
  have hsum : A x + B x = c • x := DFunLike.congr_fun hcomp x
  have hB : B x = c • x - A x := by rw [← hsum]; abel
  rw [hB]
  exact S.sub_mem (S.smul_mem c hx) (hA x hx)

/-- Invariance on the two separate submodules gives simultaneous invariance
on their intersection through scalar complementarity. -/
theorem complementary_intersection_invariant
    (A B : E →L[𝕜] E) (c : 𝕜)
    (hcomp : A + B = c • ContinuousLinearMap.id 𝕜 E)
    (U V : Submodule 𝕜 E)
    (hAU : ∀ x ∈ U, A x ∈ U) (hBV : ∀ x ∈ V, B x ∈ V) :
    (∀ x ∈ U ⊓ V, A x ∈ U ⊓ V) ∧
      (∀ x ∈ U ⊓ V, B x ∈ U ⊓ V) := by
  have hBU := complementary_preserves_submodule A B c hcomp U hAU
  have hAV := complementary_preserves_submodule B A c
    (by simpa only [add_comm] using hcomp) V hBV
  exact ⟨fun x hx => ⟨hAU x hx.1, hAV x hx.2⟩,
    fun x hx => ⟨hBU x hx.1, hBV x hx.2⟩⟩

/-- Restriction of a continuous operator to a supplied invariant submodule. -/
noncomputable def restrictedOperator
    (A : E →L[𝕜] E) (S : Submodule 𝕜 E)
    (hA : ∀ x ∈ S, A x ∈ S) : S →L[𝕜] S :=
  (A.comp S.subtypeL).codRestrict S (fun x => hA x x.property)

@[simp]
theorem restrictedOperator_apply
    (A : E →L[𝕜] E) (S : Submodule 𝕜 E)
    (hA : ∀ x ∈ S, A x ∈ S) (x : S) :
    (restrictedOperator A S hA x : E) = A x := rfl

/-- Restricted powers coerce to the ambient powers on the same vector. -/
@[simp]
theorem restrictedOperator_pow_apply
    (A : E →L[𝕜] E) (S : Submodule 𝕜 E)
    (hA : ∀ x ∈ S, A x ∈ S) (n : ℕ) (x : S) :
    ((restrictedOperator A S hA ^ n) x : E) = (A ^ n) (x : E) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', ContinuousLinearMap.mul_apply,
      restrictedOperator_apply, ih]

/-- A common invariant submodule inherits the scalar complement identity. -/
theorem restrictedOperator_complement
    (A B : E →L[𝕜] E) (c : 𝕜)
    (hcomp : A + B = c • ContinuousLinearMap.id 𝕜 E)
    (S : Submodule 𝕜 E)
    (hA : ∀ x ∈ S, A x ∈ S) (hB : ∀ x ∈ S, B x ∈ S) :
    restrictedOperator A S hA + restrictedOperator B S hB =
      c • ContinuousLinearMap.id 𝕜 S := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change A (x : E) + B (x : E) = c • (x : E)
  exact DFunLike.congr_fun hcomp (x : E)

/-- A vector envelope on an invariant submodule bounds the operator norm of
every restricted power. -/
theorem restrictedOperator_power_bound
    (A : E →L[𝕜] E) (S : Submodule 𝕜 E)
    (hA : ∀ x ∈ S, A x ∈ S) (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hbound : ∀ n : ℕ, ∀ x ∈ S, ‖(A ^ n) x‖ ≤ C * q ^ n * ‖x‖) :
    ∀ n : ℕ, ContinuousLinearMap.opNorm (restrictedOperator A S hA ^ n) ≤ C * q ^ n := by
  intro n
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (pow_nonneg hq n))
  intro x
  change ‖((restrictedOperator A S hA ^ n) x : E)‖ ≤ C * q ^ n * ‖(x : E)‖
  rw [restrictedOperator_pow_apply]
  exact hbound n x x.property

/-- If the complementary scalar norm exceeds the sum of the positive power
rates, the two separately controlled invariant submodules have zero intersection. -/
theorem intersection_eq_bot_of_separate_envelopes
    (A B : E →L[𝕜] E) (c : 𝕜)
    (hcomp : A + B = c • ContinuousLinearMap.id 𝕜 E)
    (U V : Submodule 𝕜 E)
    (hAU : ∀ x ∈ U, A x ∈ U) (hBV : ∀ x ∈ V, B x ∈ V)
    (CA CB qA qB : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hqA : 0 < qA) (hqB : 0 < qB)
    (hA : ∀ n : ℕ, ∀ x ∈ U, ‖(A ^ n) x‖ ≤ CA * qA ^ n * ‖x‖)
    (hB : ∀ n : ℕ, ∀ x ∈ V, ‖(B ^ n) x‖ ≤ CB * qB ^ n * ‖x‖)
    (hgap : qA + qB < ‖c‖) : U ⊓ V = ⊥ := by
  by_contra hnonzero
  letI : Nontrivial ↥(U ⊓ V) := Submodule.nontrivial_iff_ne_bot.mpr hnonzero
  obtain ⟨hAH, hBH⟩ := complementary_intersection_invariant A B c hcomp U V hAU hBV
  have hA_bound := restrictedOperator_power_bound A (U ⊓ V) hAH CA qA hCA hqA.le
    (fun n x hx => hA n x hx.1)
  have hB_bound := restrictedOperator_power_bound B (U ⊓ V) hBH CB qB hCB hqB.le
    (fun n x hx => hB n x hx.2)
  have hrate := ComplementaryPowerEnvelope.complementary_operator_rate_bound
    (restrictedOperator A (U ⊓ V) hAH) (restrictedOperator B (U ⊓ V) hBH)
    c CA CB qA qB hqA hqB
    (restrictedOperator_complement A B c hcomp (U ⊓ V) hAH hBH) hA_bound hB_bound
  exact (not_le_of_gt hgap) hrate

end IDT.QMClosure.FibreIntersectionObstruction
