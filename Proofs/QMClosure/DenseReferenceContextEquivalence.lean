import Proofs.QMClosure.ResponseContextQuotient
import Proofs.QMClosure.NativeRecipeContextRealization
import Mathlib.Topology.DenseEmbedding

/-!
# Dense references suffice for continuous-signature contextual equivalence

The ambient carrier has an arbitrary supplied topology. The signature is a
supplied continuous map to a Hausdorff space, and each selected gate output is
continuous separately in each input. A dense reference map has an arbitrary
index type, with no topology on that index type and no gate-closure assumption
on its image. Restricted contexts retain the existing finite one-hole grammar.

Under these explicit premises, equivalence in all restricted contexts equals
equivalence in all ambient-reference contexts, for arbitrary ambient inputs.
Consequently every ambient separating context has some finite restricted
separating context. This does not preserve a context's exact numerical output,
replace each reference exactly, or supply search, size, precision, noise, or
resource bounds. Separate continuity is not a simultaneous-reference convergence
claim.

The continuity premise excludes nonconstant point or zero tests into discrete
Bool on ordinary connected complex space: every continuous such signature is
constant. No physical topology, reference availability, generated closure,
mixture law, positivity, probability law, actualization, or QM closure follows.
-/

namespace IDT.QMClosure.DenseReferenceContextEquivalence

noncomputable section

open OperationalContextQuotient
open NativeRecipeContextRealization (mapRefs)

variable {A V Ω : Type*}

/-- Continuity of each selected output in each input separately. Joint
continuity of the raw gate is not required. -/
structure GateSeparateContinuous [TopologicalSpace V]
    (T : (V × V) → V × V) : Prop where
  left : ∀ o r, Continuous (fun x => select o (T (x, r)))
  right : ∀ o r, Continuous (fun x => select o (T (r, x)))

/-- All finite one-hole contexts whose references come from the supplied map.
The compared inputs themselves may be anywhere in the ambient carrier. -/
def RestrictedEq (T : (V × V) → V × V) (σ : V → Ω) (ref : A → V)
    (x y : V) : Prop :=
  ∀ C : Context A,
    σ (Context.eval T (mapRefs ref C) x) = σ (Context.eval T (mapRefs ref C) y)

/-- Reference replacement respects substitution into the unique hole. -/
theorem mapRefs_plug (ref : A → V) (C D : Context A) :
    mapRefs ref (Context.plug C D) =
      Context.plug (mapRefs ref C) (mapRefs ref D) := by
  induction C with
  | hole => rfl
  | left o C a ih => simp only [Context.plug, mapRefs, ih]
  | right o a C ih => simp only [Context.plug, mapRefs, ih]

theorem signature_eq {T : (V × V) → V × V} {σ : V → Ω} {ref : A → V}
    {x y : V} (h : RestrictedEq T σ ref x y) : σ x = σ y :=
  h .hole

/-- Composition supplies stability at references in the image without any
topological hypotheses. -/
theorem left_ref_stable {T : (V × V) → V × V} {σ : V → Ω} {ref : A → V}
    {x y : V} (h : RestrictedEq T σ ref x y) (o : Output) (a : A) :
    RestrictedEq T σ ref (select o (T (x, ref a))) (select o (T (y, ref a))) := by
  intro C
  simpa only [mapRefs_plug, mapRefs, Context.eval_plug, Context.eval] using
    h (Context.plug C (.left o .hole a))

theorem right_ref_stable {T : (V × V) → V × V} {σ : V → Ω} {ref : A → V}
    {x y : V} (h : RestrictedEq T σ ref x y) (o : Output) (a : A) :
    RestrictedEq T σ ref (select o (T (ref a, x))) (select o (T (ref a, y))) := by
  intro C
  simpa only [mapRefs_plug, mapRefs, Context.eval_plug, Context.eval] using
    h (Context.plug C (.right o a .hole))

section Topological

variable [TopologicalSpace V] [TopologicalSpace Ω] [T2Space Ω]
variable {T : (V × V) → V × V} {σ : V → Ω} {ref : A → V}

/-- Every fixed finite mapped context is continuous in its unique hole. -/
theorem continuous_eval_mapRefs (hT : GateSeparateContinuous T)
    (ref : A → V) (C : Context A) :
    Continuous (fun x => Context.eval T (mapRefs ref C) x) := by
  induction C with
  | hole => exact continuous_id
  | left o C a ih =>
    simpa only [mapRefs, Context.eval] using (hT.left o (ref a)).comp ih
  | right o a C ih =>
    simpa only [mapRefs, Context.eval] using (hT.right o (ref a)).comp ih

/-- Extend left-input stability from dense-image references to each fixed
ambient reference, using uniqueness of continuous maps into a Hausdorff space. -/
theorem left_stable (dense : DenseRange ref) (hT : GateSeparateContinuous T)
    (hσ : Continuous σ) {x y : V} (h : RestrictedEq T σ ref x y)
    (o : Output) (r : V) :
    RestrictedEq T σ ref (select o (T (x, r))) (select o (T (y, r))) := by
  intro C
  have hx := hσ.comp ((continuous_eval_mapRefs hT ref C).comp (hT.right o x))
  have hy := hσ.comp ((continuous_eval_mapRefs hT ref C).comp (hT.right o y))
  have heq := dense.equalizer hx hy (by
    funext a
    exact left_ref_stable h o a C)
  exact congrFun heq r

/-- The analogous dense extension for right-input stability. -/
theorem right_stable (dense : DenseRange ref) (hT : GateSeparateContinuous T)
    (hσ : Continuous σ) {x y : V} (h : RestrictedEq T σ ref x y)
    (o : Output) (r : V) :
    RestrictedEq T σ ref (select o (T (r, x))) (select o (T (r, y))) := by
  intro C
  have hx := hσ.comp ((continuous_eval_mapRefs hT ref C).comp (hT.left o x))
  have hy := hσ.comp ((continuous_eval_mapRefs hT ref C).comp (hT.left o y))
  have heq := dense.equalizer hx hy (by
    funext a
    exact right_ref_stable h o a C)
  exact congrFun heq r

/-- Dense-reference contexts recover the full ambient response relation for
all ambient inputs, not only inputs in the reference image. -/
theorem restrictedEq_iff_responseEq (dense : DenseRange ref)
    (hT : GateSeparateContinuous T) (hσ : Continuous σ) (x y : V) :
    RestrictedEq T σ ref x y ↔ ResponseContextQuotient.ResponseEq T σ x y := by
  constructor
  · intro h
    exact ResponseContextQuotient.relation_le_responseEq T σ (RestrictedEq T σ ref)
      (fun _ _ hab => signature_eq hab)
      (fun o _ _ r hab => left_stable dense hT hσ hab o r)
      (fun o _ _ r hab => right_stable dense hT hσ hab o r) h
  · intro h C
    exact h (mapRefs ref C)

/-- A finite ambient separator entails some finite dense-reference separator.
This existence result supplies no method or bound for finding the witness. -/
theorem exists_restricted_separator (dense : DenseRange ref)
    (hT : GateSeparateContinuous T) (hσ : Continuous σ) (x y : V)
    (hsep : ∃ C : Context V, σ (Context.eval T C x) ≠ σ (Context.eval T C y)) :
    ∃ C : Context A,
      σ (Context.eval T (mapRefs ref C) x) ≠ σ (Context.eval T (mapRefs ref C) y) := by
  classical
  by_contra hnone
  have heq : RestrictedEq T σ ref x y := by
    intro C
    by_contra hC
    exact hnone ⟨C, hC⟩
  obtain ⟨C, hC⟩ := hsep
  exact hC (((restrictedEq_iff_responseEq dense hT hσ x y).mp heq) C)

end Topological

end

end IDT.QMClosure.DenseReferenceContextEquivalence
