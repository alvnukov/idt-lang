import Proofs.QMClosure.ResponseDoubledNormalizationCompiler

/-!
# Compiling supplied preparations by their response classes

The input is an actual supplied raw array whose response classes are the two
copies of a specified quotient array. No representatives are chosen, and no
unknown-input copying operation or physical availability is constructed.
The entire output array is retained.
-/

namespace IDT.QMClosure.ResponseClassPreparationCompiler

noncomputable section
open ResponseContextQuotient NativeVacuumProbabilityFamily
open RawDoubledNormalizationCompiler

variable {V Ω : Type*}

/-- Equal input class arrays remain equal after any original-operation word. -/
theorem evalRaw_class_congr (d : Data V Ω) {ι : Type} [DecidableEq ι]
    (c : Native ι) (x y : ι → V)
    (h : (fun i => d.classOf (x i)) = fun i => d.classOf (y i)) :
    (fun i => d.classOf (WeightFreeRawProbability.evalRaw d.operation c x i)) =
      fun i => d.classOf (WeightFreeRawProbability.evalRaw d.operation c y i) := by
  rw [← evalRaw_class d c x, ← evalRaw_class d c y, h]

/-- The actual supplied array represents the specified duplicated classes;
its two raw rails need not be literally equal. -/
theorem evalRaw_compileWord_class_of_input (d : Data V Ω)
    {ι : Type} [DecidableEq ι] (c : Native ι) (q : ι → d.Space)
    (y : ι ⊕ ι → V)
    (hy : (fun w => d.classOf (y w)) = duplicate q) :
    (fun w => d.classOf (WeightFreeRawProbability.evalRaw d.operation
      (compileWord c) y w)) =
      duplicate (WeightFreeRawProbability.evalRaw d.quotientData.normalizedOperation c q) := by
  rw [← evalRaw_class d (compileWord c) y, hy]
  exact evalRaw_compileWord_rawData d.quotientData c q

/-- Paired compiled outputs have equal full responses, without raw equality. -/
theorem paired_output_responseEq (d : Data V Ω)
    {ι : Type} [DecidableEq ι] (c : Native ι) (q : ι → d.Space)
    (y : ι ⊕ ι → V)
    (hy : (fun w => d.classOf (y w)) = duplicate q) (i : ι) :
    ResponseEq d.operation d.signature
      (WeightFreeRawProbability.evalRaw d.operation (compileWord c) y (.inl i))
      (WeightFreeRawProbability.evalRaw d.operation (compileWord c) y (.inr i)) := by
  apply (d.classOf_eq_iff_responseEq _ _).mp
  have h := evalRaw_compileWord_class_of_input d c q y hy
  exact (congrFun h (.inl i)).trans (congrFun h (.inr i)).symm

end
end IDT.QMClosure.ResponseClassPreparationCompiler
