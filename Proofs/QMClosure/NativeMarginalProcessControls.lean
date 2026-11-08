import Proofs.QMClosure.NativeMarginalProcessBridge
import Proofs.QMClosure.DetectorConservationOmissionControls

/-!
# Omission controls for a native first-marginal process

A nonconstant positive-variance Gaussian family with hidden labels satisfies
the square-swap and full-law contracts while its raw diagonal labels move.
A second Gaussian family has both native marginals and fixed raw diagonals,
but fails square-swap and full output independence at positive variances 1 and 3.
These are supplied real probability-process controls.
-/

namespace IDT.QMClosure.NativeMarginalProcessControls

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open NativeGaussianStatisticalProcess
open scoped ENNReal NNReal

private abbrev Iso := NativeIsotropicGaussianFamily.preparation

theorem G_square (p : PairSample) : G (G p) = p.swap := by
  ext <;> simp [G_apply] <;> ring

abbrev HiddenCarrier := Sample × Fin 5

/-- A diagonal transposition alongside the original off-diagonal four-cycles. -/
def hiddenOperation (p : Fin 5 × Fin 5) : Fin 5 × Fin 5 :=
  if p = (0, 0) then (1, 1)
  else if p = (1, 1) then (0, 0)
  else DetectorConservationOmissionControls.operation p

theorem hiddenOperation_square : ∀ p, hiddenOperation (hiddenOperation p) = p.swap := by
  decide

theorem hiddenOperation_swap : ∀ p, hiddenOperation p.swap = (hiddenOperation p).swap := by
  decide

def hiddenPreparation (x : HiddenCarrier) : Measure Sample := Iso 1 x.1

instance hiddenPreparation_probability (x : HiddenCarrier) :
    IsProbabilityMeasure (hiddenPreparation x) := by
  unfold hiddenPreparation Iso
  infer_instance

def hiddenMixer (p : HiddenCarrier × HiddenCarrier) : HiddenCarrier × HiddenCarrier :=
  (((G (p.1.1, p.2.1)).1, (hiddenOperation (p.1.2, p.2.2)).1),
    ((G (p.1.1, p.2.1)).2, (hiddenOperation (p.1.2, p.2.2)).2))

theorem hiddenMixer_square (p : HiddenCarrier × HiddenCarrier) :
    hiddenMixer (hiddenMixer p) = p.swap := by
  apply Prod.ext <;> apply Prod.ext
  · exact congrArg (fun q : PairSample => q.1) (G_square (p.1.1, p.2.1))
  · exact congrArg (fun q : Fin 5 × Fin 5 => q.1) (hiddenOperation_square (p.1.2, p.2.2))
  · exact congrArg (fun q : PairSample => q.2) (G_square (p.1.1, p.2.1))
  · exact congrArg (fun q : Fin 5 × Fin 5 => q.2) (hiddenOperation_square (p.1.2, p.2.2))

theorem hiddenPreparation_firstMarginal (p : HiddenCarrier × HiddenCarrier) :
    ((hiddenPreparation p.1).prod (hiddenPreparation p.2)).map
        NativeMarginalProcessBridge.firstOutput =
      hiddenPreparation (hiddenMixer p).1 := by
  simpa [hiddenPreparation, Iso, hiddenMixer,
    NativeMarginalProcessBridge.firstOutput,
    NativeStationaryNoiseCharacterization.firstOutput,
    NativeIsotropicGaussianFamily.first, show (1 + 1 : ℝ≥0) / 2 = 1 by norm_num] using
    NativeIsotropicGaussianFamily.map_first_preparation_prod 1 1 p.1.1 p.2.1

def hiddenModel : NativeMarginalProcessBridge.Contract HiddenCarrier where
  preparation := hiddenPreparation
  probability := fun _ => inferInstance
  operation := hiddenMixer
  square := hiddenMixer_square
  firstMarginal := hiddenPreparation_firstMarginal

theorem hiddenPreparation_fullCovariance (p : HiddenCarrier × HiddenCarrier) :
    ((hiddenPreparation p.1).prod (hiddenPreparation p.2)).map G =
      (hiddenPreparation (hiddenMixer p).1).prod (hiddenPreparation (hiddenMixer p).2) :=
  NativeIsotropicGaussianFamily.map_preparation_prod 1 p.1.1 p.2.1

theorem hiddenPreparation_finiteKL (x y : HiddenCarrier) :
    klDiv (hiddenPreparation x) (hiddenPreparation y) ≠ ∞ :=
  NativeIsotropicGaussianFamily.klDiv_preparation_ne_top 1 (by norm_num) x.1 y.1

theorem hiddenPreparation_not_dirac (x : HiddenCarrier) (m : Sample) :
    hiddenPreparation x ≠ Measure.dirac m := by
  intro h
  have hh : Iso 1 x.1 = Iso 0 m := by simpa [hiddenPreparation, Iso] using h
  have hv := (NativeIsotropicGaussianFamily.preparation_ext_iff 1 0 x.1 m).mp hh
  norm_num at hv

theorem hiddenPreparation_nonconstant :
    hiddenPreparation ((0, 0), 0) ≠ hiddenPreparation ((1, 0), 0) := by
  intro h
  have hm := (NativeIsotropicGaussianFamily.preparation_ext_iff 1 1
    (0, 0) (1, 0)).mp h
  norm_num at hm

/-- The moving hidden diagonal survives a nontrivial finite-KL observed family. -/
theorem hiddenMixer_diagonal_moves :
    hiddenMixer (((0, 0), 0), ((0, 0), 0)) ≠ (((0, 0), 0), ((0, 0), 0)) := by
  intro h
  have hh := congrArg (fun p : HiddenCarrier × HiddenCarrier => p.1.2) h
  norm_num [hiddenMixer, hiddenOperation] at hh

abbrev VariableCarrier := Sample × ℝ≥0

def variablePreparation (x : VariableCarrier) : Measure Sample := Iso x.2 x.1

instance variablePreparation_probability (x : VariableCarrier) :
    IsProbabilityMeasure (variablePreparation x) := by
  unfold variablePreparation Iso
  infer_instance

/-- Only the variance labels are averaged. The means use the exact native map. -/
def variableMixer (p : VariableCarrier × VariableCarrier) :
    VariableCarrier × VariableCarrier :=
  (((G (p.1.1, p.2.1)).1, (p.1.2 + p.2.2) / 2),
    ((G (p.1.1, p.2.1)).2, (p.1.2 + p.2.2) / 2))

theorem variablePreparation_firstMarginal (p : VariableCarrier × VariableCarrier) :
    ((variablePreparation p.1).prod (variablePreparation p.2)).map
        NativeMarginalProcessBridge.firstOutput =
      variablePreparation (variableMixer p).1 :=
  NativeIsotropicGaussianFamily.map_first_preparation_prod p.1.2 p.2.2 p.1.1 p.2.1

theorem variablePreparation_secondMarginal (p : VariableCarrier × VariableCarrier) :
    ((variablePreparation p.1).prod (variablePreparation p.2)).map
        NativeMarginalProcessBridge.secondOutput =
      variablePreparation (variableMixer p).2 :=
  NativeIsotropicGaussianFamily.map_second_preparation_prod p.1.2 p.2.2 p.1.1 p.2.1

theorem variableMixer_diagonal (x : VariableCarrier) : variableMixer (x, x) = (x, x) := by
  simp only [variableMixer, NativeIsotropicGaussianFamily.G_diagonal]
  ext <;> simp

def unequalInputs : VariableCarrier × VariableCarrier := (((0, 0), 1), ((0, 0), 3))

theorem unequalInputs_positive_variances :
    0 < unequalInputs.1.2 ∧ 0 < unequalInputs.2.2 := by
  norm_num [unequalInputs]

theorem variableMixer_square_fails :
    variableMixer (variableMixer unequalInputs) ≠ unequalInputs.swap := by
  intro h
  have hh := congrArg (fun p : VariableCarrier × VariableCarrier => p.1.2) h
  norm_num [variableMixer, unequalInputs] at hh

theorem variablePreparation_variance_differs :
    Var[Prod.fst; variablePreparation unequalInputs.1] ≠
      Var[Prod.fst; variablePreparation unequalInputs.2] := by
  simp [variablePreparation, Iso, unequalInputs,
    NativeIsotropicGaussianFamily.variance_fst_preparation]

/-- This mixed-coordinate witness detects the surviving output dependence. -/
def dependenceWitness : StrongDual ℝ PairSample :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Sample Sample) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Sample Sample)

theorem actual_joint_characteristic :
    charFunDual (((variablePreparation unequalInputs.1).prod
      (variablePreparation unequalInputs.2)).map G) dependenceWitness =
        Complex.exp (-3) := by
  rw [charFunDual_map]
  change charFunDual ((Iso 1 (0, 0)).prod (Iso 3 (0, 0)))
    (dependenceWitness.comp G) = _
  rw [NativeIsotropicGaussianFamily.charFunDual_preparation_prod]
  norm_num [dependenceWitness, G_apply, e0, e1, e2, e3]

theorem independent_target_characteristic :
    charFunDual ((variablePreparation (variableMixer unequalInputs).1).prod
      (variablePreparation (variableMixer unequalInputs).2)) dependenceWitness =
        Complex.exp (-2) := by
  change charFunDual ((Iso ((1 + 3) / 2) (G ((0, 0), (0, 0))).1).prod
    (Iso ((1 + 3) / 2) (G ((0, 0), (0, 0))).2)) dependenceWitness = _
  rw [NativeIsotropicGaussianFamily.charFunDual_preparation_prod]
  norm_num [dependenceWitness, G_apply, e0, e1, e2, e3]

theorem variablePreparation_fullCovariance_fails :
    ((variablePreparation unequalInputs.1).prod
      (variablePreparation unequalInputs.2)).map G ≠
      (variablePreparation (variableMixer unequalInputs).1).prod
        (variablePreparation (variableMixer unequalInputs).2) := by
  intro h
  have hh := congrArg (fun μ : Measure PairSample => charFunDual μ dependenceWitness) h
  dsimp only at hh
  rw [actual_joint_characteristic, independent_target_characteristic] at hh
  have hreal := congrArg Complex.re hh
  rw [show (-3 : ℂ) = ((-3 : ℝ) : ℂ) by norm_num,
    show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num,
    Complex.exp_ofReal_re, Complex.exp_ofReal_re] at hreal
  have hbad : (-3 : ℝ) = -2 := Real.exp_injective hreal
  norm_num at hbad

end
end IDT.QMClosure.NativeMarginalProcessControls
