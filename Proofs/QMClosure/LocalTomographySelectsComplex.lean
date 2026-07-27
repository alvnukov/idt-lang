import Mathlib.Tactic

namespace IDT
namespace QMClosure

/-!
# Local tomography selects the complex carrier

Seven steps of this line -- coarse-graining, independent composition,
cancellation, exponent selection, generator arity, and the failure of
distinguishability -- produced no complex amplitudes. Every one of them worked
inside a single context and over ℚ. This file shows that no single-context step
could have produced them, and names what does.

A real symmetric kernel on `n` alternatives carries one parameter per unordered
pair, `n * (n + 1) / 2`. A complex Hermitian kernel carries `n` real diagonal
entries and one complex entry per unordered off-diagonal pair, which is `n^2`
real parameters in total, one per ordered pair. Both counts are grounded below
by counting the pairs rather than asserted.

Local tomography, in Hardy's parameter-counting form, demands that a composite
be determined by its parts: the count multiplies. That single demand separates
the three candidates.

* Complex is multiplicative, and generally so: `(m * n)^2 = m^2 * n^2`.
* Classical is multiplicative too, but has no off-diagonal freedom at all, so
  by `ContextualIndistinguishabilityGivesInterference` it cannot interfere.
* Real has off-diagonal freedom and fails multiplicativity, at the smallest
  case: two two-level systems give `10` parameters where the parts give `9`.

So interference excludes classical, local tomography excludes real, and complex
is what remains. Real quantum theory is not inconsistent; it is excluded by a
constraint on composites and by nothing available inside one context. That is
why nothing earlier in this line could reach complexity: the resource is not
there to be used.

The obligation named by this is `local_tomography`, which the repository
already lists and whose Lean file `V7LocalTomography.lean` contains only
`True := trivial`. So the fourth ingredient is not new to the theory. It is an
already-declared obligation that has never been discharged, and the line above
now says precisely what work it has to do.

Scope. Parameter counts for `n = 2` and `n = 4` are grounded by counting pairs;
the general formulas are used as the standard counts and are not derived here.
Local tomography is taken in its parameter-counting form, which is standard but
is a reading. Only three candidate carriers are compared, so this is a
separation among them and not a proof that complex is the unique possibility.
Nothing here derives the Born rule or phase dynamics, and the closure verdict
is unchanged.
-/

/-- Unordered pairs of alternatives: the parameters of a real symmetric kernel. -/
def unorderedPairCount (alternatives : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin alternatives × Fin alternatives)).filter
    (fun pair => pair.1 ≤ pair.2)).card

/-- Ordered pairs: the real parameters of a complex Hermitian kernel. -/
def orderedPairCount (alternatives : ℕ) : ℕ :=
  Fintype.card (Fin alternatives × Fin alternatives)

theorem unordered_pair_count_two : unorderedPairCount 2 = 3 := by decide

theorem unordered_pair_count_four : unorderedPairCount 4 = 10 := by decide

theorem ordered_pair_count_two : orderedPairCount 2 = 4 := by decide

theorem ordered_pair_count_four : orderedPairCount 4 = 16 := by decide

/-- Candidate carriers for the pairwise kernel. -/
inductive CarrierCandidate where
  | classical
  | real
  | complex
  deriving DecidableEq, Repr

/-- Real parameters determining a state of `alternatives` alternatives. -/
def parameterCount : CarrierCandidate → ℕ → ℕ
  | .classical, alternatives => alternatives
  | .real, alternatives => alternatives * (alternatives + 1) / 2
  | .complex, alternatives => alternatives ^ 2

theorem real_parameter_count_matches_unordered_pairs_two :
    parameterCount .real 2 = unorderedPairCount 2 := by decide

theorem real_parameter_count_matches_unordered_pairs_four :
    parameterCount .real 4 = unorderedPairCount 4 := by decide

theorem complex_parameter_count_matches_ordered_pairs_two :
    parameterCount .complex 2 = orderedPairCount 2 := by decide

theorem complex_parameter_count_matches_ordered_pairs_four :
    parameterCount .complex 4 = orderedPairCount 4 := by decide

/-- Local tomography: a composite is determined by its parts. -/
def LocallyTomographic (candidate : CarrierCandidate) : Prop :=
  ∀ left right : ℕ,
    parameterCount candidate (left * right)
      = parameterCount candidate left * parameterCount candidate right

/-- More parameters than the diagonal, so an off-diagonal entry can be non-zero. -/
def HasOffDiagonalFreedom (candidate : CarrierCandidate) (alternatives : ℕ) : Prop :=
  alternatives < parameterCount candidate alternatives

theorem classical_is_locally_tomographic : LocallyTomographic .classical := by
  intro left right
  rfl

theorem complex_is_locally_tomographic : LocallyTomographic .complex := by
  intro left right
  unfold parameterCount
  ring

/--
Real fails at the smallest composite: two two-level systems need `10`
parameters while their parts supply `9`.
-/
theorem real_is_not_locally_tomographic : ¬ LocallyTomographic .real := by
  intro tomographic
  have witness := tomographic 2 2
  norm_num [parameterCount] at witness

theorem classical_has_no_off_diagonal_freedom (alternatives : ℕ) :
    ¬ HasOffDiagonalFreedom .classical alternatives := by
  simp [HasOffDiagonalFreedom, parameterCount]

theorem real_has_off_diagonal_freedom : HasOffDiagonalFreedom .real 2 := by
  unfold HasOffDiagonalFreedom
  decide

theorem complex_has_off_diagonal_freedom : HasOffDiagonalFreedom .complex 2 := by
  unfold HasOffDiagonalFreedom
  decide

/--
The separation. Among the three candidates, exactly one has both the freedom to
interfere and a composite determined by its parts.
-/
theorem only_complex_interferes_and_is_locally_tomographic :
    (¬ HasOffDiagonalFreedom .classical 2 ∧ LocallyTomographic .classical)
      ∧ (HasOffDiagonalFreedom .real 2 ∧ ¬ LocallyTomographic .real)
      ∧ (HasOffDiagonalFreedom .complex 2 ∧ LocallyTomographic .complex) :=
  ⟨⟨classical_has_no_off_diagonal_freedom 2, classical_is_locally_tomographic⟩,
    ⟨real_has_off_diagonal_freedom, real_is_not_locally_tomographic⟩,
    ⟨complex_has_off_diagonal_freedom, complex_is_locally_tomographic⟩⟩

inductive ComplexSelectionFinding where
  | interferenceExcludesTheClassicalCarrier
  | localTomographyExcludesTheRealCarrier
  | complexSatisfiesBothAndIsMultiplicativeInGeneral
  | theSelectingConstraintIsAboutCompositesNotOneContext
  | localTomographyIsAnAlreadyDeclaredEmptyObligation
  deriving DecidableEq, Repr

def complexSelectionFindings : List ComplexSelectionFinding :=
  [ .interferenceExcludesTheClassicalCarrier,
    .localTomographyExcludesTheRealCarrier,
    .complexSatisfiesBothAndIsMultiplicativeInGeneral,
    .theSelectingConstraintIsAboutCompositesNotOneContext,
    .localTomographyIsAnAlreadyDeclaredEmptyObligation ]

theorem complex_selection_records_five_findings :
    complexSelectionFindings.length = 5 := by
  rfl

inductive ComplexSelectionOpenObligation where
  | deriveLocalTomographyFromContextFirstPrimitives
  | proveTheParameterCountFormulasRatherThanUseThem
  | showComplexIsUniqueRatherThanBestOfThree
  | derivePhaseDynamicsAndNotOnlyTheCarrier
  deriving DecidableEq, Repr

def complexSelectionOpenObligations : List ComplexSelectionOpenObligation :=
  [ .deriveLocalTomographyFromContextFirstPrimitives,
    .proveTheParameterCountFormulasRatherThanUseThem,
    .showComplexIsUniqueRatherThanBestOfThree,
    .derivePhaseDynamicsAndNotOnlyTheCarrier ]

theorem complex_selection_keeps_four_open_obligations :
    complexSelectionOpenObligations.length = 4 := by
  rfl

def complexSelectionClaimBoundary : String :=
  "Among classical, real and complex pairwise kernels, interference excludes classical and local tomography in its parameter-counting form excludes real, at the smallest composite where two two-level systems need 10 parameters against 9 from the parts. Complex satisfies both and is multiplicative for all sizes. This shows the selecting constraint is about composites and is unavailable inside one context, which is why no earlier step of this line reached complexity. It is a separation among three candidates, not a uniqueness proof; the parameter formulas are used rather than derived; local tomography is itself an already-declared obligation whose Lean file is empty. Nothing here derives the Born rule or phase dynamics."

end QMClosure
end IDT
