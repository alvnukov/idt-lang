import Proofs.QMClosure.ArityBoundsInterferenceOrder

namespace IDT
namespace QMClosure

/-!
# Interference lives exactly where distinguishability fails

`ArityBoundsInterferenceOrder` showed that a pairwise generator terminates at
second order for free, and that its two-path interference equals the kernel
off-diagonal `kernel 0 1 + kernel 1 0`. It left
`explainWhyTheKernelOffDiagonalIsNonZero` open: binary arity buys the *order* of
interference but not its *existence*. A diagonal kernel is binary too, and it
does not interfere.

This file locates the off-diagonal. Proved below:

* a diagonal kernel has no two-path interference and its readout is exactly
  additive -- full pairwise distinguishability gives classical probability;
* interference therefore forces some off-diagonal entry, hence some pair that
  the kernel does not separate;
* if distinguishability holds globally, across an arbitrary family of contexts,
  then no context in the family interferes;
* a two-context model in which one context separates a pair and the other does
  not: interference appears exactly in the second, and nowhere else.

So on the reading that the kernel off-diagonal records failure of stable
distinguishability, the whole line reduces to this: interference exists iff
distinguishability fails somewhere, and it is context-relative iff
distinguishability is. That is the founding commitment of a context-first
theory -- Bell and contextuality as failed global gluing of local sections,
with no global fact table -- and not a further derivation from it.

That is the honest shape of the result. The line assembled across these files
reduces the Born readout to context-relative failure of distinguishability
rather than deriving it from something more basic. Reduction to a premise the
theory already holds is progress, and it is not proof of the premise.

Scope. Three alternatives over ℚ. Since `stableDistinguishabilityRelation` has
no definition in this repository, reading the off-diagonal as its failure is a
proposed reading, exactly as in
`StableDistinguishabilityGivesCancellation`; the theorems themselves are about
kernels and are independent of the reading. Nothing here derives complex
amplitudes or phase, which remain the one ingredient no step of this line has
supplied, and the closure verdict is untouched.
-/

/-- The kernel separates every distinct pair of alternatives. -/
def SeparatesAllPairs (kernel : Fin 3 → Fin 3 → ℚ) : Prop :=
  ∀ left right : Fin 3, left ≠ right → kernel left right = 0

/-- Full pairwise separation kills two-path interference. -/
theorem separating_kernel_does_not_interfere
    (kernel : Fin 3 → Fin 3 → ℚ) (separates : SeparatesAllPairs kernel) :
    kernelTwoPathInterference kernel = 0 := by
  rw [kernel_two_path_interference_is_off_diagonal]
  rw [separates 0 1 (by decide), separates 1 0 (by decide)]
  norm_num

/-- And makes the readout exactly additive: the classical case. -/
theorem separating_kernel_is_additive
    (kernel : Fin 3 → Fin 3 → ℚ) (separates : SeparatesAllPairs kernel) :
    kernelWeight kernel 1 1 0
      = kernelWeight kernel 1 0 0 + kernelWeight kernel 0 1 0 := by
  unfold kernelWeight
  rw [separates 0 1 (by decide), separates 1 0 (by decide)]
  ring

/-- Conversely, interference forces a pair the kernel fails to separate. -/
theorem interference_forces_an_unseparated_pair
    (kernel : Fin 3 → Fin 3 → ℚ)
    (interferes : kernelTwoPathInterference kernel ≠ 0) :
    ¬ SeparatesAllPairs kernel := by
  intro separates
  exact interferes (separating_kernel_does_not_interfere kernel separates)

/--
If distinguishability holds globally -- in every context of an arbitrary family
-- then no context interferes. This is the no-global-fact-table clause read on
the readout side.
-/
theorem globally_separating_family_never_interferes
    {Context : Type} (kernelOf : Context → (Fin 3 → Fin 3 → ℚ))
    (globallySeparating : ∀ context : Context, SeparatesAllPairs (kernelOf context))
    (context : Context) :
    kernelTwoPathInterference (kernelOf context) = 0 :=
  separating_kernel_does_not_interfere (kernelOf context) (globallySeparating context)

/-- A context that separates alternatives `0` and `1`. -/
def separatingContextKernel : Fin 3 → Fin 3 → ℚ
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 2 => 1
  | _, _ => 0

/-- A context that does not separate them, differing only in that pair. -/
def overlappingContextKernel : Fin 3 → Fin 3 → ℚ
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 2 => 1
  | 0, 1 => 1
  | 1, 0 => 1
  | _, _ => 0

theorem separating_context_separates_all_pairs :
    SeparatesAllPairs separatingContextKernel := by
  intro left right different
  fin_cases left <;> fin_cases right <;>
    simp_all [separatingContextKernel]

theorem overlapping_context_does_not_separate_the_first_pair :
    overlappingContextKernel 0 1 ≠ 0 := by
  norm_num [overlappingContextKernel]

theorem separating_context_does_not_interfere :
    kernelTwoPathInterference separatingContextKernel = 0 :=
  separating_kernel_does_not_interfere _ separating_context_separates_all_pairs

theorem overlapping_context_interferes :
    kernelTwoPathInterference overlappingContextKernel = 2 := by
  rw [kernel_two_path_interference_is_off_diagonal]
  norm_num [overlappingContextKernel]

/--
The two contexts assign different distinguishability to the same pair, and
interference appears exactly where separation fails. Both remain second order,
because both are pairwise generated.
-/
theorem contextual_pair_carries_interference_only_where_separation_fails :
    kernelTwoPathInterference separatingContextKernel = 0
      ∧ kernelTwoPathInterference overlappingContextKernel ≠ 0
      ∧ kernelThreePathInterference separatingContextKernel = 0
      ∧ kernelThreePathInterference overlappingContextKernel = 0 :=
  ⟨separating_context_does_not_interfere,
    by rw [overlapping_context_interferes]; norm_num,
    kernel_three_path_interference_vanishes _,
    kernel_three_path_interference_vanishes _⟩

inductive IndistinguishabilityFinding where
  | fullSeparationGivesClassicalAdditiveReadout
  | interferenceForcesAnUnseparatedPair
  | globalSeparationRemovesInterferenceFromEveryContext
  | contextRelativeSeparationPlacesInterferencePerContext
  | bothContextsStaySecondOrderBecauseBothArePairwise
  deriving DecidableEq, Repr

def indistinguishabilityFindings : List IndistinguishabilityFinding :=
  [ .fullSeparationGivesClassicalAdditiveReadout,
    .interferenceForcesAnUnseparatedPair,
    .globalSeparationRemovesInterferenceFromEveryContext,
    .contextRelativeSeparationPlacesInterferencePerContext,
    .bothContextsStaySecondOrderBecauseBothArePairwise ]

theorem indistinguishability_records_five_findings :
    indistinguishabilityFindings.length = 5 := by
  rfl

inductive IndistinguishabilityOpenObligation where
  | deriveComplexAmplitudesAndPhase
  | giveStableDistinguishabilityAnActualDefinitionInTheBase
  | proveContextRelativeSeparationIsForcedRatherThanPermitted
  | extendBeyondThreeAlternatives
  deriving DecidableEq, Repr

def indistinguishabilityOpenObligations :
    List IndistinguishabilityOpenObligation :=
  [ .deriveComplexAmplitudesAndPhase,
    .giveStableDistinguishabilityAnActualDefinitionInTheBase,
    .proveContextRelativeSeparationIsForcedRatherThanPermitted,
    .extendBeyondThreeAlternatives ]

theorem indistinguishability_keeps_four_open_obligations :
    indistinguishabilityOpenObligations.length = 4 := by
  rfl

def indistinguishabilityClaimBoundary : String :=
  "Over three alternatives in ℚ: a kernel separating all pairs has no two-path interference and an exactly additive readout, interference forces an unseparated pair, and a globally separating family of contexts never interferes. So on the reading that the kernel off-diagonal records failure of stable distinguishability, interference exists iff distinguishability fails and is context-relative iff distinguishability is. This reduces the Born readout to the founding commitment of a context-first theory rather than deriving it; the premise is not proved. Complex amplitudes and phase are supplied by no step of this line."

end QMClosure
end IDT
