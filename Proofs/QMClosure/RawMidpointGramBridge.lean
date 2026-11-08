import Proofs.QMClosure.RawMidpointGramGeometry
import Proofs.QMClosure.RawFourPointGramBridge

/-!
# Midpoint-compatible kernels imply the raw sparse conclusions

The existing local kernel compatibility contract is supplied explicitly. Real
kernel scaling, pairwise nonnegative squares, and squared midpoint convexity
derive every finite Gram positivity inequality. Its four-point instance feeds
the existing conditional bridge to conservation, observed mediality, and the
actual sparse marginal law.
-/

namespace IDT.QMClosure.RawMidpointGramBridge

noncomputable section

open RawSparseConservationSelection
open RawMidpointGramGeometry
open RawFourPointGramBridge

variable {V : Type*}

theorem conclusions_of_squaredMidpointConvex (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hconv : SquaredMidpointConvex G mid) :
    (∀ n, RawGramGeometry.GramNonnegative G n) ∧
      (∀ x, 0 ≤ D.weight x) ∧ PairConserved D ∧ ObservedMedial D ∧
      SparseMarginalLaw D ∧ RawSparseConservationTests.Tests D := by
  have hgram := gramNonnegative_of_squaredMidpointConvex hk.symmetric scale hscale
    hnonneg mid hconv
  exact ⟨hgram, conclusions_of_fourPointPositive D G hk (hgram 4)⟩

theorem conclusions_of_distanceMidpointConvex (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (d : V → V → ℝ) (dnonneg : ∀ x y, 0 ≤ d x y)
    (dsquare : ∀ x y, (d x y) ^ 2 = squaredDistance G x y)
    (mid : V → V → V) (hconv : DistanceMidpointConvex d mid) :
    (∀ n, RawGramGeometry.GramNonnegative G n) ∧
      (∀ x, 0 ≤ D.weight x) ∧ PairConserved D ∧ ObservedMedial D ∧
      SparseMarginalLaw D ∧ RawSparseConservationTests.Tests D := by
  exact conclusions_of_squaredMidpointConvex D G hk scale hscale
    (nonnegativeSquaredDistances_of_distance d dsquare) mid
    (squaredMidpointConvex_of_distanceMidpointConvex d dnonneg dsquare mid hconv)

end

end IDT.QMClosure.RawMidpointGramBridge
