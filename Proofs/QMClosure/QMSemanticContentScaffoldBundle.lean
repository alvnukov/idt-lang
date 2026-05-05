import Proofs.QMClosure.QMSemanticKernelRoute
import Proofs.QMClosure.ProjectionScaffoldsDraft
import Proofs.QMClosure.ReadoutScaffoldsDraft
import Proofs.QMClosure.InheritanceScaffoldsDraft
import Proofs.QMClosure.CompositeScaffoldsDraft
import Proofs.QMClosure.MonoidalAssociativityDraft
import Proofs.QMClosure.ProjectiveLimitScaffoldDraft
import Proofs.QMClosure.BoundaryScaffoldsDraft

namespace IDT
namespace QMClosure

theorem projection_scaffold_covers_conservative_gluing
    {alpha : Type}
    (left right : Endomap alpha)
    (leftIdempotent : Idempotent left)
    (rightIdempotent : Idempotent right)
    (commutes : Commute left right) :
    Idempotent (composeEndomap left right)
      ∧ composeEndomap left right = composeEndomap right left :=
  And.intro
    (commuting_idempotent_composition_idempotent
      left right leftIdempotent rightIdempotent commutes)
    (commuting_projections_have_consistent_composition left right commutes)

theorem readout_scaffold_covers_context_probability_route :
    (∀ readout : StableFiniteReadout,
      normalizationDenominator readout > 0
        ∧ (normalizedReadout readout).length = readout.weights.length)
      ∧ (∀ blocks : List FiniteReadout,
        contextTotal (flattenReadoutBlocks blocks) =
          contextTotal (coarseGrainBlocks blocks))
      ∧ (∀ event : Type,
        ∀ equivalent : event → event → Prop,
        ∀ weight : EventWeight event,
        RespectsOperationalEquivalence equivalent weight →
          ∀ left right : event,
            equivalent left right → weight left = weight right) :=
  And.intro
    (fun readout =>
      And.intro
        (stable_finite_readout_has_positive_denominator readout)
        (normalized_readout_length_matches readout))
    (And.intro
      coarse_grain_blocks_preserve_total
      (fun _event equivalent weight respects left right equivalentEvents =>
        operational_equivalence_respecting_weight_function_preserves_weight
          equivalent weight respects left right equivalentEvents))

theorem inheritance_scaffold_covers_reversible_action_fragments :
    (∀ alpha : Type,
      ∀ relation : Distinguishability alpha,
        PreservesDistinguishability relation (id : InheritanceMap alpha))
      ∧ (∀ alpha : Type,
        ∀ overlap : Overlap alpha,
          PreservesOverlap overlap (id : InheritanceMap alpha))
      ∧ (∀ alpha : Type,
        ∀ fact : ProjectiveFact alpha,
          projectiveAction (id : InheritanceMap alpha) fact = fact) :=
  And.intro
    (fun _alpha relation => identity_preserves_distinguishability relation)
    (And.intro
      (fun _alpha overlap => identity_preserves_overlap overlap)
      (fun _alpha fact => projective_action_identity fact))

theorem composite_scaffold_covers_product_local_tomography :
    ∀ state : Type,
      ∀ productReadouts : List (Readout state),
        SeparatesStates productReadouts → LocalTomography productReadouts :=
  fun _state productReadouts separates =>
    product_readout_separation_implies_local_tomography
      productReadouts separates

theorem monoidal_scaffold_covers_associativity :
    (∀ alpha : Type,
      ∀ a b c : FiniteContextProduct alpha,
        contextProduct (contextProduct a b) c =
          contextProduct a (contextProduct b c))
      ∧ (∀ atom : Type,
        ∀ a b c : ContextProductExpr atom,
          ContextProductExpr.equivalentByFlatten
            (ContextProductExpr.productContext
              (ContextProductExpr.productContext a b) c)
            (ContextProductExpr.productContext a
              (ContextProductExpr.productContext b c))) :=
  And.intro
    (fun _alpha a b c => finite_context_product_assoc a b c)
    (fun _atom a b c =>
      ContextProductExpr.product_context_expr_assoc_up_to_flatten a b c)

theorem projective_limit_scaffold_covers_consistency :
    ∀ level : Type,
      ∀ tower : FiniteTower level,
        PairwiseCompatible tower → ProjectiveLimitConsistent tower :=
  fun _level tower compatible =>
    pairwise_compatibility_implies_projective_limit_consistency
      tower compatible

theorem calibrated_scale_scaffold_keeps_boundary :
    calibratedOnlyBoundary.calibratedAnchor = true
      ∧ calibratedOnlyBoundary.firstPrinciplesDerivation = false :=
  calibrated_anchor_is_not_first_principles_derivation

structure QMSemanticContentScaffoldCoverage where
  conservativeProjectiveGluingScaffold : Prop
  readoutProbabilityScaffold : Prop
  inheritanceActionScaffold : Prop
  productLocalTomographyScaffold : Prop
  monoidalAssociativityScaffold : Prop
  projectiveLimitConsistencyScaffold : Prop
  calibratedScaleBoundaryScaffold : Prop

def qmSemanticContentScaffoldCoverage :
    QMSemanticContentScaffoldCoverage :=
  {
    conservativeProjectiveGluingScaffold :=
      ∀ alpha : Type,
        ∀ left right : Endomap alpha,
          Idempotent left →
            Idempotent right →
              Commute left right →
                Idempotent (composeEndomap left right)
                  ∧ composeEndomap left right = composeEndomap right left,
    readoutProbabilityScaffold :=
      (∀ readout : StableFiniteReadout,
        normalizationDenominator readout > 0
          ∧ (normalizedReadout readout).length = readout.weights.length)
        ∧ (∀ blocks : List FiniteReadout,
          contextTotal (flattenReadoutBlocks blocks) =
            contextTotal (coarseGrainBlocks blocks))
        ∧ (∀ event : Type,
          ∀ equivalent : event → event → Prop,
          ∀ weight : EventWeight event,
          RespectsOperationalEquivalence equivalent weight →
            ∀ left right : event,
              equivalent left right → weight left = weight right),
    inheritanceActionScaffold :=
      (∀ alpha : Type,
        ∀ relation : Distinguishability alpha,
          PreservesDistinguishability relation (id : InheritanceMap alpha))
        ∧ (∀ alpha : Type,
          ∀ overlap : Overlap alpha,
            PreservesOverlap overlap (id : InheritanceMap alpha))
        ∧ (∀ alpha : Type,
          ∀ fact : ProjectiveFact alpha,
            projectiveAction (id : InheritanceMap alpha) fact = fact),
    productLocalTomographyScaffold :=
      ∀ state : Type,
        ∀ productReadouts : List (Readout state),
          SeparatesStates productReadouts → LocalTomography productReadouts,
    monoidalAssociativityScaffold :=
      (∀ alpha : Type,
        ∀ a b c : FiniteContextProduct alpha,
          contextProduct (contextProduct a b) c =
            contextProduct a (contextProduct b c))
        ∧ (∀ atom : Type,
          ∀ a b c : ContextProductExpr atom,
            ContextProductExpr.equivalentByFlatten
              (ContextProductExpr.productContext
                (ContextProductExpr.productContext a b) c)
              (ContextProductExpr.productContext a
                (ContextProductExpr.productContext b c))),
    projectiveLimitConsistencyScaffold :=
      ∀ level : Type,
        ∀ tower : FiniteTower level,
          PairwiseCompatible tower → ProjectiveLimitConsistent tower,
    calibratedScaleBoundaryScaffold :=
      calibratedOnlyBoundary.calibratedAnchor = true
        ∧ calibratedOnlyBoundary.firstPrinciplesDerivation = false
  }

theorem qm_semantic_content_scaffold_bundle_is_machine_checked :
    qmSemanticContentScaffoldCoverage.conservativeProjectiveGluingScaffold
      ∧ qmSemanticContentScaffoldCoverage.readoutProbabilityScaffold
      ∧ qmSemanticContentScaffoldCoverage.inheritanceActionScaffold
      ∧ qmSemanticContentScaffoldCoverage.productLocalTomographyScaffold
      ∧ qmSemanticContentScaffoldCoverage.monoidalAssociativityScaffold
      ∧ qmSemanticContentScaffoldCoverage.projectiveLimitConsistencyScaffold
      ∧ qmSemanticContentScaffoldCoverage.calibratedScaleBoundaryScaffold :=
  And.intro
    (fun _alpha left right leftIdempotent rightIdempotent commutes =>
      projection_scaffold_covers_conservative_gluing
        left right leftIdempotent rightIdempotent commutes)
    (And.intro
      readout_scaffold_covers_context_probability_route
      (And.intro
        inheritance_scaffold_covers_reversible_action_fragments
        (And.intro
          composite_scaffold_covers_product_local_tomography
          (And.intro
            monoidal_scaffold_covers_associativity
            (And.intro
              projective_limit_scaffold_covers_consistency
              calibrated_scale_scaffold_keeps_boundary)))))

end QMClosure
end IDT
