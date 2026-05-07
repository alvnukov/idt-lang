import Proofs.MetaLang.V8StatusTransitionPolicy

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 dependency-graph policy.

This module moves the research-graph safety discipline into Lean. It does not
export or visualize a graph, and it does not prove any physical claim. It only
states the meta-language conditions required before dependency-based claim
movement is accepted.
-/

structure DependencyEdge where
  fromRef : String
  toRef : String
deriving DecidableEq, Repr

structure DependencyGraph where
  nodes : List String
  edges : List DependencyEdge
deriving Repr

def DependencyGraph.hasNode
    (graph : DependencyGraph)
    (reference : String) : Prop :=
  reference ∈ graph.nodes

def DependencyGraph.hasEdge
    (graph : DependencyGraph)
    (fromRef : String)
    (toRef : String) : Prop :=
  { fromRef := fromRef, toRef := toRef } ∈ graph.edges

inductive DependencyGraph.Reachable
    (graph : DependencyGraph) : String → String → Prop where
  | step {fromRef toRef : String} :
      graph.hasEdge fromRef toRef →
      DependencyGraph.Reachable graph fromRef toRef
  | trans {fromRef midRef toRef : String} :
      DependencyGraph.Reachable graph fromRef midRef →
      DependencyGraph.Reachable graph midRef toRef →
      DependencyGraph.Reachable graph fromRef toRef

def DependencyGraph.acyclic
    (graph : DependencyGraph) : Prop :=
  ∀ reference, ¬ DependencyGraph.Reachable graph reference reference

def DependencyGraph.edgesAreGrounded
    (graph : DependencyGraph) : Prop :=
  ∀ edge, edge ∈ graph.edges →
    graph.hasNode edge.fromRef ∧ graph.hasNode edge.toRef

def DependencyGraph.hasNoSelfEdges
    (graph : DependencyGraph) : Prop :=
  ∀ edge, edge ∈ graph.edges → edge.fromRef ≠ edge.toRef

structure AcceptedDependencyGraph where
  graph : DependencyGraph
  grounded : graph.edgesAreGrounded
  acyclic : graph.acyclic

theorem accepted_dependency_graph_edges_are_grounded
    (accepted : AcceptedDependencyGraph)
    (edge : DependencyEdge)
    (edgePresent : edge ∈ accepted.graph.edges) :
    accepted.graph.hasNode edge.fromRef ∧ accepted.graph.hasNode edge.toRef :=
  accepted.grounded edge edgePresent

theorem accepted_dependency_graph_has_no_cycles
    (accepted : AcceptedDependencyGraph)
    (reference : String) :
    ¬ DependencyGraph.Reachable accepted.graph reference reference :=
  accepted.acyclic reference

theorem accepted_dependency_graph_has_no_self_edges
    (accepted : AcceptedDependencyGraph) :
    accepted.graph.hasNoSelfEdges := by
  intro edge edgePresent sameRef
  apply accepted.acyclic edge.fromRef
  exact DependencyGraph.Reachable.step (by
    unfold DependencyGraph.hasEdge
    cases edge with
    | mk fromRef toRef =>
        simp at edgePresent sameRef ⊢
        subst toRef
        exact edgePresent)

structure DependencyClaimRecord where
  claimRef : String
  claimStatus : ClaimStatus
  dependencies : List DependencyStatus
deriving Repr

structure DependencyClaimLedger where
  graph : AcceptedDependencyGraph
  records : List DependencyClaimRecord

def DependencyClaimRecord.hasOpenOrBlockedDependency
    (record : DependencyClaimRecord) : Prop :=
  ∃ dependency, dependency ∈ record.dependencies
    ∧ dependency.isOpenOrBlocked

def DependencyClaimRecord.forwardStatusIsDependencyClean
    (record : DependencyClaimRecord) : Prop :=
  (record.claimStatus = ClaimStatus.derived
      ∨ record.claimStatus = ClaimStatus.formalProof) →
    ¬ record.hasOpenOrBlockedDependency

def DependencyClaimRecord.dependenciesAreGrounded
    (graph : DependencyGraph)
    (record : DependencyClaimRecord) : Prop :=
  graph.hasNode record.claimRef
    ∧ ∀ dependency, dependency ∈ record.dependencies →
      graph.hasEdge record.claimRef dependency.reference

def DependencyClaimLedger.isAcceptedForV8
    (ledger : DependencyClaimLedger) : Prop :=
  ∀ record, record ∈ ledger.records →
    record.dependenciesAreGrounded ledger.graph.graph
      ∧ record.forwardStatusIsDependencyClean

theorem accepted_dependency_claim_ledger_records_are_grounded
    (ledger : DependencyClaimLedger)
    (accepted : ledger.isAcceptedForV8)
    (record : DependencyClaimRecord)
    (recordPresent : record ∈ ledger.records) :
    record.dependenciesAreGrounded ledger.graph.graph :=
  (accepted record recordPresent).left

theorem accepted_dependency_claim_ledger_forward_records_are_clean
    (ledger : DependencyClaimLedger)
    (accepted : ledger.isAcceptedForV8)
    (record : DependencyClaimRecord)
    (recordPresent : record ∈ ledger.records)
    (forward :
      record.claimStatus = ClaimStatus.derived
        ∨ record.claimStatus = ClaimStatus.formalProof) :
    ¬ record.hasOpenOrBlockedDependency :=
  (accepted record recordPresent).right forward

end V8
end MetaLang
end IDT
