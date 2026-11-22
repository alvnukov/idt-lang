"""Finite endpoint predictions from a supplied rooted adjacency experiment.

A germ at vertex u is an incident neighbor p, not a coordinate or a global
edge color. Crossing u->v returns the germ toward u when p=v; otherwise it
takes the unique fourth corner in (N(p) intersect N(v)) minus {u}. A supplied
reversible binary recorder flips, or not, separately for those two cases.
Enumerate all reachable (vertex, germ, bit), starting at bit zero once for
each incident root germ. Endpoint *bits* must be path independent; endpoint
germs need not be. Exhaust first: a missing/ambiguous required square makes
this operation unsupported; partial exploration cannot certify a rejection.

At the marked route's final vertex t and each submitted reference vertex v,
compare the two endpoint bits of each unordered pair of distinct root germs.
Agreeing strict orders vote +1, opposing strict orders -1, ties abstain.
The signed tally is an integer on this particular graph, not a sample, a
physical charge, a geometry, or evidence that any omitted apparatus exists.
References are externally submitted demands, not fit by this evaluator.
Each origin has at most 2*sum(degrees)<=512 product states; two witnessed
vertex routes therefore need at most 1024 small vertex IDs in total. There
are at most 32 integer comparison rows. The public JSON reader separately
caps raw input bytes (including whitespace) at 128 KiB.
"""

from __future__ import annotations

import hashlib
from collections import deque
from dataclasses import dataclass
from itertools import combinations
from math import isfinite
from pathlib import Path
from time import monotonic

from theory_experiments.primitive_screen import Check, Limits, bounded_int, candidate_id

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
SCOPE = "only_submitted_rooted_graph_recorder_path_independence_and_finite_tally_intervals"
FLAT_CHECK_ID = "relational_germ_endpoint_bit_path_independence"
TALLY_CHECK_ID = "relational_germ_paired_ballot_reference"
ASSUMPTIONS = ("supplied_simple_reciprocal_graph_and_identifiable_vertex_reunions",
               "controlled_paths_from_a_fixed_root_and_one_selectable_root_germ_at_a_time",
               "unique_local_square_transport_with_the_submitted_two_state_recorder",
               "initial_bit_zero_for_each_root_germ")
TALLY_ASSUMPTIONS = (*ASSUMPTIONS, "comparable_repeated_preparations_and_signed_all_pairs_tally",
                     "given_two_edge_mark_and_externally_supplied_integer_reference_intervals")
MAX_VERTICES, MAX_DEGREE, MAX_REFERENCE = 32, 8, 10**6


def _seq(o, kind, lo, hi):
    if type(o) is not kind or not lo <= len(o) <= hi:
        raise ValueError(f"expected {kind.__name__} of length {lo}..{hi}")
    return o


def _obj(o, fields):
    if type(o) is not dict or len(o) != len(fields) or set(o) != fields:
        raise ValueError(f"expected exactly {sorted(fields)}")
    return o


@dataclass(frozen=True)
class RelationalGermObserver:
    id: str
    adjacency: tuple[tuple[int, ...], ...]
    marked_route: tuple[int, int, int]
    flip_on_same: bool
    flip_on_different: bool
    references: tuple[tuple[int, int, int], ...]

    def __post_init__(self):
        if type(self.id) is not str:
            raise ValueError("expected a short fixed id")
        candidate_id(self.id)
        n=len(_seq(self.adjacency,tuple,3,MAX_VERTICES))
        for i,row in enumerate(self.adjacency):
            for v in _seq(row,tuple,0,MAX_DEGREE):
                bounded_int(v,0,n-1)
            if i in row or tuple(sorted(set(row)))!=row:
                raise ValueError("expected sorted unique non-self neighbors")
        if any(i not in self.adjacency[j] for i,row in enumerate(self.adjacency) for j in row):
            raise ValueError("edges must be reciprocal")
        r,b,t=(bounded_int(v,0,n-1) for v in _seq(self.marked_route,tuple,3,3))
        if r==t or b not in self.adjacency[r] or t not in self.adjacency[b]:
            raise ValueError("expected an actual nonbacktracking two-edge route")
        if type(self.flip_on_same) is not bool or type(self.flip_on_different) is not bool:
            raise ValueError("recorder flip choices must be Boolean")
        last=-1
        for row in _seq(self.references,tuple,1,n):
            v,lo,hi=_seq(row,tuple,3,3)
            bounded_int(v,0,n-1)
            bounded_int(lo,-MAX_REFERENCE,MAX_REFERENCE)
            bounded_int(hi,-MAX_REFERENCE,MAX_REFERENCE)
            if v<=last or lo>hi:
                raise ValueError("expected one sorted closed interval per reference vertex")
            last=v

    def specification(self):
        return {"id":self.id,"family":"relational_germ_observer","adjacency":[list(a) for a in self.adjacency],
                "marked_route":list(self.marked_route),"recorder":{"flip_on_same":self.flip_on_same,
                "flip_on_different":self.flip_on_different},
                "references":[{"vertex":v,"lower":lo,"upper":hi} for v,lo,hi in self.references]}


def parse_relational_germ_observer(value: object) -> RelationalGermObserver:
    raw=_obj(value,{"id","family","adjacency","marked_route","recorder","references"})
    if type(raw["family"]) is not str or raw["family"]!="relational_germ_observer":
        raise ValueError("expected relational_germ_observer family")
    rec=_obj(raw["recorder"],{"flip_on_same","flip_on_different"})
    rows=_seq(raw["adjacency"],list,3,MAX_VERTICES)
    n=len(rows)
    graph=tuple(tuple(sorted(bounded_int(v,0,n-1) for v in _seq(row,list,0,MAX_DEGREE))) for row in rows)
    refs=[]
    for row in _seq(raw["references"],list,1,n):
        row=_obj(row,{"vertex","lower","upper"})
        refs.append((bounded_int(row["vertex"],0,n-1),bounded_int(row["lower"],-MAX_REFERENCE,MAX_REFERENCE),
                     bounded_int(row["upper"],-MAX_REFERENCE,MAX_REFERENCE)))
    return RelationalGermObserver(raw["id"],graph,tuple(_seq(raw["marked_route"],list,3,3)),
                                  rec["flip_on_same"],rec["flip_on_different"],tuple(sorted(refs)))


def _route(parents,state):
    path=[]
    while state is not None:
        path.append(state[0])
        state=parents[state]
    return path[::-1]


def evaluate_relational_germ_observer(
    candidate: RelationalGermObserver, limits: Limits, *, deadline: float | None = None,
) -> tuple[tuple[Check, ...],dict[str,object]]:
    if type(candidate) is not RelationalGermObserver or type(limits) is not Limits:
        raise TypeError("expected exact RelationalGermObserver and Limits")
    if deadline is not None and (type(deadline) not in (int,float) or
                                  (type(deadline) is float and not isfinite(deadline))):
        raise ValueError("deadline must be finite absolute monotonic time")
    g=candidate.adjacency
    neighbors=tuple(frozenset(a) for a in g)
    r,_,t=candidate.marked_route
    ports=g[r]
    signs={}
    completed=expanded=edges=discovered=multi=0
    first_conflict=None
    reports=[]
    details={"rejection_scope":SCOPE,"scientific_status":"unassessed","proof_status":"not_attempted",
             "empirical_status":"not_tested","finite_submitted_contract_only":True,
             "vertices":len(g),"marked_route":list(candidate.marked_route),"root_germs":list(ports),
             "ballots_per_reached_reference":len(ports)*(len(ports)-1)//2,
             "references_submitted":len(candidate.references),"reference_comparisons":reports,
             "budget_semantics":"one_fully_expanded_reachable_product_state_per_origin;bounds_do_not_count_ballots",
             "check_units":["fully_exhausted_root_germs","compared_reference_vertices"],
             "unused_limits":["coefficient_radius","reference_radius","max_copies"],
             "local_domain_issue":None,"flat_bit_domain_complete":False,
             "endpoint_bit_path_independent":None}
    def expired():
        return deadline is not None and monotonic()>=deadline
    def finish(s1,s2,reason,*,w1=None,w2=None,tally_planned=0):
        details.update(stop_reason=reason,root_germs_fully_explored=completed,product_states_discovered=discovered,
                       product_states_fully_expanded=expanded,outgoing_transfers_examined=edges,
                       multiple_germs_at_vertex_in_completed_closures=multi)
        return (Check(FLAT_CHECK_ID,s1,completed,len(ports),"=0",ASSUMPTIONS,w1),
                Check(TALLY_CHECK_ID,s2,len(reports),tally_planned,">=0",TALLY_ASSUMPTIONS,w2)),details

    for origin in ports:
        start=(r,origin,0)
        queue=deque([start])
        parents={start:None}
        discovered+=1
        endpoint={r:start}
        germs={r:{origin}}
        while queue:
            if expired():
                return finish("inconclusive","inconclusive","deadline")
            if expanded>=limits.max_cases:
                return finish("inconclusive","inconclusive","max_cases")
            state=queue.popleft()
            u,p,bit=state
            for v in g[u]:
                if expired():
                    return finish("inconclusive","inconclusive","deadline")
                edges+=1
                if v==p:
                    other=u
                    flip=candidate.flip_on_same
                else:
                    fourth=(neighbors[v]&neighbors[p])-{u}
                    if len(fourth)!=1:
                        details["local_domain_issue"]={"root_germ":origin,"route_to_source":_route(parents,state),
                                                       "source":u,"transported_germ":p,"cross_to":v,
                                                       "fourth_corner_candidates":sorted(fourth)}
                        return finish("unsupported","unsupported","missing_or_ambiguous_reachable_square")
                    other=next(iter(fourth))
                    flip=candidate.flip_on_different
                nxt=(v,other,bit^flip)
                if nxt in parents:
                    continue
                parents[nxt]=state
                discovered+=1
                queue.append(nxt)
                old=endpoint.setdefault(v,nxt)
                germs.setdefault(v,set()).add(other)
                if old[2]!=nxt[2] and first_conflict is None:
                    first_conflict={"inputs":{"root_germ":origin,"endpoint":v,
                                    "routes":[_route(parents,old),_route(parents,nxt)],
                                    "final_bits":[old[2],nxt[2]]},"actual":"1","required":"=0"}
            expanded+=1
        completed+=1
        multi+=sum(len(ps)>1 for ps in germs.values())
        signs[origin]={v:q[2] for v,q in endpoint.items()}
    if expired():
        return finish("inconclusive","inconclusive","deadline")
    details["flat_bit_domain_complete"]=True
    details["endpoint_bit_path_independent"]=first_conflict is None
    if first_conflict is not None:
        return finish("counterexample","unsupported","two_paths_to_different_endpoint_bits",w1=first_conflict)
    success="no_counterexample_within_bounds"
    missing=[v for v,_,_ in candidate.references if any(v not in signs[p] for p in ports)]
    if missing:
        details["unreachable_references"]=missing
        return finish(success,"unsupported","reference_outside_root_component")
    witness=None
    planned=len(candidate.references)
    for v,lo,hi in candidate.references:
        if expired():
            return finish(success,"inconclusive","deadline",tally_planned=planned)
        votes={-1:0,0:0,1:0}
        for a,b in combinations(ports,2):
            votes[(signs[a][t]-signs[b][t])*(signs[a][v]-signs[b][v])]+=1
        value=votes[1]-votes[-1]
        entry={"vertex":v,"plus":votes[1],"minus":votes[-1],"abstain":votes[0],"tally":value,
               "lower":lo,"upper":hi}
        reports.append(entry)
        if not lo<=value<=hi and witness is None:
            witness={"inputs":{**entry,"root_germs":list(ports),
                     "mark_bits":[signs[p][t] for p in ports],"reference_bits":[signs[p][v] for p in ports]},
                     "actual":str(min(value-lo,hi-value)),"required":">=0"}
    if expired():
        return finish(success,"inconclusive","deadline",tally_planned=planned)
    return finish(success,"counterexample" if witness else success,
                  "submitted_tally_interval_mismatch" if witness else "finite_submitted_intervals_matched",
                  w2=witness,tally_planned=planned)
