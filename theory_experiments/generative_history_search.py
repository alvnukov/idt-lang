"""Context-local finite bags with supplied cyclic composition and cancellation.

This is a fixed combinatorial-source probe, not a physical model or proof.
All variants remain unsupported source proposals; no registered adapter changes.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import combinations_with_replacement, product
from pathlib import Path
from typing import TypeAlias

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import History, record_batch
from theory_experiments.primitive_screen import (
    Limits,
    canonical_json,
    load_json,
    object_fields,
)
from theory_experiments.source_candidate import SourceCandidate, SourceSnapshot

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONFIG = ROOT / "data/generative_history_search_v1.json"
SOURCE_PATHS = (
    "theory_experiments/generative_history_search.py", "scripts/search_generative_histories.py",
    "data/generative_history_search_v1.json", "theory_experiments/source_candidate.py",
    "theory_experiments/primitive_screen.py", "theory_experiments/candidate_pipeline.py",
    "theory_experiments/candidate_history.py",
)
Bag: TypeAlias = tuple[int, ...]
MISSING_BRIDGES = ("primitive_derivation", "physical_states_preparations", "physical_readout_normalization",
                   "admissible_operations", "physical_composites", "continuum", "full_QM", "SM", "gravity")


def source_hashes() -> dict[str, str]:
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in SOURCE_PATHS}


LOADED_SOURCE_HASHES = source_hashes()


def unit(m: int, label: int) -> Bag:
    return tuple(int(i == label) for i in range(m))


def union(x: Bag, y: Bag) -> Bag:
    return tuple(a+b for a, b in zip(x, y, strict=True))


def serial(x: Bag, y: Bag) -> Bag:
    """Raw Cartesian bag pairs first; never project inputs before composition."""
    m = len(x)
    out = [0]*m
    for i, a in enumerate(x):
        for j, b in enumerate(y):
            out[(i+j) % m] += a*b
    return tuple(out)


def normal(x: Bag) -> Bag:
    if len(x) == 3:
        return x[0]-x[2], x[1]-x[2]
    r = len(x)//2
    return tuple(x[i]-x[i+r] for i in range(r))


def reduced_serial(x: Bag, y: Bag, m: int) -> Bag:
    """Independent signed quotient polynomial calculation, after raw construction."""
    if m == 3:
        a, b = x
        c, d = y
        return a*c-b*d, a*d+b*c-b*d  # q^2 = -1-q
    r = m//2
    out = [0]*r
    for i, a in enumerate(x):
        for j, b in enumerate(y):
            out[(i+j) % r] += a*b*(1 if i+j < r else -1)
    return tuple(out)


def generators(m: int) -> tuple[Bag, ...]:
    return ((1, 1, 1),) if m == 3 else tuple(sorted(union(unit(m, j), unit(m, j+m//2)) for j in range(m//2)))


def bags(m: int) -> tuple[Bag, ...]:
    values = {tuple([0]*m)}
    for size in (1, 2):
        for labels in combinations_with_replacement(range(m), size):
            values.add(tuple(labels.count(i) for i in range(m)))
    return tuple(sorted(values))


@dataclass(frozen=True)
class Variant:
    id: str
    group: str
    m: int
    readout: str
    kernel2: tuple[int, ...] = ()

    def weight2(self, n: Bag) -> int:
        """Twice the exact weight, including half-integral pair kernels."""
        if self.kernel2:
            return sum(a*b*self.kernel2[(i-j) % self.m]
                       for i, a in enumerate(n) for j, b in enumerate(n))
        if self.readout == "raw_cardinality":
            return 2*sum(n)
        d = normal(n)
        if self.readout == "residual_l1":
            return 2*sum(abs(a) for a in d)
        a = sum(v*v for v in d)
        if self.readout == "diagonal_square":
            return 2*a*a
        b = d[0]*d[1]-d[0]*d[3]+d[1]*d[2]+d[2]*d[3]
        return 2*(a*a-2*b*b)

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "group": self.group, "cyclic_labels": self.m,
                "carrier": "context_local_nonnegative_integer_count_vectors",
                "alternative": "disjoint_union_coordinate_addition",
                "serial": "raw_cartesian_pairs_label_sum_mod_m_then_reduce",
                "cancellation": "e0+e1+e2~0" if self.m == 3 else "e_j+e_(j+m/2)~0",
                "normal_form": "(n0-n2,n1-n2)" if self.m == 3 else "d_i=n_i-n_(i+m/2)",
                "readout": self.readout, "ordered_pair_kernel": [str(Fraction(k, 2)) for k in self.kernel2],
                "non_pair_formulas": {"raw_cardinality": "sum(n)", "residual_l1": "sum(abs(d))",
                    "diagonal_square": "(sum(d_i^2))^2",
                    "quartic_norm": "A^2-2B^2; A=sum(d_i^2); B=d0*d1-d0*d3+d1*d2+d2*d3"},
                "unit_reference_fringe": "W(e0+ej), convention_only_not_empirical_prediction"}


def candidates() -> tuple[Variant, ...]:
    variants = []
    for m in (2, 4, 6, 8):
        kernel = tuple(2 if j == 0 else -2 if j == m//2 else 0 for j in range(m))
        variants.append(Variant(f"history_c{m}_diagonal", f"c{m}_diagonal", m, "diagonal_pair", kernel))
    variants.append(Variant("history_c3_triangle", "c3_triangle", 3, "triangle_pair", (2, -1, -1)))
    for kind in ("raw_cardinality", "residual_l1", "diagonal_square"):
        variants.append(Variant("history_c4_"+kind, "c4_"+kind, 4, kind))
    for m in (6, 8):
        for a2 in range(-4, 5):
            kernel = ((2, a2, -a2, -2, -a2, a2) if m == 6 else
                      (2, a2, 0, -a2, -2, -a2, 0, a2))
            variants.append(Variant(f"history_c{m}_kernel_a2_{'n' if a2 < 0 else 'p'}{abs(a2)}",
                                    f"c{m}_kernel_grid", m, "kernel_pair", kernel))
    variants.append(Variant("history_c8_quartic", "c8_quartic", 8, "quartic_norm"))
    return tuple(variants)


def campaign_config() -> dict[str, object]:
    return {"schema": "idt-generative-history-search-config/1", "candidate_ids": [v.id for v in candidates()],
            "bag_total_bound": 2, "cyclic_orders": [2, 3, 4, 6, 8], "kernel_a2_grid": list(range(-4, 5)),
            "bag_order": "lexicographic_count_vectors", "all_ordered_pairs": True,
            "all_ordered_triples": True, "all_generator_insertions": True,
            "descent_continuations": "all_bounded_bags_both_left_and_right",
            "clip_operation_outputs": False, "arithmetic": "exact_integer_twice_weights",
            "kernel_selection": {"orders": [3, 4], "kernel_a2_b2_grid": list(range(-4, 5)),
                                 "criterion": "reference_invariant_cancellation_not_isolated_zero"},
            "scope": "fixed_context_local_toy_histories_not_universal_or_physical"}


def validate_config(value: object) -> dict[str, object]:
    row = object_fields(value, set(campaign_config()))
    if canonical_json(row) != canonical_json(campaign_config()):
        raise ValueError("only the fixed reviewed generative-history configuration is accepted")
    return row


def load_config(path: Path = DEFAULT_CONFIG) -> dict[str, object]:
    return validate_config(load_json(path))


def exact(twice: int) -> str:
    return str(Fraction(twice, 2))


def kernel_hypotheses(m: int) -> list[dict[str, object]]:
    values: list[dict[str, object]] = []
    for a2, b2 in product(range(-4, 5), (0,) if m == 3 else range(-4, 5)):
        kernel = (2, a2, a2) if m == 3 else (2, a2, b2, a2)
        values.append({"id": f"selection_c{m}_a2_{a2}_b2_{b2}",
                       "ordered_pair_kernel": [exact(k) for k in kernel]})
    return values


@dataclass
class Probe:
    planned: int
    performed: int = 0
    failures: int = 0
    first_witness: dict[str, object] | None = None

    def observe(self, passes: bool, witness: dict[str, object]) -> None:
        self.performed += 1
        if not passes:
            self.failures += 1
            if self.first_witness is None:
                self.first_witness = witness

    def report(self) -> dict[str, object]:
        if self.planned != self.performed:
            raise ValueError("incomplete fixed-domain probe")
        return {"planned": self.planned, "performed": self.performed, "failures": self.failures,
                "first_witness": self.first_witness,
                "result": ("not_applicable_no_calculation" if not self.planned else
                           "counterexample" if self.failures else "no_counterexample_within_domain")}


def kernel_selection(m: int) -> dict[str, object]:
    domain, gens = bags(m), generators(m)
    rows = []
    selected = []
    performed = 0
    for spec in kernel_hypotheses(m):
        kernel = spec["ordered_pair_kernel"]
        if not isinstance(kernel, list):
            raise TypeError("expected exact kernel array")
        model = Variant(str(spec["id"]), "conditional_kernel_selection", m, "kernel_pair",
                        tuple(int(2*Fraction(str(v))) for v in kernel))
        isolated, insertion = Probe(len(gens)), Probe(len(domain)*len(gens))
        for gen in gens:
            isolated.observe(model.weight2(gen) == 0, {"generator": list(gen), "weight": exact(model.weight2(gen))})
        for x, gen in product(domain, gens):
            before, after = model.weight2(x), model.weight2(union(x, gen))
            insertion.observe(before == after, {"x": list(x), "generator": list(gen),
                                               "before": exact(before), "after": exact(after)})
        if not insertion.failures:
            selected.append(spec["id"])
        performed += insertion.performed
        rows.append({"specification": spec, "isolated_cancellation_zero": isolated.report(),
                     "reference_invariance": insertion.report(),
                     "bounded_input_weights": [exact(model.weight2(x)) for x in domain],
                     "candidate_verdict": "unchanged", "registration_status": "not_registered"})
    return {"cyclic_labels": m, "hypothesis_count": len(rows), "kernels": rows,
            "domain": [list(x) for x in domain], "generators": [list(g) for g in gens],
            "reference_checks_planned": len(rows)*len(domain)*len(gens),
            "reference_checks_performed": performed,
            "selected_within_declared_kernel_class": selected,
            "supplied_conditions": ["ordered_pair_bilinearity_including_self_pairs",
                "symmetric_relative_label_kernel", "K0=1", "imposed_cancellation", "reference_invariance"],
            "scope": "conditional_coefficient_selection_not_Born_or_pair_ansatz_derivation",
            "i3_boundary": "quadratic_ansatz_structurally_expects_I3_zero_not_independent_physics_evidence"}


@lru_cache(maxsize=5)
def operation_evidence(m: int) -> dict[str, object]:
    domain, gens = bags(m), generators(m)
    addition, multiplication = Probe(len(domain)**2), Probe(len(domain)**2)
    descent = {op: Probe(len(domain)**2*len(gens)*2) for op in ("alternative", "serial")}
    for x, y in product(domain, repeat=2):
        for probe, raw, reduced in ((addition, union(x, y), union(normal(x), normal(y))),
                                    (multiplication, serial(x, y), reduced_serial(normal(x), normal(y), m))):
            probe.observe(normal(raw) == reduced, {"x": list(x), "y": list(y),
                          "raw_output": list(raw), "normal_output": list(normal(raw)), "reduced_output": list(reduced)})
    max_output = {"alternative": 0, "serial": 0}
    for x, gen, y in product(domain, gens, domain):
        inserted = union(x, gen)
        for name, operation in (("alternative", union), ("serial", serial)):
            for side in ("left", "right"):
                raw = operation(inserted, y) if side == "left" else operation(y, inserted)
                base = operation(x, y) if side == "left" else operation(y, x)
                max_output[name] = max(max_output[name], sum(raw))
                descent[name].observe(normal(raw) == normal(base), {"x": list(x), "generator": list(gen),
                    "continuation": list(y), "side": side, "raw_output": list(raw), "raw_base": list(base)})
    return {"domain_count": len(domain), "generator_count": len(gens),
            "normal_addition": addition.report(), "normal_serial": multiplication.report(),
            "alternative_descent": descent["alternative"].report(), "serial_descent": descent["serial"].report(),
            "maximum_descent_output_cardinality": max_output, "outputs_clipped": False,
            "scope": "all_generator_insertions_and_all_bounded_continuations_both_sides_not_universal_proof"}


def candidate_evidence(model: Variant) -> dict[str, object]:
    domain, gens = bags(model.m), generators(model.m)
    zero = tuple([0]*model.m)
    weights: dict[Bag, int] = {}

    def w(n: Bag) -> int:
        if n not in weights:
            weights[n] = model.weight2(n)
        return weights[n]

    nonnegative = Probe(len(domain))
    invariance = Probe(len(domain)*len(gens))
    pair_formula = Probe(len(domain) if model.readout in ("diagonal_pair", "triangle_pair") else 0)
    empty = Probe(1)
    empty.observe(w(zero) == 0, {"actual": exact(w(zero)), "expected": "0"})
    multiplication, i2, i3 = Probe(len(domain)**2), Probe(len(domain)**2), Probe(len(domain)**3)
    for x in domain:
        nonnegative.observe(w(x) >= 0, {"x": list(x), "weight": exact(w(x))})
        if pair_formula.planned:
            d = normal(x)
            expected2 = 2*(d[0]**2-d[0]*d[1]+d[1]**2) if model.m == 3 else 2*sum(a*a for a in d)
            pair_formula.observe(w(x) == expected2, {"x": list(x), "raw_ordered_pair": exact(w(x)),
                                                     "quotient_formula": exact(expected2)})
        for gen in gens:
            inserted = union(x, gen)
            invariance.observe(w(x) == w(inserted), {"x": list(x), "generator": list(gen),
                "inserted": list(inserted), "before": exact(w(x)), "after": exact(w(inserted))})
    pair_sums = {(x, y): union(x, y) for x, y in product(domain, repeat=2)}
    for x, y in product(domain, repeat=2):
        raw = serial(x, y)
        multiplication.observe(2*w(raw) == w(x)*w(y), {"x": list(x), "y": list(y),
            "raw_output": list(raw), "actual": exact(w(raw)), "expected": str(Fraction(w(x)*w(y), 4))})
        value = w(pair_sums[x, y])-w(x)-w(y)+w(zero)
        i2.observe(value == 0, {"x": list(x), "y": list(y), "actual": exact(value), "expected_zero_null": "0"})
    for x, y, z in product(domain, repeat=3):
        value = (w(union(pair_sums[x, y], z))-w(pair_sums[x, y])-w(pair_sums[x, z])-w(pair_sums[y, z])
                 + w(x)+w(y)+w(z)-w(zero))
        i3.observe(value == 0, {"x": list(x), "y": list(y), "z": list(z), "actual": exact(value), "expected": "0"})
    one = unit(model.m, 0)
    equal_one = w(union(union(one, one), one))-3*w(union(one, one))+3*w(one)-w(zero)
    fringe = [exact(w(union(one, unit(model.m, j)))) for j in range(model.m)]
    return {"candidate_specification": model.specification(), "candidate_sha256": pipeline.digest(model.specification()),
            "domain": {"order": "lexicographic_count_vectors", "bags": [list(x) for x in domain],
                       "count": len(domain), "total_cardinality_bound": 2},
            "checks": {"empty_zero": empty.report(), "nonnegative_bounded_inputs": nonnegative.report(),
                       "two_alternative_interference": i2.report(), "readout_invariance": invariance.report(),
                       "raw_pair_quotient_formula": pair_formula.report(), "serial_weight_multiplicativity": multiplication.report(),
                       "i3": i3.report()},
            "equal_one_i3": {"inputs": [list(one)]*3, "actual": exact(equal_one)},
            "unit_reference_fringe": {"weights": fringe, "scope": "convention_not_empirical_prediction"},
            "i2_meaning": "zero_additivity_null_counterexample_is_structural_nonadditivity_not_empirical_interference",
            "candidate_verdict": "unchanged", "registration_status": "not_registered"}


def presentation_maps() -> dict[str, object]:
    maps = {3: ((1, 0), (0, 1), (-1, -1)),
            6: ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))}
    rows: dict[str, object] = {}
    for m, mapping in maps.items():
        product_probe, weight_probe = Probe(m*m), Probe(len(bags(m)))
        model = next(v for v in candidates() if v.id == ("history_c3_triangle" if m == 3 else "history_c6_kernel_a2_p1"))
        for i, j in product(range(m), repeat=2):
            actual, expected = reduced_serial(mapping[i], mapping[j], 3), mapping[(i+j) % m]
            product_probe.observe(actual == expected, {"labels": [i, j], "actual": list(actual), "expected": list(expected)})
        for n in bags(m):
            a, b = (sum(n[i]*mapping[i][j] for i in range(m)) for j in range(2))
            expected2 = 2*(a*a-a*b+b*b)
            weight_probe.observe(model.weight2(n) == expected2,
                                 {"bag": list(n), "actual": exact(model.weight2(n)), "expected": exact(expected2)})
        rows[f"c{m}_triangle_coordinates"] = {"label_map": [list(v) for v in mapping],
            "label_products": product_probe.report(), "bounded_weights": weight_probe.report()}
    scalar = next(v for v in candidates() if v.id == "history_c6_kernel_a2_n2")
    product_probe, weight_probe = Probe(36), Probe(len(bags(6)))
    for i, j in product(range(6), repeat=2):
        product_probe.observe((-1)**((i+j) % 6) == (-1)**i*(-1)**j, {"labels": [i, j]})
    for n in bags(6):
        expected2 = 2*sum((-1)**j*n[j] for j in range(6))**2
        weight_probe.observe(scalar.weight2(n) == expected2,
                             {"bag": list(n), "actual": exact(scalar.weight2(n)), "expected": exact(expected2)})
    rows["c6_signed_scalar"] = {"label_map": [1, -1, 1, -1, 1, -1],
                                "label_products": product_probe.report(), "bounded_weights": weight_probe.report()}
    return {"maps": rows, "scope": "exact_supplied_label_products_and_bounded_weights_not_universal_physical_equivalence",
            "interpretation": "C6_survivors_are_signed_scalar_or_C3_lattice_presentations_not_new_arithmetic",
            "bound_warning": "C6_label_(1,1)_is_one_history_but_two_C3_histories_input_bounds_differ"}


def source_archive(hashes: dict[str, str]) -> dict[str, object]:
    archive: dict[str, object] = {}
    for name, expected in hashes.items():
        raw = (ROOT / name).read_bytes()
        if hashlib.sha256(raw).hexdigest() != expected:
            raise ValueError("source changed during archive capture")
        archive[name] = {"sha256": expected, "text": raw.decode("utf-8")}
    return archive


def source_proposals(config: dict[str, object], hashes: dict[str, str], archive_sha: str) -> list[object]:
    path = SOURCE_PATHS[0]
    # Small source span plus exact whole-source binding avoids eleven full copies.
    text = "".join((ROOT / path).read_text(encoding="utf-8").splitlines(keepends=True)[:5])
    snapshot = SourceSnapshot(path, 1, 5, hashes[path], text)
    groups: dict[str, list[Variant]] = {}
    for model in candidates():
        groups.setdefault(model.group, []).append(model)
    specs: list[object] = []
    for group, variants in groups.items():
        components = [canonical_json(model.specification()) for model in variants]
        if group in ("c3_triangle", "c4_diagonal"):
            hypotheses = kernel_hypotheses(variants[0].m)
            # Nine specs fit each bounded source component, including all 81 C4 choices.
            components.extend(canonical_json(hypotheses[i:i+9]) for i in range(0, len(hypotheses), 9))
            components.append("conditional_selection=pair_bilinearity+symmetric_relative_kernel+K0=1"
                              "+imposed_cancellation+reference_invariance; not_Born_or_ansatz_derivation")
        components.extend(("config_sha256="+pipeline.digest(config), "source_context_sha256="+pipeline.digest(hashes),
                           "exact_source_archive_sha256="+archive_sha))
        specs.append(SourceCandidate("generative_"+group, "law_family_collection", tuple(components),
                     "exploratory_finite_not_registered", MISSING_BRIDGES, (snapshot,)).specification())
    if len(canonical_json(specs).encode("utf-8")) > 131072:
        raise ValueError("source proposal batch exceeds 128 KiB")
    return specs


def campaign(value: object, *, history: History | None = None) -> dict[str, object]:
    config = validate_config(value)
    before = source_hashes()
    if before != LOADED_SOURCE_HASHES or pipeline.provenance()["source_sha256"] != pipeline.LOADED_SOURCE_HASHES:
        raise ValueError("sources changed since import; restart from a stable checkout")
    archive = source_archive(before)
    archive_sha = pipeline.digest(archive)
    specs = source_proposals(config, before, archive_sha)
    if source_hashes() != before:
        raise ValueError("sources changed during campaign; rerun")
    archival: dict[str, object] | None = None
    limits = Limits(1000, 1, 2, 2)
    if history is None:
        results = pipeline.run_batch(specs, limits)
    else:
        recorded = record_batch(specs, limits, history=history)
        results = recorded.results
        archival = {"root": str(history.root), "submission": recorded.submission,
                    "observation": recorded.observation, "changes": recorded.changes}
    groups = list(dict.fromkeys(model.group for model in candidates()))
    screens = {group: {"status": result.report["status"], "request_key": result.key,
                "meaning": "source_collection_only_no_registered_physics_adapter"}
               for group, result in zip(groups, results, strict=True)}
    # Source inputs are already archived, even if an expensive probe crashes.
    rows = [{**candidate_evidence(model), "source_proposal_screen": screens[model.group]} for model in candidates()]
    operations = {str(m): operation_evidence(m) for m in (2, 3, 4, 6, 8)}
    selection = {str(m): kernel_selection(m) for m in (3, 4)}
    presentations = presentation_maps()
    if source_hashes() != before or pipeline.provenance()["source_sha256"] != pipeline.LOADED_SOURCE_HASHES:
        raise ValueError("sources changed during campaign; rerun")
    evidence: dict[str, object] = {
        "schema": "idt-generative-history-search/1", "config": config, "config_sha256": pipeline.digest(config),
        "source_sha256": before, "exact_source_archive": archive, "exact_source_archive_sha256": archive_sha,
        "screen_provenance": object_fields(results[0].report["request"])["provenance"],
        "candidates": rows, "operation_checks": operations, "kernel_selection": selection,
        "presentation_maps": presentations,
        "summary": {"candidate_count": len(rows), "source_group_count": len(specs),
                    "additional_kernel_hypotheses": 90, "kernel_reference_invariance_checks": 2520,
                    "domain_counts": {m: object_fields(v)["domain_count"] for m, v in operations.items()},
                    "source_proposal_statuses": [result.report["status"] for result in results]},
        "untested_leads": [{"cyclic_labels": 8, "kernel_a": ["sqrt(2)/2", "-sqrt(2)/2"],
                            "status": "untested_not_rejected_by_rational_grid"}],
        "candidate_verdict": "unchanged", "proof_status": "exploratory_finite_exact_not_formal_proof",
        "empirical_status": "not_tested", "archival": archival,
        "boundaries": ["cyclic_labels_disjoint_union_cartesian_composition_and_cancellation_are_supplied_primitives",
                       "readouts_are_candidate_rules_not_primitive_derived_Born",
                       "90_additional_kernel_hypotheses_are_conditional_on_pair_bilinearity_symmetry_K0_and_cancellation",
                       "I3_zero_expected_from_quadratic_ansatz_not_independent_physics_evidence",
                       "nonnegativity_check_only_on_input_bags_total_at_most_two",
                       "finite_exhaustive_inputs_never_universal_algebra_proof",
                       "serial_weight_multiplicativity_is_optional_diagnostic_not_a_physical_operation_axiom",
                       "arbitrary_state_transformations_need_not_be_algebra_homomorphisms",
                       "combinatorial_operations_not_necessarily_probability_operations",
                       "context_local_toy_histories_do_not_restore_global_history_ontology",
                       "physical_states_preparations_readout_normalization_admissible_operations_composites_continuum_not_derived",
                       "QM_SM_gravity_and_calibrated_constants_not_derived",
                       "existing_graph_history_scopes_and_registered_adapters_unchanged",
                       "all_27_variants_in_11_groups_retained_without_truth_ranking"]}
    return {**evidence, "report_sha256": pipeline.digest(evidence)}
