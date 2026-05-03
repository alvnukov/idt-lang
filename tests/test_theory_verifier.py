from __future__ import annotations

import unittest
from pathlib import Path

from theory_verifier.core import (
    ACTION_STANDARD_REQUIRED_GATES,
    ACTION_STANDARD_REQUIRED_SYMBOLS,
    ACTION_STANDARD_TARGET,
    CALIBRATED_QM_REQUIRED_SYMBOLS,
    CALIBRATED_QM_TARGET,
    BORN_READOUT_ROUTE_CONDITIONS,
    CLOCK_VACUUM_POLE_REQUIRED_SYMBOLS,
    CLOCK_VACUUM_POLE_TARGET,
    CONTINUUM_ACTION_FRONTIER_REQUIREMENTS,
    CROSS_UPDATE_CONTRACTION_SELECTION_REQUIRED_SYMBOLS,
    CROSS_UPDATE_CONTRACTION_SELECTION_TARGET,
    ELL0_EMERGENCE_CLEARANCE_REQUIRED_SYMBOLS,
    ELL0_EMERGENCE_CLEARANCE_TARGET,
    ELL0_CLOSURE_REQUIRED_GATES,
    ELL0_CLOSURE_REQUIRED_SYMBOLS,
    ELL0_CLOSURE_TARGET,
    ELL0_PHYSICAL_CANDIDATE_REQUIRED_SYMBOLS,
    ELL0_PHYSICAL_CANDIDATE_TARGET,
    FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS,
    HBAR_ACTION_STANDARD_REQUIRED_GATES,
    HBAR_ACTION_STANDARD_REQUIRED_SYMBOLS,
    HBAR_ACTION_STANDARD_TARGET,
    MEASUREMENT_FACTICITY_ROUTE_CONDITIONS,
    JOINT_ACTION_GRAVITY_ANCHOR_REQUIRED_SYMBOLS,
    JOINT_ACTION_GRAVITY_ANCHOR_TARGET,
    PRIMITIVE_TICK_REQUIRED_GATES,
    PRIMITIVE_TICK_REQUIRED_SYMBOLS,
    PRIMITIVE_TICK_TARGET,
    PRIMITIVE_MASS_ANCHOR_REQUIRED_SYMBOLS,
    PRIMITIVE_MASS_ANCHOR_TARGET,
    PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_REQUIRED_SYMBOLS,
    PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_TARGET,
    PRIMITIVE_TRANSITION_PHASE_REQUIRED_SYMBOLS,
    PRIMITIVE_TRANSITION_PHASE_TARGET,
    PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_REQUIRED_SYMBOLS,
    PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_TARGET,
    PRIMITIVE_WORK_REQUIRED_GATES,
    PRIMITIVE_WORK_REQUIRED_SYMBOLS,
    PRIMITIVE_WORK_TARGET,
    RESEARCH_GRAPH_CONTRACT_REQUIRED_SURFACES,
    NON_EXACT_HOLONOMY_SOURCE_REQUIRED_SYMBOLS,
    NON_EXACT_HOLONOMY_SOURCE_TARGET,
    RHO_CHI_PROTOCOL_REQUIRED_SYMBOLS,
    RHO_CHI_PROTOCOL_TARGET,
    SECTOR_ROLE_TAXONOMY_REQUIRED_SYMBOLS,
    SECTOR_ROLE_TAXONOMY_TARGET,
    SPECTRAL_PRIMITIVE_REDUCTION_REQUIRED_SYMBOLS,
    SPECTRAL_PRIMITIVE_REDUCTION_TARGET,
    SOURCE_RESPONSE_CHARGE_REQUIRED_GATES,
    SOURCE_RESPONSE_CHARGE_REQUIRED_SYMBOLS,
    SOURCE_RESPONSE_CHARGE_TARGET,
    GEOMETRY_RESPONSE_FACTOR_REQUIRED_SYMBOLS,
    GEOMETRY_RESPONSE_FACTOR_TARGET,
    TENSOR_COMPOSITION_ROUTE_CONDITIONS,
    CLOCK_VACUUM_STIFFNESS_REQUIRED_GATES,
    CLOCK_VACUUM_STIFFNESS_REQUIRED_SYMBOLS,
    CLOCK_VACUUM_STIFFNESS_TARGET,
    G_EMERGENCE_CLEARANCE_REQUIRED_SYMBOLS,
    G_EMERGENCE_CLEARANCE_TARGET,
    FIRST_PRINCIPLES_G_CANDIDATE_REQUIRED_SYMBOLS,
    FIRST_PRINCIPLES_G_CANDIDATE_TARGET,
    FIXED_POINT_STEP_INVARIANT_REQUIRED_SYMBOLS,
    FIXED_POINT_STEP_INVARIANT_TARGET,
    KAPPA_OMEGA_CONSISTENCY_REQUIRED_SYMBOLS,
    KAPPA_OMEGA_CONSISTENCY_TARGET,
    NON_GRAVITY_LINK_BOUND_REQUIRED_SYMBOLS,
    NON_GRAVITY_LINK_BOUND_TARGET,
    WEAK_FIELD_CLOCK_REQUIRED_SYMBOLS,
    WEAK_FIELD_CLOCK_TARGET,
    SOURCE_LAW_VARIATIONAL_REQUIRED_SYMBOLS,
    SOURCE_LAW_VARIATIONAL_TARGET,
    PPN_NO_SLIP_REQUIRED_SYMBOLS,
    PPN_NO_SLIP_TARGET,
    NO_SLIP_STRESS_REQUIRED_SYMBOLS,
    NO_SLIP_STRESS_TARGET,
    SOURCE_STRESS_PACKET_REQUIRED_SYMBOLS,
    SOURCE_STRESS_PACKET_TARGET,
    SCALE_RESIDUAL_POLICY_REQUIRED_SYMBOLS,
    SCALE_RESIDUAL_POLICY_TARGET,
    SCREENED_SLIP_RESIDUAL_REQUIRED_SYMBOLS,
    SCREENED_SLIP_RESIDUAL_TARGET,
    SCREENED_OBSERVATIONAL_GATE_REQUIRED_SYMBOLS,
    SCREENED_OBSERVATIONAL_GATE_TARGET,
    CARRIER_SELECTION_OPEN_OBSTRUCTIONS,
    CONTEXT_PRODUCT_EXHAUSTION_PRIMITIVES,
    DISTINGUISHABILITY_GEOMETRY_REQUIREMENTS,
    GENERIC_GPT_CLOSURE_CONDITIONS,
    GPT_SEPARATOR_PRINCIPLES,
    IDT_BOUNDED_CORRELATION_CONDITIONS,
    IDT_PURIFICATION_FILTERING_CONDITIONS,
    IDT_LOCAL_TOMOGRAPHY_CONDITIONS,
    NONCOMPLEX_JORDAN_SEPARATOR_CONDITIONS,
    QM_CORE_PROOF_REQUIRED_OBLIGATIONS,
    QM_CORE_RECOMPILE_REQUIRED_ROUTES,
    QM_EXPERIMENT_REQUIRED_PRIMITIVES,
    QM_UNIVERSAL_PATTERN_REQUIRED_OPERATIONS,
    QM_APPARATUS_FACTICITY_REQUIRED_GATES,
    QM_APPARATUS_FACTICITY_REQUIRED_SYMBOLS,
    QM_APPARATUS_FACTICITY_TARGET,
    QM_CONTINUUM_LIMIT_REQUIRED_GATES,
    QM_CONTINUUM_LIMIT_REQUIRED_SYMBOLS,
    QM_CONTINUUM_LIMIT_TARGET,
    QM_FOUNDATION_REQUIRED_SYMBOLS,
    QM_GENERATOR_TRANSLATION_REQUIRED_GATES,
    QM_GENERATOR_TRANSLATION_REQUIRED_SYMBOLS,
    QM_GENERATOR_TRANSLATION_TARGET,
    QM_SINGLE_PASS_REQUIRED_SYMBOLS,
    QM_SINGLE_PASS_TARGET,
    Manifest,
    VerificationReport,
    load_manifest,
    parse_manifest,
    verify_manifest,
)
from theory_verifier.qm_bench import compile_qm_bench


ROOT = Path(__file__).resolve().parents[1]


class TheoryVerifierTests(unittest.TestCase):
    def test_current_manifest_passes_logic_checks(self) -> None:
        manifest_path = ROOT / "theory_verifier_manifest_v6_0.json"
        manifest = parse_manifest_text(manifest_path)
        report = verify_manifest(manifest)
        self.assertEqual([], list(report.issues))

    def test_current_manifest_compiles_qm_bench(self) -> None:
        manifest_path = ROOT / "theory_verifier_manifest_v6_0.json"
        manifest = parse_manifest_text(manifest_path)
        bench = compile_qm_bench(manifest)
        self.assertEqual(6, len(bench.kernels))
        self.assertEqual(35, bench.experiment_count)
        self.assertEqual(35, bench.finite_gate_reference_count)
        self.assertEqual(QM_UNIVERSAL_PATTERN_REQUIRED_OPERATIONS, bench.shared_operations)

    def test_dimension_mismatch_is_reported(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {
                    "energy": {"status": "target", "dimension": {"M": 1, "L": 2, "T": -2}},
                    "time": {"status": "primitive", "dimension": {"T": 1}},
                },
                "equations": [{"id": "bad", "lhs": "energy", "rhs": {"symbol": "time"}}],
                "derivations": [],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"dimension_mismatch"})

    def test_derived_claim_cannot_depend_on_open_symbol(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {
                    "target": {"status": "target", "dimension": {}},
                    "missing": {"status": "open", "dimension": {}},
                },
                "equations": [],
                "derivations": [
                    {
                        "id": "bad_derived",
                        "target": "target",
                        "status": "derived",
                        "depends_on": ["missing"],
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"underived_dependency"})

    def test_qm_foundation_spine_requires_declared_nodes(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {"full_QM_I": {"status": "target", "dimension": {}}},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_foundation_spine_incomplete"})

    def test_qm_foundation_spine_requires_explicit_derivation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_foundation_symbols(),
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_foundation_spine_missing_derivation"})

    def test_qm_foundation_spine_requires_complete_derivation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_foundation_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "incomplete_full_qm",
                        "target": "full_QM_I",
                        "status": "target",
                        "depends_on": list(QM_FOUNDATION_REQUIRED_SYMBOLS[:-1]),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_foundation_spine_incomplete"})

    def test_qm_foundation_spine_rejects_premature_full_qm_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_foundation_symbols(
                    {
                        "full_QM_I": "derived",
                        "complex_amplitude_packet_I": "derived_conditional",
                        "hbar_I": "blocked",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "premature_full_qm",
                        "target": "full_QM_I",
                        "status": "target",
                        "depends_on": list(QM_FOUNDATION_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_full_claim_premature"})

    def test_qm_single_pass_closure_requires_explicit_derivation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_single_pass_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "numeric_hbar_route",
                        "target": "hbar_I",
                        "status": "blocked",
                        "depends_on": ["A0_I", "bar_C_gamma", "theta_gamma"],
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_single_pass_closure_missing_derivation"})

    def test_calibrated_qm_reconstruction_requires_explicit_derivation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": calibrated_qm_symbols(),
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"calibrated_qm_reconstruction_missing_derivation"})

    def test_calibrated_qm_reconstruction_rejects_premature_derived_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": calibrated_qm_symbols(
                    {
                        CALIBRATED_QM_TARGET: "derived",
                        "calibrated_qm_continuum_closure_I": "target",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "calibrated_qm",
                        "target": CALIBRATED_QM_TARGET,
                        "status": "target",
                        "depends_on": list(CALIBRATED_QM_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"calibrated_qm_reconstruction_premature"})

    def test_qm_single_pass_closure_requires_complete_derivation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_single_pass_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "numeric_hbar_route",
                        "target": "hbar_I",
                        "status": "blocked",
                        "depends_on": ["A0_I", "bar_C_gamma", "theta_gamma"],
                    },
                    {
                        "id": "incomplete_single_pass",
                        "target": QM_SINGLE_PASS_TARGET,
                        "status": "target",
                        "depends_on": list(QM_SINGLE_PASS_REQUIRED_SYMBOLS[:-1]),
                    },
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_single_pass_closure_incomplete"})

    def test_qm_single_pass_closure_rejects_premature_derived_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_single_pass_symbols(
                    {QM_SINGLE_PASS_TARGET: "derived", "hbar_I": "blocked", "A0_I": "open"}
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "numeric_hbar_route",
                        "target": "hbar_I",
                        "status": "blocked",
                        "depends_on": ["A0_I", "bar_C_gamma", "theta_gamma"],
                    },
                    {
                        "id": "premature_single_pass",
                        "target": QM_SINGLE_PASS_TARGET,
                        "status": "target",
                        "depends_on": list(QM_SINGLE_PASS_REQUIRED_SYMBOLS),
                    },
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_single_pass_closure_premature"})

    def test_hbar_action_route_requires_independent_action_inputs(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_single_pass_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "bad_hbar_route",
                        "target": "hbar_I",
                        "status": "blocked",
                        "depends_on": ["A0_I", "bar_C_gamma"],
                    },
                    {
                        "id": "single_pass",
                        "target": QM_SINGLE_PASS_TARGET,
                        "status": "target",
                        "depends_on": list(QM_SINGLE_PASS_REQUIRED_SYMBOLS),
                    },
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"hbar_action_route_incomplete"})

    def test_hbar_action_route_rejects_conditional_claim_without_action_standard(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_single_pass_symbols({"hbar_I": "derived_conditional", "A0_I": "open"}),
                "equations": [],
                "derivations": [
                    {
                        "id": "numeric_hbar_route",
                        "target": "hbar_I",
                        "status": "derived_conditional",
                        "depends_on": ["A0_I", "bar_C_gamma", "theta_gamma"],
                    },
                    {
                        "id": "single_pass",
                        "target": QM_SINGLE_PASS_TARGET,
                        "status": "target",
                        "depends_on": list(QM_SINGLE_PASS_REQUIRED_SYMBOLS),
                    },
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"hbar_action_scale_premature"})

    def test_qm_experiment_executable_requires_existing_gate(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "finite_gates": [],
                "qm_experiments": [
                    qm_experiment(
                        status="executable_gate",
                        finite_gates=["missing_gate"],
                    )
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_experiment_gate_missing"})

    def test_qm_experiment_executable_rejects_empty_gate_list(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "finite_gates": [],
                "qm_experiments": [
                    qm_experiment(
                        status="executable_gate",
                        finite_gates=[],
                    )
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_experiment_executable_without_gate"})

    def test_qm_experiment_requires_complete_idt_primitives(self) -> None:
        primitives = qm_experiment_primitives()
        del primitives["facticity"]
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "finite_gates": [],
                "qm_experiments": [qm_experiment(idt_primitives=primitives)],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_experiment_primitives_incomplete"})

    def test_qm_experiment_gate_candidate_requires_proposed_gate(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "finite_gates": [],
                "qm_experiments": [
                    qm_experiment(
                        status="gate_candidate",
                        proposed_gates=[],
                    )
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_experiment_candidate_without_proposed_gate"})

    def test_large_qm_ledger_requires_universal_patterns(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "finite_gates": [],
                "qm_experiments": [qm_experiment(identifier=f"experiment_{index}") for index in range(10)],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_universal_patterns_missing"})

    def test_qm_universal_patterns_require_complete_operations(self) -> None:
        operations = qm_universal_pattern_operations()
        del operations["facticity_rule"]
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "finite_gates": [],
                "qm_experiments": [qm_experiment(identifier="experiment_a")],
                "qm_universal_patterns": [
                    qm_universal_pattern(
                        experiments=["experiment_a"],
                        operations=operations,
                    )
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_universal_pattern_operations_incomplete"})

    def test_qm_universal_patterns_cover_experiments_once(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "finite_gates": [],
                "qm_experiments": [
                    qm_experiment(identifier="experiment_a"),
                    qm_experiment(identifier="experiment_b"),
                ],
                "qm_universal_patterns": [
                    qm_universal_pattern(
                        experiments=["experiment_a"],
                    )
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_universal_pattern_experiment_uncovered"})

    def test_large_qm_ledger_requires_core_proof_obligations(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "finite_gates": [],
                "qm_experiments": [qm_experiment(identifier=f"experiment_{index}") for index in range(10)],
                "qm_universal_patterns": [qm_universal_pattern(experiments=[f"experiment_{index}" for index in range(10)])],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_core_proof_obligations_missing"})

    def test_qm_core_proof_obligations_require_complete_required_set(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "finite_gates": [],
                "qm_experiments": [qm_experiment(identifier="experiment_a")],
                "qm_universal_patterns": [qm_universal_pattern(experiments=["experiment_a"])],
                "qm_core_proof_obligations": [qm_core_proof_obligation(identifier="finite_operational_core")],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_core_proof_obligations_incomplete"})

    def test_full_qm_derived_requires_closed_core_proof_obligations(self) -> None:
        obligations = [
            qm_core_proof_obligation(identifier=identifier, status="derived")
            for identifier in QM_CORE_PROOF_REQUIRED_OBLIGATIONS
        ]
        obligations[-1]["status"] = "blocked"
        manifest = parse_manifest(
            {
                "symbols": {
                    "full_QM_I": {"status": "derived", "dimension": {}},
                },
                "equations": [],
                "derivations": [],
                "finite_gates": [],
                "qm_core_proof_obligations": obligations,
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"full_qm_core_proof_incomplete"})

    def test_joint_action_gravity_anchor_requires_explicit_derivation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": joint_action_gravity_anchor_symbols(),
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"joint_action_gravity_anchor_missing_derivation"})

    def test_joint_action_gravity_anchor_rejects_premature_conditional_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": joint_action_gravity_anchor_symbols(
                    {
                        JOINT_ACTION_GRAVITY_ANCHOR_TARGET: "derived_conditional",
                        SOURCE_RESPONSE_CHARGE_TARGET: "target",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "joint_anchor_route",
                        "target": JOINT_ACTION_GRAVITY_ANCHOR_TARGET,
                        "status": "target",
                        "depends_on": list(JOINT_ACTION_GRAVITY_ANCHOR_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"joint_action_gravity_anchor_premature"})

    def test_ell0_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": ell0_closure_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "ell0_route",
                        "target": ELL0_CLOSURE_TARGET,
                        "status": "target",
                        "depends_on": list(ELL0_CLOSURE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ell0_closure_gate_missing"})

    def test_ell0_closure_rejects_premature_conditional_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": ell0_closure_symbols(
                    {
                        ELL0_CLOSURE_TARGET: "derived_conditional",
                        ELL0_PHYSICAL_CANDIDATE_TARGET: "target",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "ell0_route",
                        "target": ELL0_CLOSURE_TARGET,
                        "status": "target",
                        "depends_on": list(ELL0_CLOSURE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in ELL0_CLOSURE_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ell0_closure_premature"})

    def test_clock_vacuum_pole_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": clock_vacuum_pole_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "clock_vacuum_pole_route",
                        "target": CLOCK_VACUUM_POLE_TARGET,
                        "status": "target",
                        "depends_on": list(CLOCK_VACUUM_POLE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"clock_vacuum_pole_closure_gate_missing"})

    def test_spectral_primitive_reduction_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": spectral_primitive_reduction_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "spectral_reduction_route",
                        "target": SPECTRAL_PRIMITIVE_REDUCTION_TARGET,
                        "status": "target",
                        "depends_on": list(SPECTRAL_PRIMITIVE_REDUCTION_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"spectral_primitive_reduction_gate_missing"})

    def test_spectral_primitive_reduction_rejects_premature_conditional_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": spectral_primitive_reduction_symbols(
                    {
                        SPECTRAL_PRIMITIVE_REDUCTION_TARGET: "derived_conditional",
                        "primitive_transition_phase_readout_I": "target",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "spectral_reduction_route",
                        "target": SPECTRAL_PRIMITIVE_REDUCTION_TARGET,
                        "status": "target",
                        "depends_on": list(SPECTRAL_PRIMITIVE_REDUCTION_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": "spectral_law_free_parameter_audit_demo", "type": "psd_matrix", "matrix": [[1.0]]},
                    {"id": "spectral_law_no_calibrated_input_demo", "type": "psd_matrix", "matrix": [[1.0]]},
                    {"id": "fixed_point_component_status_demo", "type": "psd_matrix", "matrix": [[1.0]]},
                    {"id": "non_exact_holonomy_source_demo", "type": "psd_matrix", "matrix": [[1.0]]},
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"spectral_primitive_reduction_premature"})

    def test_cross_update_contraction_selection_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": cross_update_contraction_selection_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "contraction_selection_route",
                        "target": CROSS_UPDATE_CONTRACTION_SELECTION_TARGET,
                        "status": "target",
                        "depends_on": list(CROSS_UPDATE_CONTRACTION_SELECTION_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"cross_update_contraction_selection_gate_missing"})

    def test_fixed_point_step_invariant_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": fixed_point_step_invariant_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "fixed_point_step_route",
                        "target": FIXED_POINT_STEP_INVARIANT_TARGET,
                        "status": "target",
                        "depends_on": list(FIXED_POINT_STEP_INVARIANT_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"fixed_point_step_invariant_gate_missing"})

    def test_primitive_transition_phase_readout_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": primitive_transition_phase_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "transition_phase_route",
                        "target": PRIMITIVE_TRANSITION_PHASE_TARGET,
                        "status": "target",
                        "depends_on": list(PRIMITIVE_TRANSITION_PHASE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_transition_phase_readout_gate_missing"})

    def test_non_exact_holonomy_source_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": non_exact_holonomy_source_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "non_exact_holonomy_route",
                        "target": NON_EXACT_HOLONOMY_SOURCE_TARGET,
                        "status": "target",
                        "depends_on": list(NON_EXACT_HOLONOMY_SOURCE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"non_exact_holonomy_source_closure_gate_missing"})

    def test_primitive_holonomy_source_selector_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": primitive_holonomy_source_selector_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "holonomy_selector_route",
                        "target": PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_TARGET,
                        "status": "target",
                        "depends_on": list(PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_holonomy_source_selector_gate_missing"})

    def test_primitive_topology_winding_selector_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": primitive_topology_winding_selector_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "winding_selector_route",
                        "target": PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_TARGET,
                        "status": "target",
                        "depends_on": list(PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_topology_winding_selector_gate_missing"})

    def test_sector_role_taxonomy_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": sector_role_taxonomy_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "sector_role_taxonomy_route",
                        "target": SECTOR_ROLE_TAXONOMY_TARGET,
                        "status": "target",
                        "depends_on": list(SECTOR_ROLE_TAXONOMY_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"sector_role_taxonomy_gate_missing"})

    def test_ell0_emergence_clearance_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": ell0_emergence_clearance_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "ell0_clearance_route",
                        "target": ELL0_EMERGENCE_CLEARANCE_TARGET,
                        "status": "target",
                        "depends_on": list(ELL0_EMERGENCE_CLEARANCE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ell0_emergence_clearance_gate_missing"})

    def test_ell0_physical_candidate_rejects_premature_conditional_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": ell0_physical_candidate_symbols(
                    {
                        ELL0_PHYSICAL_CANDIDATE_TARGET: "derived_conditional",
                        ELL0_EMERGENCE_CLEARANCE_TARGET: "target",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "ell0_candidate_route",
                        "target": ELL0_PHYSICAL_CANDIDATE_TARGET,
                        "status": "target",
                        "depends_on": list(ELL0_PHYSICAL_CANDIDATE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ell0_physical_candidate_premature"})

    def test_ell0_derived_claim_requires_clearance(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": ell0_physical_candidate_symbols({"ell0": "derived"}),
                "equations": [],
                "derivations": [
                    {
                        "id": "ell0_candidate_route",
                        "target": ELL0_PHYSICAL_CANDIDATE_TARGET,
                        "status": "target",
                        "depends_on": list(ELL0_PHYSICAL_CANDIDATE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ell0_derived_without_clearance"})

    def test_mass_anchor_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": mass_anchor_closure_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "mass_anchor_route",
                        "target": PRIMITIVE_MASS_ANCHOR_TARGET,
                        "status": "target",
                        "depends_on": list(PRIMITIVE_MASS_ANCHOR_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_mass_anchor_closure_gate_missing"})

    def test_rho_chi_protocol_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": rho_chi_protocol_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "rho_chi_route",
                        "target": RHO_CHI_PROTOCOL_TARGET,
                        "status": "target",
                        "depends_on": list(RHO_CHI_PROTOCOL_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"rho_chi_protocol_closure_gate_missing"})

    def test_kappa_omega_consistency_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": kappa_omega_consistency_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "kappa_omega_route",
                        "target": KAPPA_OMEGA_CONSISTENCY_TARGET,
                        "status": "target",
                        "depends_on": list(KAPPA_OMEGA_CONSISTENCY_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"kappa_omega_consistency_closure_gate_missing"})

    def test_source_response_charge_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": source_response_charge_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "source_response_charge_route",
                        "target": SOURCE_RESPONSE_CHARGE_TARGET,
                        "status": "target",
                        "depends_on": list(SOURCE_RESPONSE_CHARGE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"source_response_charge_gate_missing"})

    def test_source_response_charge_closure_rejects_premature_conditional_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": source_response_charge_symbols(
                    {
                        SOURCE_RESPONSE_CHARGE_TARGET: "derived_conditional",
                        "source_response_charge_I": "open",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "source_response_charge_route",
                        "target": SOURCE_RESPONSE_CHARGE_TARGET,
                        "status": "target",
                        "depends_on": list(SOURCE_RESPONSE_CHARGE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in SOURCE_RESPONSE_CHARGE_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"source_response_charge_closure_premature"})

    def test_geometry_response_factor_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": geometry_response_factor_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "geometry_response_route",
                        "target": GEOMETRY_RESPONSE_FACTOR_TARGET,
                        "status": "target",
                        "depends_on": list(GEOMETRY_RESPONSE_FACTOR_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"geometry_response_factor_closure_gate_missing"})

    def test_clock_vacuum_stiffness_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": clock_vacuum_stiffness_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "clock_vacuum_stiffness_route",
                        "target": CLOCK_VACUUM_STIFFNESS_TARGET,
                        "status": "target",
                        "depends_on": list(CLOCK_VACUUM_STIFFNESS_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"clock_vacuum_stiffness_closure_gate_missing"})

    def test_clock_vacuum_stiffness_closure_rejects_premature_conditional_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": clock_vacuum_stiffness_symbols(
                    {
                        CLOCK_VACUUM_STIFFNESS_TARGET: "derived_conditional",
                        "kappa_chi_I": "open",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "clock_vacuum_stiffness_route",
                        "target": CLOCK_VACUUM_STIFFNESS_TARGET,
                        "status": "target",
                        "depends_on": list(CLOCK_VACUUM_STIFFNESS_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in CLOCK_VACUUM_STIFFNESS_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"clock_vacuum_stiffness_closure_premature"})

    def test_G_emergence_clearance_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": G_emergence_clearance_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "G_clearance_route",
                        "target": G_EMERGENCE_CLEARANCE_TARGET,
                        "status": "target",
                        "depends_on": list(G_EMERGENCE_CLEARANCE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"G_emergence_clearance_gate_missing"})

    def test_first_principles_G_candidate_rejects_premature_conditional_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": first_principles_G_candidate_symbols(
                    {
                        FIRST_PRINCIPLES_G_CANDIDATE_TARGET: "derived_conditional",
                        G_EMERGENCE_CLEARANCE_TARGET: "target",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "G_candidate_route",
                        "target": FIRST_PRINCIPLES_G_CANDIDATE_TARGET,
                        "status": "target",
                        "depends_on": list(FIRST_PRINCIPLES_G_CANDIDATE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"first_principles_G_candidate_premature"})

    def test_G_I_derived_claim_requires_clearance(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": first_principles_G_candidate_symbols({"G_I": "derived"}),
                "equations": [],
                "derivations": [
                    {
                        "id": "G_candidate_route",
                        "target": FIRST_PRINCIPLES_G_CANDIDATE_TARGET,
                        "status": "target",
                        "depends_on": list(FIRST_PRINCIPLES_G_CANDIDATE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"G_derived_without_clearance"})

    def test_non_gravity_link_bound_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": non_gravity_link_bound_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "omega_bound_route",
                        "target": NON_GRAVITY_LINK_BOUND_TARGET,
                        "status": "derived_conditional",
                        "depends_on": list(NON_GRAVITY_LINK_BOUND_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"non_gravity_link_bound_gate_missing"})

    def test_weak_field_clock_calculator_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": weak_field_clock_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "weak_field_clock_route",
                        "target": WEAK_FIELD_CLOCK_TARGET,
                        "status": "derived_conditional",
                        "depends_on": list(WEAK_FIELD_CLOCK_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"weak_field_clock_gate_missing"})

    def test_source_law_variational_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": source_law_variational_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "source_law_variational_route",
                        "target": SOURCE_LAW_VARIATIONAL_TARGET,
                        "status": "derived_conditional",
                        "depends_on": list(SOURCE_LAW_VARIATIONAL_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"source_law_variational_gate_missing"})

    def test_ppn_no_slip_validation_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": ppn_no_slip_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "ppn_no_slip_route",
                        "target": PPN_NO_SLIP_TARGET,
                        "status": "derived_conditional",
                        "depends_on": list(PPN_NO_SLIP_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ppn_no_slip_gate_missing"})

    def test_no_slip_stress_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": no_slip_stress_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "no_slip_stress_route",
                        "target": NO_SLIP_STRESS_TARGET,
                        "status": "derived_conditional",
                        "depends_on": list(NO_SLIP_STRESS_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"no_slip_stress_gate_missing"})

    def test_source_stress_packet_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": source_stress_packet_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "source_stress_packet_route",
                        "target": SOURCE_STRESS_PACKET_TARGET,
                        "status": "derived_conditional",
                        "depends_on": list(SOURCE_STRESS_PACKET_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"source_stress_packet_gate_missing"})

    def test_scale_residual_policy_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": scale_residual_policy_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "scale_residual_policy_route",
                        "target": SCALE_RESIDUAL_POLICY_TARGET,
                        "status": "derived_conditional",
                        "depends_on": list(SCALE_RESIDUAL_POLICY_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"scale_residual_policy_gate_missing"})

    def test_screened_slip_residual_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": screened_slip_residual_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "screened_slip_residual_route",
                        "target": SCREENED_SLIP_RESIDUAL_TARGET,
                        "status": "derived_conditional",
                        "depends_on": list(SCREENED_SLIP_RESIDUAL_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_slip_residual_gate_missing"})

    def test_screened_observational_gate_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": screened_observational_gate_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "screened_observational_route",
                        "target": SCREENED_OBSERVATIONAL_GATE_TARGET,
                        "status": "derived_conditional",
                        "depends_on": list(SCREENED_OBSERVATIONAL_GATE_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_observational_gate_missing"})

    def test_primitive_tick_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": primitive_tick_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "primitive_tick_route",
                        "target": PRIMITIVE_TICK_TARGET,
                        "status": "target",
                        "depends_on": list(PRIMITIVE_TICK_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_tick_gate_missing"})

    def test_primitive_tick_closure_rejects_premature_derived_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": primitive_tick_symbols(
                    {PRIMITIVE_TICK_TARGET: "derived", "primitive_tick_I": "open"}
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "primitive_tick_route",
                        "target": PRIMITIVE_TICK_TARGET,
                        "status": "target",
                        "depends_on": list(PRIMITIVE_TICK_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in PRIMITIVE_TICK_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_tick_closure_premature"})

    def test_primitive_tick_closure_rejects_open_ell0_closure(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": primitive_tick_symbols(
                    {"primitive_tick_closure_I": "derived", "ell0_closure_I": "target"}
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "primitive_tick_route",
                        "target": PRIMITIVE_TICK_TARGET,
                        "status": "target",
                        "depends_on": list(PRIMITIVE_TICK_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in PRIMITIVE_TICK_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_tick_closure_premature"})

    def test_primitive_work_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": primitive_work_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "primitive_work_route",
                        "target": PRIMITIVE_WORK_TARGET,
                        "status": "target",
                        "depends_on": list(PRIMITIVE_WORK_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_work_gate_missing"})

    def test_primitive_work_closure_rejects_premature_derived_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": primitive_work_symbols(
                    {PRIMITIVE_WORK_TARGET: "derived", "primitive_work_unit_I": "open"}
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "primitive_work_route",
                        "target": PRIMITIVE_WORK_TARGET,
                        "status": "target",
                        "depends_on": list(PRIMITIVE_WORK_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in PRIMITIVE_WORK_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_work_closure_premature"})

    def test_primitive_work_closure_rejects_open_mass_anchor_closure(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": primitive_work_symbols(
                    {
                        "primitive_work_unit_closure_I": "derived",
                        "primitive_mass_anchor_closure_I": "target",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "primitive_work_route",
                        "target": PRIMITIVE_WORK_TARGET,
                        "status": "target",
                        "depends_on": list(PRIMITIVE_WORK_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in PRIMITIVE_WORK_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_work_closure_premature"})

    def test_action_standard_work_time_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": action_standard_work_time_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "action_standard_work_time",
                        "target": ACTION_STANDARD_TARGET,
                        "status": "target",
                        "depends_on": list(ACTION_STANDARD_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"action_standard_work_time_gate_missing"})

    def test_action_standard_work_time_rejects_premature_A0_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": action_standard_work_time_symbols(
                    {
                        "A0_I": "derived_conditional",
                        "primitive_work_unit_I": "open",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "action_standard_work_time",
                        "target": ACTION_STANDARD_TARGET,
                        "status": "target",
                        "depends_on": list(ACTION_STANDARD_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in ACTION_STANDARD_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"action_standard_work_time_premature"})

    def test_hbar_action_standard_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": hbar_action_standard_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "hbar_action_standard",
                        "target": HBAR_ACTION_STANDARD_TARGET,
                        "status": "target",
                        "depends_on": list(HBAR_ACTION_STANDARD_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"hbar_action_standard_gate_missing"})

    def test_hbar_action_standard_closure_rejects_premature_derived_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": hbar_action_standard_symbols(
                    {
                        HBAR_ACTION_STANDARD_TARGET: "derived",
                        "A0_I": "open",
                        "hbar_I": "blocked",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "hbar_action_standard",
                        "target": HBAR_ACTION_STANDARD_TARGET,
                        "status": "target",
                        "depends_on": list(HBAR_ACTION_STANDARD_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in HBAR_ACTION_STANDARD_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"hbar_action_standard_closure_premature"})

    def test_qm_generator_translation_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_generator_translation_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "generator_translation",
                        "target": QM_GENERATOR_TRANSLATION_TARGET,
                        "status": "target",
                        "depends_on": list(QM_GENERATOR_TRANSLATION_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_generator_translation_gate_missing"})

    def test_qm_generator_translation_closure_rejects_premature_derived_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_generator_translation_symbols(
                    {
                        QM_GENERATOR_TRANSLATION_TARGET: "derived",
                        "hbar_I": "blocked",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "generator_translation",
                        "target": QM_GENERATOR_TRANSLATION_TARGET,
                        "status": "target",
                        "depends_on": list(QM_GENERATOR_TRANSLATION_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in QM_GENERATOR_TRANSLATION_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_generator_translation_closure_premature"})

    def test_qm_continuum_limit_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_continuum_limit_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "continuum_limit",
                        "target": QM_CONTINUUM_LIMIT_TARGET,
                        "status": "target",
                        "depends_on": list(QM_CONTINUUM_LIMIT_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_continuum_limit_gate_missing"})

    def test_qm_continuum_limit_closure_rejects_premature_derived_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_continuum_limit_symbols(
                    {
                        QM_CONTINUUM_LIMIT_TARGET: "derived",
                        "continuum_limit_I": "derived_conditional",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "continuum_limit",
                        "target": QM_CONTINUUM_LIMIT_TARGET,
                        "status": "target",
                        "depends_on": list(QM_CONTINUUM_LIMIT_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in QM_CONTINUUM_LIMIT_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_continuum_limit_closure_premature"})

    def test_qm_apparatus_facticity_closure_requires_finite_gates(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_apparatus_facticity_symbols(),
                "equations": [],
                "derivations": [
                    {
                        "id": "apparatus_facticity",
                        "target": QM_APPARATUS_FACTICITY_TARGET,
                        "status": "target",
                        "depends_on": list(QM_APPARATUS_FACTICITY_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_apparatus_facticity_gate_missing"})

    def test_qm_apparatus_facticity_closure_rejects_premature_derived_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": qm_apparatus_facticity_symbols(
                    {
                        QM_APPARATUS_FACTICITY_TARGET: "derived",
                        "measurement_facticity_I": "derived_conditional",
                    }
                ),
                "equations": [],
                "derivations": [
                    {
                        "id": "apparatus_facticity",
                        "target": QM_APPARATUS_FACTICITY_TARGET,
                        "status": "target",
                        "depends_on": list(QM_APPARATUS_FACTICITY_REQUIRED_SYMBOLS),
                    }
                ],
                "forbidden_paths": [],
                "finite_gates": [
                    {"id": gate_id, "type": "psd_matrix", "matrix": [[1.0]]}
                    for gate_id in QM_APPARATUS_FACTICITY_REQUIRED_GATES
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_apparatus_facticity_closure_premature"})

    def test_forbidden_path_is_reported_transitively(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {
                    "hbar_I": {"status": "target", "dimension": {}},
                    "middle": {"status": "definition", "dimension": {}},
                    "G_N": {"status": "experimental_gate", "dimension": {}},
                },
                "equations": [],
                "derivations": [
                    {
                        "id": "bad_hbar",
                        "target": "hbar_I",
                        "status": "formula",
                        "depends_on": ["middle"],
                    },
                    {
                        "id": "bad_middle",
                        "target": "middle",
                        "status": "formula",
                        "depends_on": ["G_N"],
                    },
                ],
                "forbidden_paths": [{"target": "hbar_I", "sources": ["G_N"]}],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"forbidden_input_path"})

    def test_dependency_cycle_is_reported(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {
                    "a": {"status": "definition", "dimension": {}},
                    "b": {"status": "definition", "dimension": {}},
                },
                "equations": [],
                "derivations": [
                    {"id": "a_from_b", "target": "a", "status": "formula", "depends_on": ["b"]},
                    {"id": "b_from_a", "target": "b", "status": "formula", "depends_on": ["a"]},
                ],
                "forbidden_paths": [],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"dependency_cycle"})

    def test_non_psd_finite_gate_is_reported(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_psd",
                        "type": "psd_matrix",
                        "matrix": [[1.0, 2.0], [2.0, 1.0]],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"matrix_not_psd"})

    def test_non_hermitian_finite_gate_is_reported(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_hermitian",
                        "type": "psd_matrix",
                        "matrix": [[1.0, 0.2], [0.3, 1.0]],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"matrix_not_hermitian"})

    def test_invalid_holonomy_cycle_is_reported(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_cycle",
                        "type": "cycle_holonomy_gauge_invariance",
                        "edges": [{"from": "a", "to": "b", "phase": 0.1}],
                        "cycle": ["a", "b", "a"],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_non_contraction_is_reported(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_contraction",
                        "type": "contraction",
                        "matrix": [[1.2, 0.0], [0.0, 1.0]],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"not_contraction"})

    def test_unexpected_exact_holonomy_is_reported(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_exact",
                        "type": "cycle_holonomy_class",
                        "edges": [
                            {"from": "a", "to": "b", "phase": 0.2},
                            {"from": "b", "to": "a", "phase": -0.2},
                        ],
                        "cycle": ["a", "b", "a"],
                        "expected": "non_exact",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"unexpected_exact_holonomy"})

    def test_schur_rejects_non_psd_input(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_schur",
                        "type": "schur_psd",
                        "left": [[1.0, 2.0], [2.0, 1.0]],
                        "right": [[1.0, 0.0], [0.0, 1.0]],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"schur_input_not_psd"})

    def test_i3_gate_requires_pairwise_disjoint_events(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_i3",
                        "type": "actualization_i3_zero",
                        "weights": [1.0, 1.0],
                        "gamma": [[1.0, 0.0], [0.0, 1.0]],
                        "events": {"A": [0], "B": [0], "C": [1]},
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_two_path_interference_rejects_bad_expected_probability(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_two_path_fringe",
                        "type": "two_path_interference_fringe",
                        "weights": [0.7071067811865476, 0.7071067811865476],
                        "gamma": [[1.0, 0.8], [0.8, 1.0]],
                        "expected_visibility": 0.8,
                        "samples": [{"phase": 0.0, "expected_probability": 0.8}],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"fringe_probability_mismatch"})

    def test_two_path_interference_rejects_non_psd_kernel(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_two_path_kernel",
                        "type": "two_path_interference_fringe",
                        "weights": [0.7071067811865476, 0.7071067811865476],
                        "gamma": [[1.0, 2.0], [2.0, 1.0]],
                        "samples": [{"phase": 0.0, "expected_probability": 1.0}],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"fringe_kernel_not_psd"})

    def test_born_context_probability_table_rejects_bad_probability(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_born_table",
                        "type": "born_context_probability_table",
                        "delta": 0.0,
                        "weights": [0.4472135954999579, 0.5477225575051661],
                        "gamma": [[1.0, 0.0], [0.0, 1.0]],
                        "events": [[0], [1]],
                        "expected_probabilities": [0.5, 0.5],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"born_probability_mismatch"})

    def test_born_quadratic_readout_route_rejects_bad_linear_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_born_route",
                        "type": "born_quadratic_readout_route",
                        "tolerance": 1.0e-10,
                        "conditions": list(BORN_READOUT_ROUTE_CONDITIONS),
                        "samples": [
                            {
                                "id": "two_branch_packet",
                                "amplitudes": [0.6, 0.8],
                                "expected_probabilities": [0.36, 0.64],
                                "candidate_readouts": [
                                    {
                                        "id": "quadratic",
                                        "type": "quadratic_modulus",
                                        "expected_status": "survives",
                                    },
                                    {
                                        "id": "linear",
                                        "type": "linear_modulus",
                                        "expected_status": "survives",
                                    },
                                ],
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"born_quadratic_route_candidate_status_mismatch"})

    def test_unitary_measurement_context_rejects_bad_probability(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_measurement_context",
                        "type": "unitary_measurement_context",
                        "state": [1.0, 0.0],
                        "basis": [
                            [0.7071067811865476, 0.7071067811865476],
                            [0.7071067811865476, -0.7071067811865476],
                        ],
                        "expected_probabilities": [1.0, 0.0],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"measurement_probability_mismatch"})

    def test_unitary_measurement_context_rejects_nonunitary_basis(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_measurement_basis",
                        "type": "unitary_measurement_context",
                        "state": [1.0, 0.0],
                        "basis": [[1.0, 0.1], [0.0, 1.0]],
                        "expected_probabilities": [1.0, 0.0],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_sorkin_parameter_rejects_non_psd_kernel(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_sorkin_kernel",
                        "type": "triple_path_sorkin_parameter",
                        "max_abs_kappa": 1.0e-10,
                        "weights": [0.5773502691896258, 0.5773502691896258, 0.5773502691896258],
                        "gamma": [[1.0, 2.0, 0.0], [2.0, 1.0, 0.0], [0.0, 0.0, 1.0]],
                        "events": {"A": [0], "B": [1], "C": [2]},
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"sorkin_kernel_not_psd"})

    def test_marker_eraser_visibility_rejects_bad_marked_visibility(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_marker_visibility",
                        "type": "marker_eraser_visibility",
                        "initial_visibility": 1.0,
                        "marker_overlap": 0.6,
                        "expected_marked_visibility": 0.7,
                        "expected_distinguishability": 0.8,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"marker_visibility_mismatch"})

    def test_bell_chsh_table_rejects_signalling_table(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_bell_signalling",
                        "type": "bell_chsh_table",
                        "expected_abs_s": 0.0,
                        "max_abs_s": 2.8284271247461903,
                        "contexts": bell_contexts(signalling=True),
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"bell_signalling"})

    def test_bell_chsh_table_rejects_super_tsirelson_table(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_bell_bound",
                        "type": "bell_chsh_table",
                        "expected_abs_s": 4.0,
                        "max_abs_s": 2.8284271247461903,
                        "contexts": pr_box_contexts(),
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"bell_chsh_bound_exceeded"})

    def test_bell_chsh_from_amplitudes_rejects_bad_chsh(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_bell_amplitudes",
                        "type": "bell_chsh_from_amplitudes",
                        "expected_abs_s": 2.0,
                        "max_abs_s": 2.8284271247461903,
                        "contexts": bell_amplitude_contexts(),
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"bell_chsh_mismatch"})

    def test_bell_chsh_from_amplitudes_rejects_unnormalized_context(self) -> None:
        contexts = bell_amplitude_contexts()
        contexts[0] = {
            "x": 0,
            "y": 0,
            "amplitudes": [
                {"a": 1, "b": 1, "amp": 1.0},
                {"a": 1, "b": -1, "amp": 1.0},
                {"a": -1, "b": 1, "amp": 0.0},
                {"a": -1, "b": -1, "amp": 0.0},
            ],
        }
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_bell_amplitude_norm",
                        "type": "bell_chsh_from_amplitudes",
                        "expected_abs_s": 2.8284271247461903,
                        "max_abs_s": 2.8284271247461903,
                        "contexts": contexts,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_unitary_network_probability_rejects_bad_output(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_unitary_network_output",
                        "type": "unitary_network_probability",
                        "state": [1.0, 0.0],
                        "unitaries": [
                            [
                                [0.7071067811865476, 0.7071067811865476],
                                [0.7071067811865476, -0.7071067811865476],
                            ]
                        ],
                        "expected_probabilities": [1.0, 0.0],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"unitary_network_probability_mismatch"})

    def test_projective_measurement_update_rejects_nonprojector(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_projector",
                        "type": "projective_measurement_update",
                        "state": [1.0, 0.0],
                        "projectors": [
                            [[1.0, 0.0], [0.0, 0.2]],
                            [[0.0, 0.0], [0.0, 0.8]],
                        ],
                        "expected_probabilities": [1.0, 0.0],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_projective_measurement_update_rejects_bad_probability(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_projective_probability",
                        "type": "projective_measurement_update",
                        "state": [0.6, 0.8],
                        "projectors": [
                            [[1.0, 0.0], [0.0, 0.0]],
                            [[0.0, 0.0], [0.0, 1.0]],
                        ],
                        "expected_probabilities": [0.5, 0.5],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"projective_probability_mismatch"})

    def test_stern_gerlach_context_readout_rejects_bad_probability(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_stern_gerlach_context",
                        "type": "stern_gerlach_context_readout",
                        "state": [1.0, 0.0],
                        "context": [[1.0, 0.0], [0.0, 1.0]],
                        "expected_probabilities": [0.5, 0.5],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"stern_gerlach_probability_mismatch"})

    def test_sequential_sg_noncommuting_context_rejects_bad_probability(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_sequential_sg",
                        "type": "sequential_sg_noncommuting_context",
                        "initial_state": [1.0, 0.0],
                        "sequences": [
                            {
                                "id": "z_x_z",
                                "contexts": [
                                    [[1.0, 0.0], [0.0, 1.0]],
                                    [
                                        [0.7071067811865476, 0.7071067811865476],
                                        [0.7071067811865476, -0.7071067811865476],
                                    ],
                                    [[1.0, 0.0], [0.0, 1.0]],
                                ],
                                "expected_final_probabilities": [1.0, 0.0],
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"sequential_sg_probability_mismatch"})

    def test_two_level_update_oscillation_rejects_bad_probability(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_two_level_update",
                        "type": "two_level_update_oscillation",
                        "initial_state": [1.0, 0.0],
                        "angular_frequency": 2.0,
                        "samples": [
                            {
                                "time": 0.7853981633974483,
                                "expected_probabilities": [1.0, 0.0],
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"two_level_update_probability_mismatch"})

    def test_delayed_context_partition_rejects_bad_probability(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_delayed_context_partition",
                        "type": "delayed_context_partition",
                        "state": [0.7071067811865476, 0.7071067811865476],
                        "readouts": [
                            {
                                "id": "open_path_context",
                                "context": [[1.0, 0.0], [0.0, 1.0]],
                                "expected_probabilities": [0.5, 0.5],
                            },
                            {
                                "id": "closed_interference_context",
                                "context": [
                                    [0.7071067811865476, 0.7071067811865476],
                                    [0.7071067811865476, -0.7071067811865476],
                                ],
                                "expected_probabilities": [0.5, 0.5],
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"delayed_context_probability_mismatch"})

    def test_ramsey_clock_phase_rejects_bad_probability(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_ramsey_clock_phase",
                        "type": "ramsey_clock_phase",
                        "initial_state": [1.0, 0.0],
                        "first_pulse": [
                            [0.7071067811865476, 0.7071067811865476],
                            [0.7071067811865476, -0.7071067811865476],
                        ],
                        "second_pulse": [
                            [0.7071067811865476, 0.7071067811865476],
                            [0.7071067811865476, -0.7071067811865476],
                        ],
                        "samples": [
                            {
                                "phase": 1.5707963267948966,
                                "expected_probabilities": [1.0, 0.0],
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ramsey_clock_phase_probability_mismatch"})

    def test_ab_holonomy_phase_rejects_bad_phase(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_ab_holonomy_phase",
                        "type": "ab_holonomy_phase",
                        "charge": 1.0,
                        "magnetic_flux": 1.5707963267948966,
                        "hbar": 1.0,
                        "expected_phase": 0.0,
                        "local_force_bound": 0.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ab_holonomy_phase_mismatch"})

    def test_ab_flux_period_rejects_bad_period(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_ab_flux_period",
                        "type": "ab_flux_period",
                        "charge": 2.0,
                        "h": 6.0,
                        "expected_flux_period": 2.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ab_flux_period_mismatch"})

    def test_action_frequency_threshold_rejects_bad_emission(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_action_frequency_threshold",
                        "type": "action_frequency_threshold",
                        "h": 2.0,
                        "work_function": 5.0,
                        "samples": [
                            {
                                "frequency": 3.0,
                                "expected_emission": False,
                                "expected_kinetic_energy": 1.0,
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"action_frequency_emission_mismatch"})

    def test_spectral_anchor_consistency_rejects_bad_frequency(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_spectral_anchor",
                        "type": "spectral_anchor_consistency",
                        "h": 2.0,
                        "transitions": [
                            {
                                "id": "line_a",
                                "delta_energy": 8.0,
                                "frequency": 3.0,
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"spectral_anchor_frequency_mismatch"})

    def test_barrier_transmission_rejects_bad_transmission(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_barrier_transmission",
                        "type": "barrier_transmission",
                        "classically_forbidden": True,
                        "decay_constant": 0.5,
                        "width": 2.0,
                        "expected_transmission": 0.5,
                        "expected_reflection": 0.5,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"barrier_transmission_mismatch"})

    def test_repeated_context_zeno_rejects_bad_survival(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_repeated_context_zeno",
                        "type": "repeated_context_zeno",
                        "total_angle": 1.5707963267948966,
                        "samples": [
                            {
                                "readout_count": 1,
                                "expected_survival": 1.0,
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"repeated_context_zeno_survival_mismatch"})

    def test_bosonic_indistinguishability_rejects_bad_coincidence(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_bosonic_indistinguishability",
                        "type": "bosonic_indistinguishability",
                        "wavepacket_overlap": 1.0,
                        "expected_coincidence": 0.5,
                        "expected_bunching": 0.5,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"bosonic_coincidence_mismatch"})

    def test_single_quantum_facticity_rejects_bad_g2(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_single_quantum_facticity",
                        "type": "single_quantum_facticity",
                        "trial_count": 100,
                        "detector_a_count": 50,
                        "detector_b_count": 50,
                        "coincidence_count": 0,
                        "expected_g2_zero": 0.5,
                        "max_g2_zero": 1.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"single_quantum_g2_mismatch"})

    def test_conditional_inheritance_swap_rejects_bad_correlation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_conditional_inheritance_swap",
                        "type": "conditional_inheritance_swap",
                        "bell_outcome": "psi_minus",
                        "remote_correlations": [
                            {
                                "context": "zz",
                                "expected_correlation": 1.0,
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"conditional_inheritance_swap_correlation_mismatch"})

    def test_context_transfer_no_cloning_rejects_bad_target(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_context_transfer",
                        "type": "context_transfer_no_cloning",
                        "input_state": [0.6, 0.8],
                        "bell_branch": "psi_minus",
                        "expected_target_state": [0.8, 0.6],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"context_transfer_target_state_mismatch"})

    def test_no_cloning_context_invariance_rejects_bad_obstruction_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_no_cloning_context_invariance",
                        "type": "no_cloning_context_invariance",
                        "state_overlap": 0.5,
                        "min_obstruction": 0.1,
                        "expected_obstructed": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"no_cloning_obstruction_mismatch"})

    def test_multipartite_contextuality_rejects_bad_obstruction_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_multipartite_contextuality",
                        "type": "multipartite_contextuality",
                        "constraints": [
                            {"context": ["x", "y", "y"], "expected_product": 1},
                            {"context": ["y", "x", "y"], "expected_product": 1},
                            {"context": ["y", "y", "x"], "expected_product": 1},
                            {"context": ["x", "x", "x"], "expected_product": -1},
                        ],
                        "expected_obstructed": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"multipartite_contextuality_obstruction_mismatch"})

    def test_ks_contextuality_obstruction_rejects_bad_obstruction_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_ks_contextuality",
                        "type": "ks_contextuality_obstruction",
                        "contexts": [["a", "b"], ["b", "c"], ["c", "a"]],
                        "expected_obstructed": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ks_contextuality_obstruction_mismatch"})

    def test_temporal_facticity_rejects_bad_k(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_temporal_facticity",
                        "type": "temporal_facticity",
                        "c12": 0.7071067811865476,
                        "c23": 0.7071067811865476,
                        "c13": 0.0,
                        "expected_k": 1.0,
                        "macrorealist_bound": 1.0,
                        "expected_violation": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"temporal_facticity_k_mismatch"})

    def test_partial_facticity_readout_rejects_bad_pointer_shift(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_partial_facticity",
                        "type": "partial_facticity_readout",
                        "coupling": 0.1,
                        "weak_value": 2.0,
                        "expected_pointer_shift": 0.1,
                        "observed_disturbance": 0.01,
                        "max_disturbance": 0.05,
                        "distinguishability_gain": 0.2,
                        "facticity_threshold": 1.0,
                        "expected_full_facticity": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"partial_facticity_pointer_shift_mismatch"})

    def test_measurement_facticity_route_rejects_bad_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_measurement_facticity_route",
                        "type": "measurement_facticity_route",
                        "conditions": list(MEASUREMENT_FACTICITY_ROUTE_CONDITIONS),
                        "samples": [
                            {
                                "id": "partial_pointer",
                                "readout_gain": 0.2,
                                "facticity_threshold": 1.0,
                                "disturbance": 0.01,
                                "max_disturbance": 0.05,
                                "recoverability_loss": 0.1,
                                "recoverability_threshold": 2.0,
                                "expected_status": "full_facticity",
                            },
                            {
                                "id": "stable_record",
                                "readout_gain": 1.2,
                                "facticity_threshold": 1.0,
                                "disturbance": 0.2,
                                "max_disturbance": 0.05,
                                "recoverability_loss": 2.5,
                                "recoverability_threshold": 2.0,
                                "expected_status": "full_facticity",
                            },
                            {
                                "id": "recoverable_marker",
                                "readout_gain": 0.0,
                                "facticity_threshold": 1.0,
                                "disturbance": 0.0,
                                "max_disturbance": 0.05,
                                "recoverability_loss": 0.1,
                                "recoverability_threshold": 2.0,
                                "expected_status": "recoverable_marker",
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"measurement_facticity_route_status_mismatch"})

    def test_unitary_graph_walk_rejects_bad_distribution(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_unitary_graph_walk",
                        "type": "unitary_graph_walk",
                        "steps": 3,
                        "initial_coin": [1.0, 0.0],
                        "expected_distribution": [
                            {"position": -3, "probability": 0.125},
                            {"position": -1, "probability": 0.125},
                            {"position": 1, "probability": 0.125},
                            {"position": 3, "probability": 0.625},
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"unitary_graph_walk_distribution_mismatch"})

    def test_distinguishability_geometry_probe_rejects_bad_candidate_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_distinguishability_geometry_probe",
                        "type": "distinguishability_geometry_probe",
                        "requirements": list(DISTINGUISHABILITY_GEOMETRY_REQUIREMENTS),
                        "expected_selected_carrier": "none",
                        "candidates": [
                            {
                                "id": "classical_simplex",
                                "expected_status": "survives",
                                "capabilities": {
                                    "contextual_probability_readout": "supported",
                                    "interference_i3_zero": "unsupported",
                                    "reversible_inheritance_maps": "unsupported",
                                    "contextual_correlation_obstruction": "unsupported",
                                    "noncopyability": "unsupported",
                                    "tensor_like_composition": "supported",
                                },
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"distinguishability_geometry_candidate_status_mismatch"})

    def test_local_tomography_separator_rejects_bad_candidate_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_local_tomography_separator",
                        "type": "local_tomography_separator",
                        "expected_selected_carrier": "none",
                        "systems": [
                            {
                                "id": "complex_qubit_pair",
                                "local_a": 4,
                                "local_b": 4,
                                "composite": 16,
                                "expected_locally_tomographic": True,
                            },
                            {
                                "id": "real_rebit_pair",
                                "local_a": 3,
                                "local_b": 3,
                                "composite": 10,
                                "expected_locally_tomographic": False,
                            }
                        ],
                        "candidates": [
                            {
                                "id": "real_hilbert_like",
                                "local_tomography": "unsupported",
                                "expected_status": "survives",
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"local_tomography_candidate_status_mismatch"})

    def test_idt_local_tomography_derivation_rejects_hidden_joint_admissibility(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_idt_local_tomography",
                        "type": "idt_local_tomography_derivation",
                        "idt_conditions": list(IDT_LOCAL_TOMOGRAPHY_CONDITIONS),
                        "systems": [
                            {
                                "id": "hidden_joint_sector",
                                "local_a": 4,
                                "local_b": 4,
                                "composite": 18,
                                "joint_only_degrees": 2,
                                "expected_product_dimension": 16,
                                "expected_locally_tomographic": False,
                                "expected_idt_admissible": True,
                            },
                            {
                                "id": "product_context_table",
                                "local_a": 4,
                                "local_b": 4,
                                "composite": 16,
                                "joint_only_degrees": 0,
                                "expected_product_dimension": 16,
                                "expected_locally_tomographic": True,
                                "expected_idt_admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"idt_local_tomography_admissibility_mismatch"})

    def test_context_product_exhaustion_rejects_hidden_invariant_admissibility(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_context_product_exhaustion",
                        "type": "context_product_exhaustion",
                        "idt_primitives": list(CONTEXT_PRODUCT_EXHAUSTION_PRIMITIVES),
                        "candidates": [
                            {
                                "id": "hidden_joint_candidate",
                                "left_contexts": ["a0", "a1"],
                                "right_contexts": ["b0", "b1"],
                                "product_contexts": [
                                    {"id": "a0_b0", "left": "a0", "right": "b0"},
                                    {"id": "a0_b1", "left": "a0", "right": "b1"},
                                    {"id": "a1_b0", "left": "a1", "right": "b0"},
                                    {"id": "a1_b1", "left": "a1", "right": "b1"},
                                ],
                                "stable_invariants": [
                                    {
                                        "id": "visible_joint_table",
                                        "witness_contexts": ["a0_b0", "a0_b1", "a1_b0", "a1_b1"],
                                        "expected_exhausted": True,
                                    },
                                    {
                                        "id": "hidden_joint_phase",
                                        "witness_contexts": [],
                                        "expected_exhausted": False,
                                    },
                                ],
                                "expected_context_product_exhausted": False,
                                "expected_idt_admissible": True,
                            },
                            {
                                "id": "exhausted_product_candidate",
                                "left_contexts": ["a0"],
                                "right_contexts": ["b0"],
                                "product_contexts": [{"id": "a0_b0", "left": "a0", "right": "b0"}],
                                "stable_invariants": [
                                    {
                                        "id": "single_product_record",
                                        "witness_contexts": ["a0_b0"],
                                        "expected_exhausted": True,
                                    }
                                ],
                                "expected_context_product_exhausted": True,
                                "expected_idt_admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"context_product_exhaustion_admissibility_mismatch"})

    def test_idt_purification_filtering_rejects_bad_posterior(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_idt_purification_filtering",
                        "type": "idt_purification_filtering",
                        "idt_conditions": list(IDT_PURIFICATION_FILTERING_CONDITIONS),
                        "purification_samples": [
                            {
                                "id": "two_branch_extension",
                                "schmidt_amplitudes": [0.8, 0.6],
                                "expected_marginal": [0.64, 0.36],
                                "environment_dimension": 2,
                                "expected_recoverable_extension": True,
                            }
                        ],
                        "filtering_samples": [
                            {
                                "id": "bad_two_cell_filter",
                                "prior": [0.2, 0.3, 0.5],
                                "filter_indices": [1, 2],
                                "expected_acceptance_probability": 0.8,
                                "expected_posterior": [0.5, 0.5],
                                "expected_filter_admissible": True,
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"idt_purification_filtering_posterior_mismatch"})

    def test_idt_bounded_correlation_rejects_boxworld_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_idt_bounded_correlation",
                        "type": "idt_bounded_correlation",
                        "tolerance": 1.0e-10,
                        "idt_conditions": list(IDT_BOUNDED_CORRELATION_CONDITIONS),
                        "max_abs_s": 2.8284271247461903,
                        "samples": [
                            {
                                "id": "pr_box_like",
                                "correlations": [1.0, 1.0, 1.0, -1.0],
                                "expected_abs_s": 4.0,
                                "expected_status": "survives",
                            },
                            {
                                "id": "tsirelson_edge",
                                "correlations": [
                                    0.7071067811865476,
                                    0.7071067811865476,
                                    0.7071067811865476,
                                    -0.7071067811865476,
                                ],
                                "expected_abs_s": 2.8284271247461903,
                                "expected_status": "survives",
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"idt_bounded_correlation_status_mismatch"})

    def test_noncomplex_jordan_separator_rejects_bad_candidate_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_noncomplex_jordan_separator",
                        "type": "noncomplex_jordan_separator",
                        "conditions": list(NONCOMPLEX_JORDAN_SEPARATOR_CONDITIONS),
                        "expected_selected_carrier": "none",
                        "candidates": [
                            {
                                "id": "real_hilbert_like",
                                "expected_status": "survives",
                                "capabilities": {
                                    "complex_phase_orientation": "unsupported",
                                    "local_tomographic_composition": "unsupported",
                                    "associative_tensor_composition": "supported",
                                    "purification_filtering_route": "underdetermined",
                                    "bounded_correlation_route": "supported",
                                },
                            },
                            {
                                "id": "complex_hilbert_like",
                                "expected_status": "survives",
                                "capabilities": {
                                    "complex_phase_orientation": "supported",
                                    "local_tomographic_composition": "supported",
                                    "associative_tensor_composition": "supported",
                                    "purification_filtering_route": "supported",
                                    "bounded_correlation_route": "supported",
                                },
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"noncomplex_jordan_separator_status_mismatch"})

    def test_generic_gpt_closure_separator_rejects_bad_candidate_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_generic_gpt_closure",
                        "type": "generic_gpt_closure_separator",
                        "conditions": list(GENERIC_GPT_CLOSURE_CONDITIONS),
                        "expected_selected_carrier": "none",
                        "candidates": [
                            {
                                "id": "unconstrained_generic_gpt_cone",
                                "expected_status": "survives",
                                "capabilities": {
                                    "finite_route_witness_completeness": "unsupported",
                                    "no_unwitnessed_effect_cone_degrees": "unsupported",
                                    "tomographic_state_effect_duality": "underdetermined",
                                    "reversible_filter_closure": "underdetermined",
                                    "bounded_composite_correlations": "unsupported",
                                },
                            },
                            {
                                "id": "complex_hilbert_like",
                                "expected_status": "survives",
                                "capabilities": {
                                    "finite_route_witness_completeness": "supported",
                                    "no_unwitnessed_effect_cone_degrees": "supported",
                                    "tomographic_state_effect_duality": "supported",
                                    "reversible_filter_closure": "supported",
                                    "bounded_composite_correlations": "supported",
                                },
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"generic_gpt_closure_status_mismatch"})

    def test_tensor_composition_route_rejects_bad_factorization_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_tensor_composition_route",
                        "type": "tensor_composition_route",
                        "conditions": list(TENSOR_COMPOSITION_ROUTE_CONDITIONS),
                        "systems": [
                            {
                                "id": "two_qubit_context",
                                "local_a": 2,
                                "local_b": 2,
                                "expected_composite": 4,
                                "expected_product_basis_count": 4,
                            }
                        ],
                        "states": [
                            {
                                "id": "product_state",
                                "schmidt_coefficients": [1.0, 0.0],
                                "expected_schmidt_rank": 1,
                                "expected_factorizable": True,
                            },
                            {
                                "id": "bell_state",
                                "schmidt_coefficients": [0.7071067811865476, 0.7071067811865476],
                                "expected_schmidt_rank": 2,
                                "expected_factorizable": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"tensor_composition_factorization_mismatch"})

    def test_qm_core_recompile_route_rejects_missing_route(self) -> None:
        route_gates = [route for route in QM_CORE_RECOMPILE_REQUIRED_ROUTES if route != "carrier_selection_frontier_demo"]
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_qm_core_recompile_route",
                        "type": "qm_core_recompile_route",
                        "shared_operations": list(QM_UNIVERSAL_PATTERN_REQUIRED_OPERATIONS),
                        "route_gates": route_gates,
                        "kernel_count": 6,
                        "experiment_count": 35,
                        "finite_gate_reference_count": 35,
                        "expected_kernel_count": 6,
                        "expected_experiment_count": 35,
                        "expected_finite_gate_reference_count": 35,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"qm_core_recompile_routes_mismatch"})

    def test_continuum_action_frontier_rejects_premature_extension(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_continuum_action_frontier",
                        "type": "continuum_action_frontier",
                        "requirements": list(CONTINUUM_ACTION_FRONTIER_REQUIREMENTS),
                        "components": [
                            {"requirement": "finite_generator_reconstruction", "status": "supported"},
                            {"requirement": "finite_translation_relation", "status": "supported"},
                            {"requirement": "finite_weyl_relation", "status": "supported"},
                            {"requirement": "strong_continuity_modulus", "status": "supported"},
                            {"requirement": "generator_difference_convergence", "status": "supported"},
                            {"requirement": "calibrated_action_holdout", "status": "supported"},
                            {"requirement": "first_principles_hbar_lock", "status": "blocked"},
                            {"requirement": "field_mode_limit", "status": "open"},
                        ],
                        "expected_extension_status": "derived",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"continuum_action_frontier_status_mismatch"})

    def test_full_qm_closure_frontier_rejects_premature_closure(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_full_qm_closure_frontier",
                        "type": "full_qm_closure_frontier",
                        "requirements": list(FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS),
                        "components": [
                            {"requirement": "universal_carrier_selection_theorem", "status": "open"},
                            {"requirement": "hilbert_carrier_derivation", "status": "blocked"},
                            {"requirement": "universal_born_rule_theorem", "status": "open"},
                            {"requirement": "wigner_reversible_inheritance_theorem", "status": "open"},
                            {"requirement": "apparatus_facticity_theorem", "status": "open"},
                            {"requirement": "monoidal_tensor_composition_theorem", "status": "open"},
                            {"requirement": "first_principles_hbar_lock", "status": "blocked"},
                            {"requirement": "field_mode_continuum_limit", "status": "open"},
                        ],
                        "expected_full_qm_status": "derived",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"full_qm_closure_frontier_status_mismatch"})

    def test_full_qm_frontier_requires_theorem_cards(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "full_qm_frontier_without_cards",
                        "type": "full_qm_closure_frontier",
                        "requirements": list(FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS),
                        "components": [
                            {"requirement": requirement, "status": "open"}
                            for requirement in FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS
                        ],
                        "expected_full_qm_status": "target",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"full_qm_frontier_theorem_card_missing"})

    def test_theorem_card_rejects_ungrounded_dependency(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "theorem_cards": [
                    {
                        "id": "bad_theorem_card",
                        "statement": "A bad card depends on a missing graph node.",
                        "role": "theorem",
                        "assumptions": [],
                        "dependencies": ["missing_theorem_dependency"],
                        "proof_status": "open",
                        "verifier": "",
                        "known_failures": [],
                        "physical_scope": "test",
                        "forbidden_claims": [],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"theorem_card_dependency_missing"})

    def test_full_qm_frontier_status_must_match_theorem_card(self) -> None:
        cards = [
            {
                "id": requirement,
                "statement": f"{requirement} statement.",
                "role": "theorem",
                "assumptions": [],
                "dependencies": [],
                "proof_status": "open",
                "verifier": "",
                "known_failures": [],
                "physical_scope": "test",
                "forbidden_claims": [],
            }
            for requirement in FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS
        ]
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "theorem_cards": cards,
                "finite_gates": [
                    {
                        "id": "full_qm_frontier_mismatched_card",
                        "type": "full_qm_closure_frontier",
                        "requirements": list(FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS),
                        "components": [
                            {
                                "requirement": FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS[0],
                                "status": "blocked",
                            },
                            *[
                                {"requirement": requirement, "status": "open"}
                                for requirement in FULL_QM_CLOSURE_FRONTIER_REQUIREMENTS[1:]
                            ],
                        ],
                        "expected_full_qm_status": "blocked",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"full_qm_frontier_theorem_card_status_mismatch"})

    def test_gpt_principle_separator_rejects_bad_candidate_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_gpt_principle_separator",
                        "type": "gpt_principle_separator",
                        "principles": list(GPT_SEPARATOR_PRINCIPLES),
                        "expected_selected_carrier": "none",
                        "candidates": [
                            {
                                "id": "complex_hilbert_like",
                                "expected_status": "survives",
                                "capabilities": {
                                    "local_tomography": "supported",
                                    "homogeneous_self_dual_cone": "supported",
                                    "continuous_reversible_bit_symmetry": "supported",
                                    "no_third_order_interference": "supported",
                                    "purification_or_filtering": "supported",
                                    "bounded_nonclassical_correlations": "supported",
                                },
                            },
                            {
                                "id": "boxworld_like_gpt",
                                "expected_status": "survives",
                                "capabilities": {
                                    "local_tomography": "supported",
                                    "homogeneous_self_dual_cone": "unsupported",
                                    "continuous_reversible_bit_symmetry": "unsupported",
                                    "no_third_order_interference": "underdetermined",
                                    "purification_or_filtering": "unsupported",
                                    "bounded_nonclassical_correlations": "unsupported",
                                },
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"gpt_principle_separator_candidate_status_mismatch"})

    def test_carrier_selection_frontier_rejects_premature_selection(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_carrier_selection_frontier",
                        "type": "carrier_selection_frontier",
                        "open_obstructions": list(CARRIER_SELECTION_OPEN_OBSTRUCTIONS),
                        "expected_selected_carrier": "complex_hilbert_like",
                        "expected_frontier_status": "selected_by_current_gates",
                        "candidates": [
                            {
                                "id": "complex_hilbert_like",
                                "status": "survives",
                                "blocking_obstructions": [],
                            },
                            {
                                "id": "euclidean_jordan_family",
                                "status": "underdetermined",
                                "blocking_obstructions": [
                                    "extend_context_product_exhaustion_to_carrier_theorem",
                                    "extend_purification_filtering_to_carrier_theorem",
                                    "extend_noncomplex_jordan_exclusion_to_classification_theorem",
                                ],
                            },
                            {
                                "id": "generic_gpt_cone",
                                "status": "underdetermined",
                                "blocking_obstructions": [
                                    "extend_context_product_exhaustion_to_carrier_theorem",
                                    "extend_purification_filtering_to_carrier_theorem",
                                    "extend_bounded_correlation_to_carrier_theorem",
                                    "extend_generic_gpt_exclusion_to_classification_theorem",
                                ],
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"carrier_selection_frontier_selection_mismatch"})

    def test_carrier_selection_proof_route_rejects_premature_formal_proof(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_carrier_selection_proof_route",
                        "type": "carrier_selection_proof_route",
                        "target_theorem": "universal_carrier_selection_theorem",
                        "lemmas": [
                            {
                                "id": lemma,
                                "status": "finite_witnessed",
                                "evidence_refs": ["finite_witness"],
                                "open_gap": "not yet formal",
                            }
                            for lemma in CARRIER_SELECTION_OPEN_OBSTRUCTIONS
                        ],
                        "expected_proof_status": "formal_proof",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"carrier_selection_proof_route_status_mismatch"})

    def test_context_product_carrier_lemma_rejects_premature_formal_proof(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_context_product_carrier_lemma",
                        "type": "context_product_carrier_lemma_route",
                        "target_lemma": "extend_context_product_exhaustion_to_carrier_theorem",
                        "required_primitives": list(CONTEXT_PRODUCT_EXHAUSTION_PRIMITIVES),
                        "required_conditions": list(IDT_LOCAL_TOMOGRAPHY_CONDITIONS),
                        "finite_evidence_refs": [
                            "context_product_exhaustion_demo",
                            "idt_local_tomography_derivation_demo",
                        ],
                        "excluded_counterexamples": [
                            "hidden_joint_invariant_composite",
                            "real_rebit_pair",
                            "hidden_joint_sector",
                        ],
                        "expected_exclusion_count": 3,
                        "open_generalization_gaps": ["still finite"],
                        "expected_lemma_status": "formal_proof",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"context_product_carrier_lemma_status_mismatch"})

    def test_purification_filtering_carrier_lemma_rejects_premature_formal_proof(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_purification_filtering_carrier_lemma",
                        "type": "purification_filtering_carrier_lemma_route",
                        "target_lemma": "extend_purification_filtering_to_carrier_theorem",
                        "required_conditions": list(IDT_PURIFICATION_FILTERING_CONDITIONS),
                        "finite_evidence_refs": ["idt_purification_filtering_demo"],
                        "excluded_counterexamples": [
                            "insufficient_environment_extension",
                            "zero_support_filter",
                        ],
                        "expected_exclusion_count": 2,
                        "open_generalization_gaps": ["still finite"],
                        "expected_lemma_status": "formal_proof",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"purification_filtering_carrier_lemma_status_mismatch"})

    def test_bounded_correlation_carrier_lemma_rejects_premature_formal_proof(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_bounded_correlation_carrier_lemma",
                        "type": "bounded_correlation_carrier_lemma_route",
                        "target_lemma": "extend_bounded_correlation_to_carrier_theorem",
                        "required_conditions": list(IDT_BOUNDED_CORRELATION_CONDITIONS),
                        "required_principles": list(GPT_SEPARATOR_PRINCIPLES),
                        "finite_evidence_refs": [
                            "idt_bounded_correlation_demo",
                            "gpt_principle_separator_demo",
                        ],
                        "excluded_counterexamples": [
                            "pr_box_like",
                            "boxworld_like_gpt",
                        ],
                        "expected_exclusion_count": 2,
                        "open_generalization_gaps": ["still finite"],
                        "expected_lemma_status": "formal_proof",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"bounded_correlation_carrier_lemma_status_mismatch"})

    def test_noncomplex_jordan_classification_lemma_rejects_premature_formal_proof(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_noncomplex_jordan_classification_lemma",
                        "type": "noncomplex_jordan_classification_lemma_route",
                        "target_lemma": "extend_noncomplex_jordan_exclusion_to_classification_theorem",
                        "required_conditions": list(NONCOMPLEX_JORDAN_SEPARATOR_CONDITIONS),
                        "finite_evidence_refs": ["noncomplex_jordan_separator_demo"],
                        "excluded_counterexamples": [
                            "real_hilbert_like",
                            "quaternionic_hilbert_like",
                            "exceptional_jordan_like",
                        ],
                        "expected_exclusion_count": 3,
                        "open_generalization_gaps": ["still finite"],
                        "expected_lemma_status": "formal_proof",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"noncomplex_jordan_classification_lemma_status_mismatch"})

    def test_spin_bell_angle_model_rejects_bad_chsh(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_spin_bell_angles",
                        "type": "spin_bell_angle_model",
                        "alice_angles": [0.0, 1.5707963267948966],
                        "bob_angles": [0.7853981633974483, -0.7853981633974483],
                        "expected_abs_s": 2.0,
                        "max_abs_s": 2.8284271247461903,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"spin_bell_chsh_mismatch"})

    def test_unitary_generator_reconstruction_rejects_bad_unitary(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_generator_unitary",
                        "type": "unitary_generator_reconstruction",
                        "dt": 0.5,
                        "omegas": [1.0],
                        "expected_unitary": [[1.0]],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"unitary_generator_mismatch"})

    def test_translation_de_broglie_scale_rejects_bad_momentum(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_translation_scale",
                        "type": "translation_de_broglie_scale",
                        "shift": 0.25,
                        "wave_numbers": [2.0],
                        "hbar": 0.5,
                        "expected_translation": [
                            [{"re": 0.8775825618903728, "im": -0.479425538604203}]
                        ],
                        "expected_momenta": [2.0],
                        "expected_wavelengths": [3.141592653589793],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"momentum_scale_mismatch"})

    def test_finite_weyl_relation_rejects_bad_phase(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_weyl_phase",
                        "type": "finite_weyl_relation",
                        "dimension": 5,
                        "expected_phase": 1.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"weyl_phase_mismatch"})

    def test_one_parameter_unitary_flow_rejects_bad_pair(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_unitary_flow",
                        "type": "one_parameter_unitary_flow",
                        "omegas": [1.0],
                        "times": [0.0, 0.25, 0.5],
                        "pairs": [{"left": 0.25, "right": 0.25, "sum": 0.25}],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"unitary_flow_group_law_mismatch"})

    def test_strong_continuity_modulus_rejects_large_deviation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_strong_continuity",
                        "type": "strong_continuity_modulus",
                        "omegas": [10.0],
                        "max_time": 0.1,
                        "samples": [0.1],
                        "max_deviation": 0.01,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"strong_continuity_modulus_exceeded"})

    def test_generator_difference_convergence_rejects_wrapped_step(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_generator_difference",
                        "type": "generator_difference_convergence",
                        "omega": 4.0,
                        "steps": [2.0],
                        "max_error": 0.01,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"generator_difference_error_exceeded"})

    def test_phase_action_scale_universality_rejects_bad_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_phase_action_scale",
                        "type": "phase_action_scale_universality",
                        "epsilon": 0.01,
                        "action_standard": 2.0,
                        "cycles": [
                            {
                                "id": "cal",
                                "role": "calibration",
                                "cost": 3.0,
                                "phase": 6.0,
                            },
                            {
                                "id": "val",
                                "role": "validation",
                                "cost": 4.0,
                                "phase": 7.0,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_action_scale_validation_failed"})

    def test_action_standard_independence_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_action_standard_source",
                        "type": "action_standard_independence",
                        "candidate_sources": ["primitive_update_work", "hbar_obs"],
                        "forbidden_sources": ["hbar_obs", "G_N", "planck_units"],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"action_standard_forbidden_source"})

    def test_action_standard_provenance_rejects_physical_claim_from_normalization(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_action_standard_provenance",
                        "type": "action_standard_provenance",
                        "candidate_sources": ["primitive_update_work"],
                        "forbidden_sources": ["hbar_obs", "G_N", "planck_units"],
                        "action_standard_status": "candidate",
                        "normalization_only": True,
                        "claims_physical_hbar": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"hbar_physical_claim_from_normalization"})

    def test_action_standard_work_time_provenance_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_work_time_action",
                        "type": "action_standard_work_time_provenance",
                        "work_unit": 2.0,
                        "tick": 3.0,
                        "expected_action": 7.0,
                        "candidate_sources": ["primitive_work_unit_I", "primitive_tick_I"],
                        "forbidden_sources": ["hbar_obs", "G_N", "planck_units"],
                        "action_standard_status": "candidate",
                        "claims_physical_action": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"action_standard_work_time_mismatch"})

    def test_action_standard_work_time_provenance_rejects_candidate_physical_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_work_time_claim",
                        "type": "action_standard_work_time_provenance",
                        "work_unit": 2.0,
                        "tick": 3.0,
                        "expected_action": 6.0,
                        "candidate_sources": ["primitive_work_unit_I", "primitive_tick_I"],
                        "forbidden_sources": ["hbar_obs", "G_N", "planck_units"],
                        "action_standard_status": "candidate",
                        "claims_physical_action": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"physical_action_claim_without_independent_standard"})

    def test_action_scale_gauge_obstruction_rejects_false_locked_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_action_scale_lock",
                        "type": "action_scale_gauge_obstruction",
                        "tick_samples": [3.0, 6.0, 9.0],
                        "work_samples": [2.0, 4.0, 8.0],
                        "tick_gauge_factor": 5.0,
                        "work_gauge_factor": 7.0,
                        "expected_action_scale_factor": 35.0,
                        "declared_status": "scale_locked",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"action_scale_gauge_status_mismatch"})

    def test_tick_scale_lock_rejects_false_lock_claim_from_bound(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_tick_lock",
                        "type": "tick_scale_lock_status",
                        "lower_bound": 0.0,
                        "upper_bound": 1.0,
                        "expected_width": 1.0,
                        "source_status": "bound_only",
                        "declared_status": "locked",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"tick_scale_lock_status_mismatch"})

    def test_work_scale_lock_rejects_false_lock_claim_from_candidate_mass(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_work_lock",
                        "type": "work_scale_lock_status",
                        "impulse": 12.0,
                        "velocity_delta": 3.0,
                        "expected_mass": 4.0,
                        "impulse_scale_status": "candidate",
                        "mass_anchor_status": "candidate",
                        "candidate_sources": ["inertial_response_protocol"],
                        "forbidden_sources": ["hbar_obs", "G_N", "planck_units"],
                        "declared_status": "locked",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"work_scale_lock_status_mismatch"})

    def test_action_anchor_lock_rejects_false_lock_claim_from_unlocked_inputs(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_action_lock",
                        "type": "action_anchor_lock_status",
                        "tick_lock_status": "bound_only",
                        "work_lock_status": "not_locked",
                        "gauge_status": "scale_not_locked",
                        "declared_status": "locked",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"action_anchor_lock_status_mismatch"})

    def test_ell0_radar_consistency_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_ell0_radar",
                        "type": "ell0_radar_consistency",
                        "c_value": 10.0,
                        "round_trip_time": 4.0,
                        "order_weight": 2.0,
                        "expected_ell0": 9.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ell0_radar_consistency_mismatch"})

    def test_ell0_link_frequency_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_ell0_frequency",
                        "type": "ell0_link_frequency_consistency",
                        "c_value": 12.0,
                        "omega_link": 3.0,
                        "expected_ell0": 5.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ell0_link_frequency_mismatch"})

    def test_ell0_no_gravity_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_ell0_source",
                        "type": "ell0_no_gravity_input",
                        "candidate_sources": ["clock_radar", "G_N"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "ell0_status": "candidate",
                        "claims_physical_length": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_length_forbidden_source"})

    def test_clock_vacuum_pole_candidate_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_clock_pole",
                        "type": "clock_vacuum_pole_candidate",
                        "candidate_edges": [5.0, 7.0],
                        "expected_omega_link": 6.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"clock_vacuum_pole_mismatch"})

    def test_clock_vacuum_pole_universality_rejects_spread(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_clock_pole_universality",
                        "type": "clock_vacuum_pole_universality",
                        "species_omega_values": [5.0, 5.2],
                        "tolerance": 1.0e-3,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"clock_vacuum_pole_universality_failed"})

    def test_clock_vacuum_pole_no_calibrated_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_clock_pole_source",
                        "type": "clock_vacuum_pole_no_calibrated_input",
                        "candidate_sources": ["clock_vacuum_response", "planck_units"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "pole_status": "candidate",
                        "claims_physical_frequency": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_clock_vacuum_pole_forbidden_source"})

    def test_ell0_candidate_from_clock_pole_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_ell0_clock_pole",
                        "type": "ell0_candidate_from_clock_pole",
                        "c_value": 12.0,
                        "omega_link": 3.0,
                        "expected_ell0": 5.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ell0_clock_pole_candidate_mismatch"})

    def test_ell0_candidate_no_gravity_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_ell0_candidate_source",
                        "type": "ell0_candidate_no_gravity_input",
                        "candidate_sources": ["clock_vacuum_pole_closure_I", "G_N"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "ell0_status": "candidate",
                        "claims_physical_length": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_length_forbidden_source"})

    def test_ell0_bound_not_value_rejects_exact_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_bound_promotion",
                        "type": "ell0_bound_not_value",
                        "bound_status": "upper_bound",
                        "uses_bound_only_input": True,
                        "claims_exact_length": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ell0_bound_used_as_value"})

    def test_spectral_law_free_parameter_audit_rejects_predictive_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_spectral_claim",
                        "type": "spectral_law_free_parameter_audit",
                        "free_parameters": ["theta_star"],
                        "claims_predictive": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"spectral_law_parametric_not_predictive"})

    def test_spectral_law_no_calibrated_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_spectral_source",
                        "type": "spectral_law_no_calibrated_input",
                        "candidate_sources": ["primitive_transition_phase_readout_I", "G_N"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "spectral_law_status": "candidate",
                        "claims_physical_spectral_law": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_spectral_law_forbidden_source"})

    def test_fixed_point_component_status_rejects_underived_predictive_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_fixed_point_claim",
                        "type": "fixed_point_component_status",
                        "components": {
                            "primitive_transition_phase_readout_I": "target",
                            "fixed_point_step_invariant_I": "derived",
                        },
                        "claims_predictive": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"fixed_point_route_underived"})

    def test_non_exact_holonomy_source_rejects_exact_cocycle_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_holonomy_claim",
                        "type": "non_exact_holonomy_source",
                        "source_status": "derived",
                        "exact_cocycle": True,
                        "claims_nontrivial_rotation": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"nonexact_holonomy_missing"})

    def test_rho_chi_protocol_invariance_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_rho_protocol",
                        "type": "rho_chi_protocol_invariance",
                        "tolerance": 1.0e-10,
                        "expected_rho": 1.0,
                        "protocols": [
                            {"eta_tau": 1.0, "C_chi": 1.0},
                            {"eta_tau": 2.0, "C_chi": 1.0},
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"rho_chi_protocol_mismatch"})

    def test_rho_chi_no_gravity_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_rho_source",
                        "type": "rho_chi_no_gravity_input",
                        "candidate_sources": ["radar_sampling_invariant", "G_N"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "rho_status": "candidate",
                        "claims_physical_rho": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_rho_chi_forbidden_source"})

    def test_kappa_omega_consistency_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_kappa_omega",
                        "type": "kappa_omega_consistency",
                        "hbar_value": 2.0,
                        "omega_link": 3.0,
                        "rho_chi": 1.5,
                        "expected_kappa": 5.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"kappa_omega_consistency_mismatch"})

    def test_kappa_omega_no_gravity_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_kappa_omega_source",
                        "type": "kappa_omega_no_gravity_input",
                        "candidate_sources": ["kappa_omega_consistency_gate", "G_N"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "relation_status": "candidate",
                        "claims_physical_relation": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_kappa_omega_forbidden_source"})

    def test_contraction_phase_degeneracy_rejects_unique_selection_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_contraction_phase_selection",
                        "type": "contraction_phase_degeneracy",
                        "recoverability_scores": [1.0, 1.0],
                        "phase_values": [0.0, 0.5],
                        "claims_unique_selection": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"contraction_phase_degeneracy"})

    def test_support_matching_phase_freedom_rejects_phase_selected_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_support_phase_selection",
                        "type": "support_matching_phase_freedom",
                        "unique_support_matching": True,
                        "diagonal_phase_freedom": True,
                        "claims_phase_selected": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"support_matching_phase_unselected"})

    def test_contraction_selection_no_calibrated_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_contraction_source",
                        "type": "contraction_selection_no_calibrated_input",
                        "candidate_sources": ["maximal_recoverability", "G_N"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "selection_status": "candidate",
                        "claims_physical_selection": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_contraction_selection_forbidden_source"})

    def test_fixed_point_step_integer_obstruction_rejects_exact_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_exact_step",
                        "type": "fixed_point_step_integer_obstruction",
                        "cycle_steps": 6,
                        "winding": 1,
                        "half_radar_steps": 1,
                        "claims_exact_compatibility": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"fixed_point_step_integer_obstruction"})

    def test_fixed_point_step_free_parameter_audit_rejects_derived_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_step_claim",
                        "type": "fixed_point_step_free_parameter_audit",
                        "free_parameters": ["zeta_step"],
                        "claims_derived_step": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"fixed_point_step_parametric"})

    def test_fixed_point_step_no_gravity_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_step_source",
                        "type": "fixed_point_step_no_gravity_input",
                        "candidate_sources": ["step_clock_readout_rule", "G_N"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "step_status": "candidate",
                        "claims_physical_step": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_fixed_point_step_forbidden_source"})

    def test_transition_phase_unit_readout_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_transition_phase",
                        "type": "transition_phase_unit_readout",
                        "transfer": {"re": 0.8, "im": 0.0},
                        "expected_unit_phase": {"re": 0.0, "im": 1.0},
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"transition_phase_unit_mismatch"})

    def test_cycle_holonomy_composition_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_cycle_holonomy",
                        "type": "cycle_holonomy_composition",
                        "unit_edges": [
                            {"from": "a", "to": "b", "unit_transfer": {"re": 1.0, "im": 0.0}},
                            {"from": "b", "to": "a", "unit_transfer": {"re": 1.0, "im": 0.0}},
                        ],
                        "cycle": ["a", "b", "a"],
                        "expected_holonomy": {"re": 0.0, "im": 1.0},
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"cycle_holonomy_composition_mismatch"})

    def test_primitive_transition_phase_no_calibrated_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_transition_phase_source",
                        "type": "primitive_transition_phase_no_calibrated_input",
                        "candidate_sources": ["transfer_phase_normalization_I", "G_N"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "phase_status": "candidate",
                        "claims_physical_phase": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_transition_phase_forbidden_source"})

    def test_holonomy_source_classification_rejects_exact_nonexact_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_holonomy_source",
                        "type": "holonomy_source_classification",
                        "source_class": "none",
                        "source_status": "target",
                        "exact_cocycle": False,
                        "claims_nonexact_source": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"holonomy_source_not_nonexact"})

    def test_holonomy_selector_class_registry_rejects_missing_class(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_selector_registry",
                        "type": "holonomy_selector_class_registry",
                        "registered_classes": [
                            "discrete_curvature",
                            "topological_winding",
                            "action_cost_obstruction",
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"holonomy_selector_class_registry_incomplete"})

    def test_holonomy_selector_status_rejects_empty_physical_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_selector_status",
                        "type": "holonomy_selector_status",
                        "selected_class": "none",
                        "selector_status": "candidate",
                        "claims_physical_selector": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"holonomy_selector_missing_source_class"})

    def test_holonomy_selector_no_calibrated_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_selector_source",
                        "type": "holonomy_selector_no_calibrated_input",
                        "candidate_sources": ["primitive_source_class_registry_I", "G_N"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "selector_status": "candidate",
                        "claims_physical_selector": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_holonomy_selector_forbidden_source"})

    def test_winding_selector_homotopy_consistency_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_winding_homotopy",
                        "type": "winding_selector_homotopy_consistency",
                        "assignments": [
                            {"cycle": "gamma_1", "homotopy_class": "a", "winding": 1},
                            {"cycle": "gamma_2", "homotopy_class": "a", "winding": 2},
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"winding_selector_homotopy_mismatch"})

    def test_winding_selector_orientation_reversal_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_winding_orientation",
                        "type": "winding_selector_orientation_reversal",
                        "pairs": [
                            {
                                "left_class": "a",
                                "right_class": "a_inv",
                                "left_winding": 1,
                                "right_winding": 1,
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"winding_selector_orientation_mismatch"})

    def test_winding_selector_additivity_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_winding_additivity",
                        "type": "winding_selector_additivity",
                        "relations": [
                            {
                                "left_class": "a",
                                "right_class": "b",
                                "composed_class": "ab",
                                "left_winding": 1,
                                "right_winding": 2,
                                "composed_winding": 4,
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"winding_selector_additivity_failed"})

    def test_winding_selector_no_calibrated_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_winding_source",
                        "type": "winding_selector_no_calibrated_input",
                        "candidate_sources": ["cycle_word_grammar_I", "hbar_obs"],
                        "forbidden_sources": ["hbar_obs", "G_N", "planck_units"],
                        "selector_status": "candidate",
                        "claims_physical_selector": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_winding_selector_forbidden_source"})

    def test_sector_role_registry_rejects_missing_role(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_sector_roles",
                        "type": "sector_role_registry",
                        "roles": [
                            "structural_selector",
                            "dimensional_anchor",
                            "dimensionless_coupling",
                            "bridge_assumption",
                            "derived_readout",
                            "experimental_gate",
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"sector_role_registry_incomplete"})

    def test_sector_role_assignment_partition_rejects_overlap(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_sector_assignment",
                        "type": "sector_role_assignment_partition",
                        "assignments": [
                            {"symbol": "calibrated_hbar_I", "role": "bridge_assumption"},
                            {"symbol": "calibrated_hbar_I", "role": "derived_readout"},
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"sector_role_assignment_overlap"})

    def test_dimensionful_anchor_policy_rejects_unanchored_derived_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_dimensionful_claim",
                        "type": "dimensionful_anchor_policy",
                        "entries": [
                            {
                                "symbol": "G_I",
                                "role": "dimensional_anchor",
                                "dimensionful": True,
                                "anchor_status": "target",
                                "claims_first_principles_output": True,
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"dimensionful_claim_without_anchor"})

    def test_dimensionless_coupling_policy_rejects_underived_selector_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_dimensionless_coupling",
                        "type": "dimensionless_coupling_policy",
                        "entries": [
                            {
                                "symbol": "alpha_em_I",
                                "role": "dimensionless_coupling",
                                "selector_status": "candidate",
                                "coupling_status": "target",
                                "claims_derived_coupling": True,
                                "calibrated_once": False,
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"dimensionless_coupling_without_selector"})

    def test_bridge_assumption_boundary_rejects_derived_relabel(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_bridge_claim",
                        "type": "bridge_assumption_boundary",
                        "entries": [
                            {
                                "symbol": "calibrated_G_anchor_I",
                                "role": "bridge_assumption",
                                "status": "bridge_assumption",
                                "claims_derived": True,
                            }
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"bridge_assumption_relabelled_derived"})

    def test_research_graph_contract_rejects_premature_complete_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_research_graph_contract",
                        "type": "research_graph_contract",
                        "surfaces": [
                            {
                                "surface": surface,
                                "status": "partial",
                                "evidence_refs": ["bad_research_graph_contract"],
                                "open_gap": "not yet first-class",
                            }
                            for surface in RESEARCH_GRAPH_CONTRACT_REQUIRED_SURFACES
                        ],
                        "expected_contract_status": "complete",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"research_graph_contract_status_mismatch"})

    def test_research_graph_contract_rejects_ungrounded_evidence_ref(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_research_graph_contract",
                        "type": "research_graph_contract",
                        "surfaces": [
                            {
                                "surface": surface,
                                "status": "partial",
                                "evidence_refs": (
                                    ["missing_graph_ref"]
                                    if surface == RESEARCH_GRAPH_CONTRACT_REQUIRED_SURFACES[0]
                                    else ["bad_research_graph_contract"]
                                ),
                                "open_gap": "not yet first-class",
                            }
                            for surface in RESEARCH_GRAPH_CONTRACT_REQUIRED_SURFACES
                        ],
                        "expected_contract_status": "partial",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"research_graph_contract_evidence_unresolved"})

    def test_phase_branch_additivity_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_phase_branch_sum",
                        "type": "phase_branch_additivity",
                        "theta_left": 0.2,
                        "theta_right": 0.3,
                        "theta_composed": 0.6,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_branch_additivity_failed"})

    def test_phase_branch_no_postfit_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_phase_branch_source",
                        "type": "phase_branch_no_postfit",
                        "candidate_sources": ["phase_branch_reconstruction_gate", "G_N"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "branch_status": "candidate",
                        "claims_physical_branch": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_phase_branch_forbidden_source"})

    def test_phase_cost_independence_rejects_phase_defined_cost(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_phase_cost",
                        "type": "phase_cost_independence",
                        "phase_defined_cost": True,
                        "claims_independent_cost": True,
                        "candidate_sources": ["phase_branch_reconstruction_gate"],
                        "forbidden_sources": ["G_N", "planck_units"],
                        "cost_status": "candidate",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_circular"})

    def test_mass_anchor_inertia_response_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_mass_inertia",
                        "type": "primitive_mass_anchor_inertia_response",
                        "impulse": 12.0,
                        "velocity_delta": 3.0,
                        "expected_mass": 5.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_mass_anchor_inertia_mismatch"})

    def test_mass_anchor_no_quantum_gravity_rejects_candidate_physical_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_mass_claim",
                        "type": "primitive_mass_anchor_no_quantum_gravity_input",
                        "candidate_sources": ["inertial_response"],
                        "forbidden_sources": ["hbar_obs", "G_N", "planck_units"],
                        "mass_status": "candidate",
                        "claims_physical_mass": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"physical_mass_claim_without_independent_standard"})

    def test_source_response_charge_normalization_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_source_charge_norm",
                        "type": "source_response_charge_normalization",
                        "stiffness_scale": 8.0,
                        "clock_strain_response": 0.5,
                        "geometry_factor": 2.0,
                        "expected_source_charge": 3.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"source_response_charge_normalization_mismatch"})

    def test_source_response_no_calibrated_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_source_charge_input",
                        "type": "source_response_no_calibrated_input",
                        "candidate_sources": ["inertial_response", "local_G_anchor_I"],
                        "forbidden_sources": ["G_N", "planck_units", "local_G_anchor_I"],
                        "source_charge_status": "candidate",
                        "claims_physical_source_charge": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_source_response_charge_forbidden_source"})

    def test_active_passive_inertial_equality_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_active_passive",
                        "type": "active_passive_inertial_equality",
                        "inertial_mass": 4.0,
                        "passive_charge": 4.0,
                        "active_charge": 5.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"active_passive_inertial_equality_mismatch"})

    def test_source_response_packet_universality_rejects_spread(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_source_charge_spread",
                        "type": "source_response_packet_universality",
                        "source_charges": [4.0, 4.1, 5.2],
                        "max_relative_spread": 0.05,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"source_response_packet_universality_failed"})

    def test_geometry_response_factor_freeze_rejects_false_freeze(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_geometry_freeze",
                        "type": "geometry_response_factor_freeze",
                        "D_S_values": [1.0, 1.001],
                        "z_values": [3.0, 3.01],
                        "q_V_values": [2.0, 2.0],
                        "ell0_values": [5.0, 5.0],
                        "max_relative_spread": 0.0001,
                        "declared_status": "frozen",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"geometry_response_factor_status_mismatch"})

    def test_geometry_response_no_gravity_anchor_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_geometry_input",
                        "type": "geometry_response_no_gravity_anchor",
                        "candidate_sources": ["radar_readout", "local_G_anchor_I"],
                        "forbidden_sources": ["G_N", "local_G_anchor_I"],
                        "geometry_status": "candidate",
                        "claims_physical_geometry": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_geometry_response_factor_forbidden_source"})

    def test_clock_vacuum_stiffness_from_source_response_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_stiffness_from_source",
                        "type": "clock_vacuum_stiffness_from_source_response",
                        "source_charge": 4.0,
                        "geometry_factor": 2.0,
                        "clock_strain_response": 0.5,
                        "expected_kappa": 12.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"clock_vacuum_stiffness_mismatch"})

    def test_clock_vacuum_stiffness_universality_rejects_spread(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_stiffness_spread",
                        "type": "clock_vacuum_stiffness_universality",
                        "kappa_values": [16.0, 16.1, 18.0],
                        "max_relative_spread": 0.02,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"clock_vacuum_stiffness_universality_failed"})

    def test_clock_vacuum_stiffness_no_calibrated_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_stiffness_input",
                        "type": "clock_vacuum_stiffness_no_calibrated_input",
                        "candidate_sources": ["source_response_charge_closure_I", "calibrated_G_anchor_I"],
                        "forbidden_sources": ["G_N", "calibrated_G_anchor_I", "local_G_anchor_I"],
                        "stiffness_status": "candidate",
                        "claims_physical_stiffness": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_clock_vacuum_stiffness_forbidden_source"})

    def test_G_symbolic_clock_strain_candidate_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_G_symbolic",
                        "type": "G_symbolic_clock_strain_candidate",
                        "c_value": 10.0,
                        "ell0_value": 5.0,
                        "dimension_factor": 3.0,
                        "kappa_value": 20.0,
                        "adjacency_factor": 6.0,
                        "volume_factor": 1.0,
                        "expected_G": 1200.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"G_symbolic_clock_strain_mismatch"})

    def test_G_candidate_no_calibrated_input_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_G_candidate_input",
                        "type": "G_candidate_no_calibrated_input",
                        "candidate_sources": [
                            "G_symbolic_clock_strain",
                            "local_G_anchor_I",
                        ],
                        "forbidden_sources": ["G_N", "calibrated_G_anchor_I", "local_G_anchor_I"],
                        "G_candidate_status": "candidate",
                        "claims_physical_G": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_G_candidate_forbidden_source"})

    def test_photon_dispersion_bound_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_photon_bound",
                        "type": "photon_dispersion_bound",
                        "alpha_abs": 0.125,
                        "omega_qg": 1.9750476834523637e35,
                        "convention_kappa": 1.0,
                        "expected_omega_min": 8.0e34,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"photon_dispersion_bound_mismatch"})

    def test_matter_wave_bound_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_matter_bound",
                        "type": "matter_wave_bound",
                        "c_value": 299792458.0,
                        "wave_number": 1.19e14,
                        "coefficient_abs": 1.0 / 12.0,
                        "phase_residual_bound": 0.1,
                        "expected_omega_min": 4.0e22,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"matter_wave_bound_mismatch"})

    def test_composite_omega_bound_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_composite_bound",
                        "type": "composite_omega_bound",
                        "omega_bounds": [6.98e34, 3.24e22],
                        "expected_omega_min": 3.24e22,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"composite_omega_bound_mismatch"})

    def test_ell0_tick_bound_rejects_tick_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_ell0_tick_bound",
                        "type": "ell0_tick_bound",
                        "c_value": 299792458.0,
                        "omega_lower_bound": 6.982848050679741e34,
                        "radar_steps": 1,
                        "expected_ell0_upper": 4.293269104872143e-27,
                        "expected_tick_upper": 2.0e-35,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"tick_upper_bound_mismatch"})

    def test_clock_redshift_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_clock_redshift",
                        "type": "clock_redshift",
                        "c_value": 299792458.0,
                        "potential_a": 9.80665,
                        "potential_b": 0.0,
                        "expected_fractional_shift": 2.0e-16,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"clock_redshift_mismatch"})

    def test_combined_clock_rate_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_combined_clock_rate",
                        "type": "combined_clock_rate",
                        "c_value": 299792458.0,
                        "potential": 100.0,
                        "speed": 1000.0,
                        "expected_rate": 1.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"combined_clock_rate_mismatch"})

    def test_point_mass_clock_field_rejects_acceleration_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_point_mass_clock",
                        "type": "newtonian_point_mass_clock_field",
                        "c_value": 299792458.0,
                        "g_value": 6.67430e-11,
                        "mass": 5.9722e24,
                        "radius": 6.371e6,
                        "expected_potential": -62565145.91115994,
                        "expected_acceleration": 9.7,
                        "expected_redshift_to_infinity": 6.961311310505493e-10,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"newtonian_point_mass_acceleration_mismatch"})

    def test_source_flux_gauss_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_source_flux",
                        "type": "source_flux_gauss",
                        "g_value": 6.67430e-11,
                        "mass": 5.9722e24,
                        "expected_flux": 5.0e15,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"source_flux_gauss_mismatch"})

    def test_ppn_light_bending_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_light_bending",
                        "type": "ppn_light_bending",
                        "c_value": 299792458.0,
                        "g_value": 6.67430e-11,
                        "mass": 1.98847e30,
                        "impact_parameter": 6.957e8,
                        "gamma_ppn": 1.0,
                        "expected_deflection": 7.0e-6,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ppn_light_bending_mismatch"})

    def test_clock_strain_variational_poisson_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_variational_poisson",
                        "type": "clock_strain_variational_poisson",
                        "alpha": 3.0,
                        "beta": 2.0,
                        "phi_values": [0.0, -1.0, 0.0],
                        "source_values": [0.0, 2.0, 0.0],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"clock_strain_variational_poisson_mismatch"})

    def test_source_law_coefficient_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_source_coefficient",
                        "type": "source_law_coefficient",
                        "c_value": 299792458.0,
                        "alpha": 1.0,
                        "beta": 1.0e-45,
                        "zeta": 1.0,
                        "expected_coefficient": 1.0e-10,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"source_law_coefficient_mismatch"})

    def test_ppn_gamma_from_potentials_rejects_slip(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_ppn_gamma",
                        "type": "ppn_gamma_from_potentials",
                        "phi_values": [1.0, 2.0, 3.0],
                        "psi_values": [1.0, 2.1, 3.0],
                        "expected_gamma": 1.0,
                        "max_slip_fraction": 1.0e-3,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ppn_gamma_slip_bound_exceeded"})

    def test_shapiro_delay_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_shapiro",
                        "type": "shapiro_delay",
                        "c_value": 299792458.0,
                        "g_value": 6.67430e-11,
                        "mass": 1.98847e30,
                        "emitter_radius": 1.495978707e11,
                        "receiver_radius": 1.495978707e11,
                        "impact_parameter": 6.957e8,
                        "gamma_ppn": 1.0,
                        "expected_delay": 1.0e-4,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"shapiro_delay_mismatch"})

    def test_ppn_perihelion_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_perihelion",
                        "type": "ppn_perihelion",
                        "c_value": 299792458.0,
                        "g_value": 6.67430e-11,
                        "mass": 1.98847e30,
                        "semi_major_axis": 5.790905e10,
                        "eccentricity": 0.205630,
                        "beta_ppn": 1.0,
                        "gamma_ppn": 1.0,
                        "expected_precession": 4.0e-7,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"ppn_perihelion_mismatch"})

    def test_slip_source_poisson_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_slip_source",
                        "type": "slip_source_poisson",
                        "coupling": 2.0,
                        "slip_values": [0.0, -1.0, 0.0],
                        "stress_values": [0.0, 2.0, 0.0],
                        "residual_values": [0.0, 0.0, 0.0],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"slip_source_poisson_mismatch"})

    def test_zero_stress_boundary_no_slip_rejects_nonzero_solution(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_no_slip",
                        "type": "zero_stress_boundary_no_slip",
                        "slip_values": [0.0, 0.01, 0.0],
                        "stress_values": [0.0, 0.0, 0.0],
                        "residual_values": [0.0, 0.0, 0.0],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"no_slip_solution_not_zero"})

    def test_source_continuity_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_continuity",
                        "type": "source_continuity",
                        "delta_t": 0.5,
                        "density_initial": [1.0, 2.0],
                        "density_final": [1.1, 1.8],
                        "flux_divergence": [-0.2, 0.2],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"source_continuity_mismatch"})

    def test_stress_tensor_decomposition_rejects_pressure_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_stress_decomposition",
                        "type": "stress_tensor_decomposition",
                        "stress_matrix": [[4.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]],
                        "expected_pressure": 1.0,
                        "expected_anisotropic": [[2.0, 0.0, 0.0], [0.0, -1.0, 0.0], [0.0, 0.0, -1.0]],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"stress_decomposition_pressure_mismatch"})

    def test_anisotropic_stress_norm_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_anisotropy_norm",
                        "type": "anisotropic_stress_norm",
                        "stress_matrix": [[2.0, 0.0, 0.0], [0.0, 2.0, 0.0], [0.0, 0.0, 2.0]],
                        "expected_norm": 0.1,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"anisotropic_stress_norm_mismatch"})

    def test_coarse_grained_anisotropy_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_coarse_anisotropy",
                        "type": "coarse_grained_anisotropy",
                        "weights": [0.5, 0.5],
                        "stress_tensors": [
                            [[3.0, 0.0, 0.0], [0.0, 0.0, 0.0], [0.0, 0.0, 0.0]],
                            [[0.0, 0.0, 0.0], [0.0, 3.0, 0.0], [0.0, 0.0, 0.0]],
                        ],
                        "expected_norm": 0.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"coarse_grained_anisotropy_mismatch"})

    def test_slip_source_bound_from_anisotropy_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_slip_bound",
                        "type": "slip_source_bound_from_anisotropy",
                        "coupling": 2.0,
                        "anisotropy_norm": 0.25,
                        "non_gravity_residual_norm": 0.1,
                        "expected_bound": 0.5,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"slip_source_bound_mismatch"})

    def test_scale_residual_bound_rejects_validated_excess(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_scale_bound",
                        "type": "scale_residual_bound",
                        "scales": [1.0, 10.0, 100000.0],
                        "residuals": [1.0e-6, 2.0e-4, 0.1],
                        "validated_max_scale": 10.0,
                        "validated_bound": 1.0e-5,
                        "expected_validated_max": 2.0e-4,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"validated_residual_bound_exceeded"})

    def test_scale_residual_activation_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_activation",
                        "type": "scale_residual_activation",
                        "amplitude": 1.0,
                        "transition_scale": 10000.0,
                        "exponent": 2.0,
                        "scales": [1.0, 100000.0],
                        "expected_residuals": [1.0e-8, 0.5],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"scale_residual_activation_mismatch"})

    def test_domain_no_refit_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_no_refit",
                        "type": "domain_no_refit",
                        "constants": [6.67430e-11, 6.70e-11],
                        "reference": 6.67430e-11,
                        "expected_max_fractional_mismatch": 0.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"domain_no_refit_mismatch"})

    def test_screened_transition_bound_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_transition",
                        "type": "screened_transition_bound",
                        "amplitude": 1.0,
                        "residual_bound": 1.0e-5,
                        "validated_scale": 10.0,
                        "exponent": 2.0,
                        "expected_transition_min": 3000.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_transition_bound_mismatch"})

    def test_screened_profile_prediction_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_profile",
                        "type": "screened_profile_prediction",
                        "amplitude": 1.0,
                        "transition_scale": 3162.26184874055,
                        "exponent": 2.0,
                        "scales": [1.0, 10.0],
                        "expected_residuals": [1.0e-7, 2.0e-5],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_profile_prediction_mismatch"})

    def test_residual_acceleration_output_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_acceleration_output",
                        "type": "residual_acceleration_output",
                        "g_value": 6.67430e-11,
                        "mass": 5.9722e24,
                        "radius": 6.371e6,
                        "residual_fraction": 2.0e-8,
                        "expected_newtonian_acceleration": 9.820302293385645,
                        "expected_residual_acceleration": 1.0e-7,
                        "expected_total_acceleration": 9.820302489791692,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"residual_acceleration_mismatch"})

    def test_residual_light_bending_output_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_light_output",
                        "type": "residual_light_bending_output",
                        "base_gr_deflection": 8.490267017584816e-6,
                        "gamma_residual": 2.0e-8,
                        "expected_deflection": 8.490267017584816e-6,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"residual_light_bending_mismatch"})

    def test_screened_observational_profile_rejects_solar_excess(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_solar_observation",
                        "type": "screened_observational_profile",
                        "amplitude": 1.0,
                        "transition_scale": 3162.26184874055,
                        "exponent": 2.0,
                        "solar_scale": 10.0,
                        "solar_bound": 1.0e-6,
                        "expected_solar_residual": 1.0e-5,
                        "galactic_scale": 100000.0,
                        "expected_galactic_residual": 0.9990010089810291,
                        "galactic_min": 0.1,
                        "galactic_max": 1.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_observation_solar_bound_exceeded"})

    def test_screened_observational_profile_rejects_galactic_range(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_galactic_observation",
                        "type": "screened_observational_profile",
                        "amplitude": 1.0,
                        "transition_scale": 3162.26184874055,
                        "exponent": 2.0,
                        "solar_scale": 10.0,
                        "solar_bound": 1.0e-5,
                        "expected_solar_residual": 1.0e-5,
                        "galactic_scale": 100000.0,
                        "expected_galactic_residual": 0.9990010089810291,
                        "galactic_min": 1.1,
                        "galactic_max": 2.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_observation_galactic_range_failed"})

    def test_sparc_baryonic_residual_point_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_sparc_point",
                        "type": "sparc_baryonic_residual_point",
                        "source_path": str(ROOT / "data/sparc/raw/Rotmod_LTG.zip"),
                        "source_sha256": "0a80cc90714828cc28b7dd57923576714d209f2490328c087c4a4ad607faf588",
                        "member_path": "DDO154_rotmod.dat",
                        "row_number": 10,
                        "upsilon_disk": 0.5,
                        "upsilon_bulge": 0.0,
                        "expected_radius_kpc": 4.94,
                        "expected_observed_velocity_km_s": 48.20,
                        "expected_gas_velocity_km_s": 16.93,
                        "expected_disk_velocity_km_s": 6.89,
                        "expected_bulge_velocity_km_s": 0.0,
                        "expected_observed_acceleration": 470.2914979757085,
                        "expected_baryonic_acceleration": 62.82610323886638,
                        "expected_missing_acceleration": 407.46539473684214,
                        "expected_residual_fraction": 0.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"sparc_residual_fraction_mismatch"})

    def test_sparc_residual_packet_rejects_vector_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_sparc_packet",
                        "type": "sparc_residual_packet",
                        "source_path": str(ROOT / "data/sparc/raw/Rotmod_LTG.zip"),
                        "source_sha256": "0a80cc90714828cc28b7dd57923576714d209f2490328c087c4a4ad607faf588",
                        "member_path": "DDO154_rotmod.dat",
                        "upsilon_disk": 0.5,
                        "upsilon_bulge": 0.0,
                        "expected_count": 12,
                        "expected_radius_min_kpc": 0.49,
                        "expected_radius_max_kpc": 5.92,
                        "expected_residual_fractions": [0.0] * 12,
                        "expected_min_residual": 1.1217605799746315,
                        "expected_max_residual": 6.842377551859201,
                        "expected_mean_residual": 4.581090117622583,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"sparc_packet_residual_vector_mismatch"})

    def test_screened_sparc_capacity_rejects_false_sufficiency_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_sparc_capacity",
                        "type": "screened_sparc_capacity",
                        "candidate_max_residual": 1.0,
                        "required_max_residual": 6.842377551859201,
                        "expected_capacity_ratio": 0.1461480300408564,
                        "declared_status": "sufficient",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_sparc_capacity_status_mismatch"})

    def test_screened_amplitude_lower_bound_rejects_false_status(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_amplitude_bound",
                        "type": "screened_amplitude_lower_bound",
                        "residual_fractions": [1.0, 2.0, 6.0],
                        "candidate_amplitude": 1.0,
                        "expected_lower_bound": 6.0,
                        "expected_shortfall": 5.0,
                        "declared_status": "satisfies_bound",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_amplitude_bound_status_mismatch"})

    def test_residual_no_postfit_provenance_rejects_false_predeclared_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_postfit_provenance",
                        "type": "residual_no_postfit_provenance",
                        "candidate_sources": ["kernel_route", "sparc_galaxy_residual_packet_I"],
                        "forbidden_sources": ["sparc_galaxy_residual_packet_I", "observed_acceleration"],
                        "declared_status": "predeclared",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"residual_postfit_status_mismatch"})

    def test_screened_profile_bound_status_rejects_false_compatibility_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_screened_status",
                        "type": "screened_profile_bound_status",
                        "amplitude": 6.842377551859201,
                        "transition_scale": 3162.26184874055,
                        "exponent": 2.0,
                        "validated_scale": 10.0,
                        "residual_bound": 1.0e-5,
                        "expected_residual": 6.842377551859202e-05,
                        "declared_status": "compatible",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_profile_bound_status_mismatch"})

    def test_screened_corridor_feasibility_rejects_false_open_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_corridor",
                        "type": "screened_corridor_feasibility",
                        "amplitude": 1.0,
                        "transition_scale": 8271.860462954632,
                        "exponent": 2.0,
                        "solar_scale": 10.0,
                        "solar_bound": 1.0e-5,
                        "required_amplitude": 6.842377551859201,
                        "galactic_scale": 100000.0,
                        "galactic_activation_min": 0.99,
                        "expected_solar_residual": 1.461480300408564e-06,
                        "expected_galactic_residual": 0.993204132272963,
                        "expected_activation_fraction": 0.993204132272963,
                        "declared_status": "open",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_corridor_status_mismatch"})

    def test_residual_fit_claim_status_rejects_fit_without_map(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_fit_claim",
                        "type": "residual_fit_claim_status",
                        "profile_source_status": "predeclared",
                        "radius_scale_map_status": "missing",
                        "heldout_validation_status": "missing",
                        "declared_status": "candidate_fit",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"residual_fit_claim_status_mismatch"})

    def test_screened_radius_scale_prediction_rejects_false_acceptance(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_radius_map",
                        "type": "screened_radius_scale_prediction",
                        "amplitude": 6.842377551859201,
                        "transition_scale": 8271.860462954632,
                        "exponent": 2.0,
                        "radii_kpc": [0.49, 0.99],
                        "observed_residuals": [1.1217605799746315, 1.8888654286905768],
                        "anchor_radius_kpc": 5.92,
                        "anchor_scale": 100000.0,
                        "expected_map_factor": 16891.891891891893,
                        "expected_predicted_residuals": [3.4233249665711125, 5.497345941121766],
                        "expected_rms_error": 3.026411260407688,
                        "expected_max_abs_error": 3.6084805124311896,
                        "expected_mean_abs_error": 2.9550224495138355,
                        "acceptance_max_abs_error": 1.0,
                        "declared_status": "accepted",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_radius_map_status_mismatch"})

    def test_screened_baryonic_acceleration_map_rejects_false_acceptance(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_baryonic_map",
                        "type": "screened_baryonic_acceleration_map",
                        "amplitude": 6.842377551859201,
                        "transition_scale": 8271.860462954632,
                        "screened_exponent": 2.0,
                        "baryonic_accelerations": [183.17479591836735, 163.13419191919195],
                        "observed_residuals": [1.1217605799746315, 1.8888654286905768],
                        "anchor_baryonic_acceleration": 44.62895270270271,
                        "anchor_scale": 100000.0,
                        "map_exponent": 2.0,
                        "expected_scales": [5936.110247965054, 7484.165780173169],
                        "expected_predicted_residuals": [2.325922392391693, 3.0799690228066243],
                        "expected_rms_error": 1.197650500438193,
                        "expected_max_abs_error": 1.2041618124170617,
                        "expected_mean_abs_error": 1.1976327032665546,
                        "acceptance_max_abs_error": 1.0,
                        "declared_status": "accepted",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_baryonic_map_status_mismatch"})

    def test_screened_baryonic_exponent_scan_rejects_false_all_rejected_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_baryonic_exponent_scan",
                        "type": "screened_baryonic_exponent_scan",
                        "amplitude": 6.842377551859201,
                        "transition_scale": 8271.860462954632,
                        "screened_exponent": 2.0,
                        "baryonic_accelerations": [183.17479591836735, 163.13419191919195],
                        "observed_residuals": [1.1217605799746315, 1.8888654286905768],
                        "anchor_baryonic_acceleration": 44.62895270270271,
                        "anchor_scale": 100000.0,
                        "map_exponents": [2.0, 2.5],
                        "expected_rms_errors": [1.1976505004381932, 0.5169482489546624],
                        "expected_max_abs_errors": [1.204161812417062, 0.6368915532923927],
                        "expected_mean_abs_errors": [1.1976327032665548, 0.49791731585185045],
                        "acceptance_max_abs_error": 1.0,
                        "expected_best_exponent": 2.5,
                        "expected_best_max_abs_error": 0.6368915532923927,
                        "declared_status": "all_rejected",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_baryonic_exponent_scan_status_mismatch"})

    def test_screened_baryonic_transfer_rejects_false_acceptance(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_baryonic_transfer",
                        "type": "screened_baryonic_exponent_transfer",
                        "source_path": str(ROOT / "data/sparc/raw/Rotmod_LTG.zip"),
                        "source_sha256": "0a80cc90714828cc28b7dd57923576714d209f2490328c087c4a4ad607faf588",
                        "selection_start_after": "DDO154_rotmod.dat",
                        "heldout_count": 1,
                        "min_row_count": 8,
                        "expected_member_paths": ["DDO161_rotmod.dat"],
                        "upsilon_disk": 0.5,
                        "upsilon_bulge": 0.0,
                        "amplitude": 6.842377551859201,
                        "transition_scale": 8271.860462954632,
                        "screened_exponent": 2.0,
                        "map_exponent": 2.5,
                        "anchor_scale": 100000.0,
                        "expected_row_counts": [31],
                        "expected_rms_errors": [2.167412481319462],
                        "expected_max_abs_errors": [3.472139558653409],
                        "expected_mean_abs_errors": [1.7492127149324677],
                        "expected_aggregate_count": 31,
                        "expected_aggregate_rms_error": 2.167412481319462,
                        "expected_aggregate_max_abs_error": 3.472139558653409,
                        "expected_aggregate_mean_abs_error": 1.7492127149324677,
                        "acceptance_max_abs_error": 1.0,
                        "declared_status": "accepted",
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"screened_transfer_validation_status_mismatch"})

    def test_primitive_tick_clock_count_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_tick_count",
                        "type": "primitive_tick_clock_count",
                        "clock_interval": 12.0,
                        "step_count": 4,
                        "expected_tick": 4.0,
                        "candidate_sources": ["clock_interval_readout", "step_count_readout"],
                        "forbidden_sources": ["hbar_obs", "G_N", "planck_units"],
                        "tick_status": "candidate",
                        "claims_physical_tick": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_tick_clock_count_mismatch"})

    def test_primitive_tick_radar_rejects_candidate_physical_claim(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_tick_claim",
                        "type": "primitive_tick_radar_consistency",
                        "radar_half_time": 12.0,
                        "step_count": 4,
                        "expected_tick": 3.0,
                        "candidate_sources": ["radar_half_time", "step_count_readout"],
                        "forbidden_sources": ["hbar_obs", "G_N", "planck_units"],
                        "tick_status": "candidate",
                        "claims_physical_tick": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"physical_tick_claim_without_independent_standard"})

    def test_primitive_tick_reparam_rejects_rate_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_tick_reparam",
                        "type": "primitive_tick_reparam_invariance",
                        "rates_before": [2.0, 4.0, 6.0],
                        "rates_after": [1.0, 2.0, 4.0],
                        "reparam_factor": 2.0,
                        "reference_index": 0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_tick_reparam_rate_mismatch"})

    def test_primitive_tick_universality_rejects_spread(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_tick_universality",
                        "type": "primitive_tick_clock_universality",
                        "epsilon": 0.01,
                        "tick_estimates": [3.0, 3.2, 3.0],
                        "candidate_sources": ["clock_a", "clock_b", "clock_c"],
                        "forbidden_sources": ["hbar_obs", "G_N", "planck_units"],
                        "tick_status": "candidate",
                        "claims_physical_tick": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_tick_universality_failed"})

    def test_primitive_work_balance_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_work_balance",
                        "type": "primitive_work_balance",
                        "work_inputs": [5.0, 2.0],
                        "work_outputs": [1.0],
                        "expected_work_unit": 7.0,
                        "candidate_sources": ["kernel_strain_work_balance"],
                        "forbidden_sources": ["hbar_obs", "E_equals_hbar_omega"],
                        "work_unit_status": "candidate",
                        "claims_physical_work": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_work_balance_mismatch"})

    def test_primitive_work_no_quantum_energy_rejects_forbidden_source(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_work_source",
                        "type": "primitive_work_no_quantum_energy",
                        "candidate_sources": ["kernel_strain_work_balance", "E_equals_hbar_omega"],
                        "forbidden_sources": ["hbar_obs", "E_equals_hbar_omega"],
                        "work_unit_status": "candidate",
                        "claims_physical_work": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_work_forbidden_source"})

    def test_primitive_work_coarse_grain_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_work_coarse_grain",
                        "type": "primitive_work_coarse_grain_balance",
                        "fine_inputs": [2.0, 4.0],
                        "fine_outputs": [1.0],
                        "coarse_inputs": [4.0],
                        "coarse_outputs": [],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_work_coarse_grain_mismatch"})

    def test_primitive_work_universality_rejects_spread(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_work_universality",
                        "type": "primitive_work_sector_universality",
                        "epsilon": 0.01,
                        "work_units": [6.0, 6.4, 6.0],
                        "candidate_sources": ["sector_a", "sector_b", "sector_c"],
                        "forbidden_sources": ["hbar_obs", "E_equals_hbar_omega"],
                        "work_unit_status": "candidate",
                        "claims_physical_work": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"primitive_work_universality_failed"})

    def test_primitive_work_dimensional_obstruction_rejects_false_clearance(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_dimension_clearance",
                        "type": "primitive_work_dimensional_obstruction",
                        "target_dimension": {"M": 1, "L": 2, "T": -2},
                        "source_dimensions": [
                            {"id": "dimensionless_cost", "dimension": {}},
                            {"id": "c_I", "dimension": {"L": 1, "T": -1}},
                            {"id": "ell0", "dimension": {"L": 1}},
                            {"id": "primitive_tick_I", "dimension": {"T": 1}},
                        ],
                        "expected_obstructed": False,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"dimension_span_obstruction_mismatch"})

    def test_hbar_known_gate_holdout_rejects_bad_energy(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_hbar_holdout",
                        "type": "hbar_known_gate_holdout",
                        "hbar_estimate": 1.0,
                        "frequency_pairs": [{"omega": 2.0, "energy": 3.0}],
                        "momentum_pairs": [{"k": 3.0, "p": 3.0}],
                        "phase_pairs": [{"action": 5.0, "phase": 5.0}],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"hbar_energy_holdout_mismatch"})

    def test_pointer_sector_stability_rejects_large_overlap(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_pointer_overlap",
                        "type": "pointer_sector_stability",
                        "pointer_kernel": [[1.0, 0.2], [0.2, 1.0]],
                        "max_offdiag": 0.05,
                        "expected_stable": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"pointer_sector_stability_mismatch"})

    def test_premeasurement_decoherence_rejects_residual_coherence(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_residual_coherence",
                        "type": "premeasurement_decoherence",
                        "amplitudes": [0.6, 0.8],
                        "environment_kernel": [[1.0, 0.5], [0.5, 1.0]],
                        "expected_probabilities": [0.36, 0.64],
                        "max_residual_coherence": 0.01,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"premeasurement_residual_coherence"})

    def test_recoverability_loss_rejects_bad_lambda(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_recoverability_loss",
                        "type": "recoverability_loss",
                        "observed_visibility": 0.1,
                        "environment_recoverable_visibility": 0.9,
                        "expected_lambda": 1.0,
                        "facticity_threshold": 2.0,
                        "expected_facticity": True,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"recoverability_loss_mismatch"})

    def test_probability_context_rejects_large_offdiagonal(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_context",
                        "type": "probability_admissible_context",
                        "delta": 0.05,
                        "weights": [0.7071067811865476, 0.7071067811865476],
                        "gamma": [[1.0, 0.8], [0.8, 1.0]],
                        "events": [[0], [1]],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"context_not_probability_admissible"})

    def test_phase_cost_family_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_phase_cost",
                        "type": "relative_phase_cost_family",
                        "epsilon": 0.01,
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.4,
                                "cost": 2.0,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.9,
                                "cost": 3.0,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_phase_cost_family_rejects_duplicate_active_cycle(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_duplicate",
                        "type": "relative_phase_cost_family",
                        "epsilon": 0.01,
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.4,
                                "cost": 2.0,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "b", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.6,
                                "cost": 3.0,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"duplicate_active_cycle"})

    def test_diagonal_kernel_strain_cost_mismatch_is_reported(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_kernel_cost",
                        "type": "diagonal_kernel_strain_cost",
                        "G0_diag": [1.0, 1.0],
                        "G1_diag": [4.0, 1.0],
                        "alignment": [0, 1],
                        "expected_cost": 0.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"kernel_strain_cost_mismatch"})

    def test_cycle_cost_sum_mismatch_is_reported(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_cycle_sum",
                        "type": "cycle_cost_sum",
                        "edge_costs": [
                            {"from": "a", "to": "b", "cost": 1.0},
                            {"from": "b", "to": "a", "cost": 1.0},
                        ],
                        "cycles": [
                            {"id": "gamma", "word": ["a", "b", "a"], "expected_cost": 3.0}
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"cycle_cost_mismatch"})

    def test_phase_cost_from_edges_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_phase_cost_from_edges",
                        "type": "relative_phase_cost_from_edges",
                        "epsilon": 0.01,
                        "edge_costs": [
                            {"from": "a", "to": "b", "cost": 1.0},
                            {"from": "b", "to": "a", "cost": 1.0},
                            {"from": "a", "to": "c", "cost": 1.5},
                            {"from": "c", "to": "a", "cost": 1.5},
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.4,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.9,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_phase_cost_from_edges_rejects_missing_edge_cost(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_missing_edge_cost",
                        "type": "relative_phase_cost_from_edges",
                        "epsilon": 0.01,
                        "edge_costs": [
                            {"from": "a", "to": "b", "cost": 1.0},
                            {"from": "b", "to": "a", "cost": 1.0},
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.4,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.6,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_phase_cost_from_kernel_edges_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_kernel_phase_cost",
                        "type": "relative_phase_cost_from_kernel_edges",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.04140936770181867,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.12,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_phase_cost_from_kernel_edges_rejects_invalid_alignment(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_kernel_alignment",
                        "type": "relative_phase_cost_from_kernel_edges",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 0],
                            }
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.04140936770181867,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "b", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "theta": 0.04140936770181867,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_phase_cost_from_kernel_holonomy_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_kernel_holonomy_phase_cost",
                        "type": "relative_phase_cost_from_kernel_holonomy",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "phase_edges": [
                            {"from": "a", "to": "b", "phase": 0.020704683850909334},
                            {"from": "b", "to": "a", "phase": 0.020704683850909334},
                            {"from": "a", "to": "c", "phase": 0.04299382106643289},
                            {"from": "c", "to": "a", "phase": 0.07},
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_phase_cost_from_kernel_holonomy_rejects_missing_phase_edge(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_missing_phase_edge",
                        "type": "relative_phase_cost_from_kernel_holonomy",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "phase_edges": [
                            {"from": "a", "to": "b", "phase": 0.020704683850909334}
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "b", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_phase_cost_from_kernel_unit_holonomy_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_kernel_unit_holonomy_phase_cost",
                        "type": "relative_phase_cost_from_kernel_unit_holonomy",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "unit_holonomy": {
                                    "re": 0.9991427546395419,
                                    "im": 0.04139753436266696,
                                },
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "unit_holonomy": {
                                    "re": 0.9928086358538663,
                                    "im": 0.11971220728891936,
                                },
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_phase_cost_from_kernel_unit_holonomy_rejects_nonunit_holonomy(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_nonunit_holonomy",
                        "type": "relative_phase_cost_from_kernel_unit_holonomy",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "unit_holonomy": {"re": 2.0, "im": 0.0},
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "b", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                                "unit_holonomy": {"re": 1.0, "im": 0.0},
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_phase_cost_from_kernel_unit_edges_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_kernel_unit_edge_phase_cost",
                        "type": "relative_phase_cost_from_kernel_unit_edges",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "unit_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "unit_transfer": {
                                    "re": 0.9997856656902873,
                                    "im": 0.020703204588397774,
                                },
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "unit_transfer": {
                                    "re": 0.9997856656902873,
                                    "im": 0.020703204588397774,
                                },
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "unit_transfer": {
                                    "re": 0.9990759080344632,
                                    "im": 0.04298057683550604,
                                },
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "unit_transfer": {
                                    "re": 0.9928086358538663,
                                    "im": 0.11971220728891936,
                                },
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_phase_cost_from_kernel_unit_edges_rejects_nonunit_transfer(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_nonunit_transfer",
                        "type": "relative_phase_cost_from_kernel_unit_edges",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "unit_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "unit_transfer": {"re": 2.0, "im": 0.0},
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "unit_transfer": {"re": 1.0, "im": 0.0},
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "b", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_phase_cost_from_kernel_transfer_elements_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_transfer_element_phase_cost",
                        "type": "relative_phase_cost_from_kernel_transfer_elements",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "transfer_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "transfer": {
                                    "re": 0.7998285325522299,
                                    "im": 0.01656256367071822,
                                },
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "transfer": {
                                    "re": 0.7998285325522299,
                                    "im": 0.01656256367071822,
                                },
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "transfer": {
                                    "re": 0.6993531356241243,
                                    "im": 0.030086403784854224,
                                },
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "transfer": {
                                    "re": 0.6950,
                                    "im": 0.0830,
                                },
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_phase_cost_from_kernel_transfer_elements_rejects_noncontraction(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_noncontraction_transfer",
                        "type": "relative_phase_cost_from_kernel_transfer_elements",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "transfer_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "transfer": {"re": 2.0, "im": 0.0},
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "transfer": {"re": 1.0, "im": 0.0},
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "b", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_phase_cost_from_kernel_transfer_blocks_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_transfer_block_phase_cost",
                        "type": "relative_phase_cost_from_kernel_transfer_blocks",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "transfer_blocks": [
                            {
                                "from": "a",
                                "to": "b",
                                "block": [
                                    [
                                        {
                                            "re": 0.7998285325522299,
                                            "im": 0.01656256367071822,
                                        },
                                        0.0,
                                    ],
                                    [0.0, 0.5],
                                ],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "block": [
                                    [
                                        {
                                            "re": 0.7998285325522299,
                                            "im": 0.01656256367071822,
                                        },
                                        0.0,
                                    ],
                                    [0.0, 0.5],
                                ],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "block": [
                                    [
                                        {
                                            "re": 0.6993531356241243,
                                            "im": 0.030086403784854224,
                                        },
                                        0.0,
                                    ],
                                    [0.0, 0.4],
                                ],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "block": [
                                    [{"re": 0.6950, "im": 0.0830}, 0.0],
                                    [0.0, 0.4],
                                ],
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_phase_cost_from_kernel_transfer_blocks_rejects_noncontraction(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_transfer_block_contraction",
                        "type": "relative_phase_cost_from_kernel_transfer_blocks",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "transfer_blocks": [
                            {
                                "from": "a",
                                "to": "b",
                                "block": [[2.0, 0.0], [0.0, 1.0]],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "block": [[1.0, 0.0], [0.0, 1.0]],
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "b", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_phase_cost_from_kernel_block_kernels_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_block_kernel_phase_cost",
                        "type": "relative_phase_cost_from_kernel_block_kernels",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "block_kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0": [[1.0]],
                                "G1": [[1.0]],
                                "X": [[{"re": 0.7998285325522299, "im": 0.01656256367071822}]],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0": [[1.0]],
                                "G1": [[1.0]],
                                "X": [[{"re": 0.7998285325522299, "im": 0.01656256367071822}]],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0": [[1.0]],
                                "G1": [[1.0]],
                                "X": [[{"re": 0.6993531356241243, "im": 0.030086403784854224}]],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0": [[1.0]],
                                "G1": [[1.0]],
                                "X": [[{"re": 0.6950, "im": 0.0830}]],
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_phase_cost_from_kernel_block_kernels_rejects_non_psd_block(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_block_kernel_psd",
                        "type": "relative_phase_cost_from_kernel_block_kernels",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "block_kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0": [[1.0]],
                                "G1": [[1.0]],
                                "X": [[2.0]],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0": [[1.0]],
                                "G1": [[1.0]],
                                "X": [[1.0]],
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "b", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_phase_cost_from_kernel_normalized_blocks_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_normalized_block_phase_cost",
                        "type": "relative_phase_cost_from_kernel_normalized_blocks",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "normalized_block_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [2.0],
                                "G1_diag": [5.0],
                                "X": [[{"re": 2.5292799004551743, "im": 0.052375425091028625}]],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [2.0],
                                "G1_diag": [5.0],
                                "X": [[{"re": 2.5292799004551743, "im": 0.052375425091028625}]],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0_diag": [2.0],
                                "G1_diag": [5.0],
                                "X": [[{"re": 2.211548797352875, "im": 0.0951415625636499}]],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0_diag": [2.0],
                                "G1_diag": [5.0],
                                "X": [[{"re": 2.1976755989880474, "im": 0.26499426713143714}]],
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_phase_cost_from_kernel_normalized_blocks_rejects_non_psd_block(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_normalized_block_psd",
                        "type": "relative_phase_cost_from_kernel_normalized_blocks",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "normalized_block_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [2.0],
                                "G1_diag": [5.0],
                                "X": [[8.0]],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [2.0],
                                "G1_diag": [5.0],
                                "X": [[2.0]],
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "b", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_phase_cost_from_kernel_spectral_blocks_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_spectral_block_phase_cost",
                        "type": "relative_phase_cost_from_kernel_spectral_blocks",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [9.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "spectral_block_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0": [[2.0, 0.4], [0.4, 3.0]],
                                "G1": [[2.0, 0.4], [0.4, 3.0]],
                                "X": [
                                    [
                                        {
                                            "re": 1.599914263979032,
                                            "im": 0.016563451223469094,
                                        },
                                        {
                                            "re": 0.3199828527958064,
                                            "im": 0.003312690244693819,
                                        },
                                    ],
                                    [
                                        {
                                            "re": 0.3199828527958064,
                                            "im": 0.003312690244693819,
                                        },
                                        {
                                            "re": 2.399871395968548,
                                            "im": 0.02484517683520364,
                                        },
                                    ],
                                ],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0": [[2.0, 0.4], [0.4, 3.0]],
                                "G1": [[2.0, 0.4], [0.4, 3.0]],
                                "X": [
                                    [
                                        {
                                            "re": 1.599914263979032,
                                            "im": 0.016563451223469094,
                                        },
                                        {
                                            "re": 0.3199828527958064,
                                            "im": 0.003312690244693819,
                                        },
                                    ],
                                    [
                                        {
                                            "re": 0.3199828527958064,
                                            "im": 0.003312690244693819,
                                        },
                                        {
                                            "re": 2.399871395968548,
                                            "im": 0.02484517683520364,
                                        },
                                    ],
                                ],
                            },
                            {
                                "from": "a",
                                "to": "c",
                                "G0": [[2.0, 0.4], [0.4, 3.0]],
                                "G1": [[2.0, 0.4], [0.4, 3.0]],
                                "X": [
                                    [
                                        {
                                            "re": 1.3996765304432928,
                                            "im": 0.03009335684542467,
                                        },
                                        {
                                            "re": 0.2799353060886586,
                                            "im": 0.006018671369084934,
                                        },
                                    ],
                                    [
                                        {
                                            "re": 0.2799353060886586,
                                            "im": 0.006018671369084934,
                                        },
                                        {
                                            "re": 2.0995147956649394,
                                            "im": 0.04514003526813701,
                                        },
                                    ],
                                ],
                            },
                            {
                                "from": "c",
                                "to": "a",
                                "G0": [[2.0, 0.4], [0.4, 3.0]],
                                "G1": [[2.0, 0.4], [0.4, 3.0]],
                                "X": [
                                    [
                                        {
                                            "re": 1.3974807559092859,
                                            "im": 0.08394960907122243,
                                        },
                                        {
                                            "re": 0.27949615118185717,
                                            "im": 0.016789921814244487,
                                        },
                                    ],
                                    [
                                        {
                                            "re": 0.27949615118185717,
                                            "im": 0.016789921814244487,
                                        },
                                        {
                                            "re": 2.0962211338639287,
                                            "im": 0.12592441360683365,
                                        },
                                    ],
                                ],
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_phase_cost_from_kernel_spectral_blocks_rejects_singular_support(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_spectral_singular_support",
                        "type": "relative_phase_cost_from_kernel_spectral_blocks",
                        "epsilon": 0.01,
                        "kernel_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0_diag": [1.0, 1.0],
                                "G1_diag": [4.0, 1.0],
                                "alignment": [0, 1],
                            },
                        ],
                        "spectral_block_edges": [
                            {
                                "from": "a",
                                "to": "b",
                                "G0": [[1.0, 0.0], [0.0, 0.0]],
                                "G1": [[1.0, 0.0], [0.0, 1.0]],
                                "X": [[0.5, 0.0], [0.0, 0.0]],
                            },
                            {
                                "from": "b",
                                "to": "a",
                                "G0": [[1.0, 0.0], [0.0, 1.0]],
                                "G1": [[1.0, 0.0], [0.0, 1.0]],
                                "X": [[0.5, 0.0], [0.0, 0.5]],
                            },
                        ],
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "b", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_spectral_kernel_strain_cost_rejects_mismatch(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_spectral_cost",
                        "type": "spectral_kernel_strain_cost",
                        "tolerance": 1.0e-10,
                        "G0": [[2.0, 0.4], [0.4, 3.0]],
                        "G1": [[4.0, 0.7], [0.7, 1.6]],
                        "X": spectral_cost_phase_edges(False)[0]["X"],
                        "expected_cost": 0.0,
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"kernel_strain_cost_mismatch"})

    def test_phase_cost_from_spectral_kernel_blocks_rejects_failed_validation(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_full_spectral_phase_cost",
                        "type": "relative_phase_cost_from_spectral_kernel_blocks",
                        "tolerance": 1.0e-10,
                        "epsilon": 0.01,
                        "spectral_block_edges": spectral_cost_phase_edges(True),
                        "cycles": [
                            {
                                "id": "gamma_cal",
                                "word": ["a", "b", "a"],
                                "role": "calibration",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                            {
                                "id": "gamma_val",
                                "word": ["a", "c", "a"],
                                "role": "validation",
                                "class": "small",
                                "branch_source": "principal",
                                "admissible": True,
                            },
                        ],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"phase_cost_validation_failed"})

    def test_spectral_kernel_diagonal_limit_rejects_bad_alignment(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_diagonal_limit",
                        "type": "spectral_kernel_diagonal_limit",
                        "tolerance": 1.0e-10,
                        "G0_diag": [1.0, 1.0],
                        "G1_diag": [4.0, 1.0],
                        "alignment": [0, 0],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def test_spectral_kernel_readout_covariance_rejects_nonunitary_basis(self) -> None:
        manifest = parse_manifest(
            {
                "symbols": {},
                "equations": [],
                "derivations": [],
                "forbidden_paths": [],
                "finite_gates": [
                    {
                        "id": "bad_covariance_basis",
                        "type": "spectral_kernel_readout_covariance",
                        "tolerance": 1.0e-10,
                        "G0": [[2.0, 0.4], [0.4, 3.0]],
                        "G1": [[4.0, 0.7], [0.7, 1.6]],
                        "X": spectral_cost_phase_edges(False)[0]["X"],
                        "U0": [[1.0, 0.0], [0.0, 1.0]],
                        "U1": [[1.0, 0.2], [0.0, 1.0]],
                    }
                ],
            }
        )
        report = verify_manifest(manifest)
        self.assertIssueCodes(report, {"invalid_finite_gate"})

    def assertIssueCodes(self, report: VerificationReport, expected: set[str]) -> None:
        codes = {issue.code for issue in report.issues}
        self.assertTrue(expected.issubset(codes), codes)


def parse_manifest_text(path: Path) -> Manifest:
    return load_manifest(path)


def qm_experiment_primitives() -> dict[str, str]:
    return {primitive: f"{primitive} description" for primitive in QM_EXPERIMENT_REQUIRED_PRIMITIVES}


def qm_experiment(
    *,
    identifier: str = "test_qm_experiment",
    status: str = "idt_language_description",
    idt_primitives: dict[str, str] | None = None,
    finite_gates: list[str] | None = None,
    proposed_gates: list[str] | None = None,
) -> dict[str, object]:
    return {
        "id": identifier,
        "title": "Test QM experiment",
        "status": status,
        "standard_result": "known finite QM result",
        "idt_primitives": qm_experiment_primitives() if idt_primitives is None else idt_primitives,
        "stable_invariant": "context-indexed invariant",
        "finite_gates": [] if finite_gates is None else finite_gates,
        "proposed_gates": [] if proposed_gates is None else proposed_gates,
        "claim_boundary": "language coverage only; not full QM derivation",
    }


def qm_universal_pattern_operations() -> dict[str, str]:
    return {operation: f"{operation} operation" for operation in QM_UNIVERSAL_PATTERN_REQUIRED_OPERATIONS}


def qm_universal_pattern(
    *,
    identifier: str = "test_qm_universal_pattern",
    experiments: list[str] | None = None,
    finite_gates: list[str] | None = None,
    operations: dict[str, str] | None = None,
) -> dict[str, object]:
    return {
        "id": identifier,
        "title": "Test QM universal pattern",
        "mechanism": "shared finite context mechanism",
        "experiments": ["test_qm_experiment"] if experiments is None else experiments,
        "finite_gates": [] if finite_gates is None else finite_gates,
        "operations": qm_universal_pattern_operations() if operations is None else operations,
        "compiler_target": "compile this family into a shared QM bench primitive",
        "claim_boundary": "pattern audit only; not full QM derivation",
    }


def qm_core_proof_obligation(
    *,
    identifier: str = "finite_operational_core",
    status: str = "target",
    depends_on: list[str] | None = None,
    evidence_refs: list[str] | None = None,
) -> dict[str, object]:
    return {
        "id": identifier,
        "title": "Test QM core proof obligation",
        "status": status,
        "scope": "finite_core",
        "depends_on": [] if depends_on is None else depends_on,
        "evidence_refs": [] if evidence_refs is None else evidence_refs,
        "open_gap": "remaining derivation gap",
        "claim_boundary": "proof obligation only; not a closed QM derivation",
    }


def qm_foundation_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        "full_QM_I": {"status": resolved_statuses.get("full_QM_I", "target"), "dimension": {}}
    }
    for symbol in QM_FOUNDATION_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def qm_single_pass_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        QM_SINGLE_PASS_TARGET: {
            "status": resolved_statuses.get(QM_SINGLE_PASS_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in QM_SINGLE_PASS_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def calibrated_qm_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        CALIBRATED_QM_TARGET: {
            "status": resolved_statuses.get(CALIBRATED_QM_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in CALIBRATED_QM_REQUIRED_SYMBOLS:
        default_status = "bridge_assumption" if symbol == "calibrated_hbar_I" else "derived_conditional"
        symbols[symbol] = {"status": resolved_statuses.get(symbol, default_status), "dimension": {}}
    return symbols


def hbar_action_standard_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        HBAR_ACTION_STANDARD_TARGET: {
            "status": resolved_statuses.get(HBAR_ACTION_STANDARD_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in HBAR_ACTION_STANDARD_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def ell0_closure_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        ELL0_CLOSURE_TARGET: {
            "status": resolved_statuses.get(ELL0_CLOSURE_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in ELL0_CLOSURE_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def clock_vacuum_pole_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        CLOCK_VACUUM_POLE_TARGET: {
            "status": resolved_statuses.get(CLOCK_VACUUM_POLE_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in CLOCK_VACUUM_POLE_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def spectral_primitive_reduction_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        SPECTRAL_PRIMITIVE_REDUCTION_TARGET: {
            "status": resolved_statuses.get(SPECTRAL_PRIMITIVE_REDUCTION_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in SPECTRAL_PRIMITIVE_REDUCTION_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def cross_update_contraction_selection_symbols(
    statuses: dict[str, str] | None = None,
) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        CROSS_UPDATE_CONTRACTION_SELECTION_TARGET: {
            "status": resolved_statuses.get(CROSS_UPDATE_CONTRACTION_SELECTION_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in CROSS_UPDATE_CONTRACTION_SELECTION_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def fixed_point_step_invariant_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        FIXED_POINT_STEP_INVARIANT_TARGET: {
            "status": resolved_statuses.get(FIXED_POINT_STEP_INVARIANT_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in FIXED_POINT_STEP_INVARIANT_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def primitive_transition_phase_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        PRIMITIVE_TRANSITION_PHASE_TARGET: {
            "status": resolved_statuses.get(PRIMITIVE_TRANSITION_PHASE_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in PRIMITIVE_TRANSITION_PHASE_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def non_exact_holonomy_source_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        NON_EXACT_HOLONOMY_SOURCE_TARGET: {
            "status": resolved_statuses.get(NON_EXACT_HOLONOMY_SOURCE_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in NON_EXACT_HOLONOMY_SOURCE_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def primitive_holonomy_source_selector_symbols(
    statuses: dict[str, str] | None = None,
) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_TARGET: {
            "status": resolved_statuses.get(PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in PRIMITIVE_HOLONOMY_SOURCE_SELECTOR_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def primitive_topology_winding_selector_symbols(
    statuses: dict[str, str] | None = None,
) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_TARGET: {
            "status": resolved_statuses.get(PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in PRIMITIVE_TOPOLOGY_WINDING_SELECTOR_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def sector_role_taxonomy_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        SECTOR_ROLE_TAXONOMY_TARGET: {
            "status": resolved_statuses.get(SECTOR_ROLE_TAXONOMY_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in SECTOR_ROLE_TAXONOMY_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def ell0_emergence_clearance_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        ELL0_EMERGENCE_CLEARANCE_TARGET: {
            "status": resolved_statuses.get(ELL0_EMERGENCE_CLEARANCE_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in ELL0_EMERGENCE_CLEARANCE_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def ell0_physical_candidate_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        ELL0_PHYSICAL_CANDIDATE_TARGET: {
            "status": resolved_statuses.get(ELL0_PHYSICAL_CANDIDATE_TARGET, "target"),
            "dimension": {},
        },
        "ell0": {"status": resolved_statuses.get("ell0", "target"), "dimension": {}},
    }
    for symbol in ELL0_PHYSICAL_CANDIDATE_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def mass_anchor_closure_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        PRIMITIVE_MASS_ANCHOR_TARGET: {
            "status": resolved_statuses.get(PRIMITIVE_MASS_ANCHOR_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in PRIMITIVE_MASS_ANCHOR_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def rho_chi_protocol_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        RHO_CHI_PROTOCOL_TARGET: {
            "status": resolved_statuses.get(RHO_CHI_PROTOCOL_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in RHO_CHI_PROTOCOL_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def kappa_omega_consistency_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        KAPPA_OMEGA_CONSISTENCY_TARGET: {
            "status": resolved_statuses.get(KAPPA_OMEGA_CONSISTENCY_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in KAPPA_OMEGA_CONSISTENCY_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def joint_action_gravity_anchor_symbols(
    statuses: dict[str, str] | None = None,
) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        JOINT_ACTION_GRAVITY_ANCHOR_TARGET: {
            "status": resolved_statuses.get(JOINT_ACTION_GRAVITY_ANCHOR_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in JOINT_ACTION_GRAVITY_ANCHOR_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def source_response_charge_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        SOURCE_RESPONSE_CHARGE_TARGET: {
            "status": resolved_statuses.get(SOURCE_RESPONSE_CHARGE_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in SOURCE_RESPONSE_CHARGE_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def geometry_response_factor_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        GEOMETRY_RESPONSE_FACTOR_TARGET: {
            "status": resolved_statuses.get(GEOMETRY_RESPONSE_FACTOR_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in GEOMETRY_RESPONSE_FACTOR_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def clock_vacuum_stiffness_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        CLOCK_VACUUM_STIFFNESS_TARGET: {
            "status": resolved_statuses.get(CLOCK_VACUUM_STIFFNESS_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in CLOCK_VACUUM_STIFFNESS_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def G_emergence_clearance_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        G_EMERGENCE_CLEARANCE_TARGET: {
            "status": resolved_statuses.get(G_EMERGENCE_CLEARANCE_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in G_EMERGENCE_CLEARANCE_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def first_principles_G_candidate_symbols(
    statuses: dict[str, str] | None = None,
) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        FIRST_PRINCIPLES_G_CANDIDATE_TARGET: {
            "status": resolved_statuses.get(FIRST_PRINCIPLES_G_CANDIDATE_TARGET, "target"),
            "dimension": {},
        },
        "G_I": {"status": resolved_statuses.get("G_I", "target"), "dimension": {}},
        G_EMERGENCE_CLEARANCE_TARGET: {
            "status": resolved_statuses.get(G_EMERGENCE_CLEARANCE_TARGET, "target"),
            "dimension": {},
        },
    }
    return symbols


def non_gravity_link_bound_symbols(
    statuses: dict[str, str] | None = None,
) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        NON_GRAVITY_LINK_BOUND_TARGET: {
            "status": resolved_statuses.get(NON_GRAVITY_LINK_BOUND_TARGET, "derived_conditional"),
            "dimension": {},
        }
    }
    for symbol in NON_GRAVITY_LINK_BOUND_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived_conditional"), "dimension": {}}
    return symbols


def weak_field_clock_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        WEAK_FIELD_CLOCK_TARGET: {
            "status": resolved_statuses.get(WEAK_FIELD_CLOCK_TARGET, "derived_conditional"),
            "dimension": {},
        },
        "c_I": {"status": resolved_statuses.get("c_I", "primitive"), "dimension": {"L": 1, "T": -1}},
        "G_N": {
            "status": resolved_statuses.get("G_N", "experimental_gate"),
            "dimension": {"M": -1, "L": 3, "T": -2},
        },
        "G_I": {"status": resolved_statuses.get("G_I", "target"), "dimension": {"M": -1, "L": 3, "T": -2}},
        "Phi_I": {"status": resolved_statuses.get("Phi_I", "derived_conditional"), "dimension": {"L": 2, "T": -2}},
        "gamma_ppn_I": {"status": resolved_statuses.get("gamma_ppn_I", "target"), "dimension": {}},
    }
    for symbol in WEAK_FIELD_CLOCK_REQUIRED_SYMBOLS:
        symbols.setdefault(symbol, {"status": resolved_statuses.get(symbol, "derived_conditional"), "dimension": {}})
    return symbols


def source_law_variational_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        SOURCE_LAW_VARIATIONAL_TARGET: {
            "status": resolved_statuses.get(SOURCE_LAW_VARIATIONAL_TARGET, "derived_conditional"),
            "dimension": {},
        },
        "Phi_I": {"status": resolved_statuses.get("Phi_I", "derived_conditional"), "dimension": {"L": 2, "T": -2}},
        "rho_source_I": {"status": resolved_statuses.get("rho_source_I", "derived_conditional"), "dimension": {}},
        "alpha_chi_I": {
            "status": resolved_statuses.get("alpha_chi_I", "derived_conditional"),
            "dimension": {},
        },
        "beta_source_I": {
            "status": resolved_statuses.get("beta_source_I", "derived_conditional"),
            "dimension": {},
        },
    }
    for symbol in SOURCE_LAW_VARIATIONAL_REQUIRED_SYMBOLS:
        symbols.setdefault(symbol, {"status": resolved_statuses.get(symbol, "derived_conditional"), "dimension": {}})
    return symbols


def ppn_no_slip_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        PPN_NO_SLIP_TARGET: {
            "status": resolved_statuses.get(PPN_NO_SLIP_TARGET, "derived_conditional"),
            "dimension": {},
        },
        "Phi_I": {"status": resolved_statuses.get("Phi_I", "derived_conditional"), "dimension": {"L": 2, "T": -2}},
        "Psi_I": {"status": resolved_statuses.get("Psi_I", "target"), "dimension": {"L": 2, "T": -2}},
        "gamma_ppn_I": {"status": resolved_statuses.get("gamma_ppn_I", "target"), "dimension": {}},
        "beta_ppn_I": {"status": resolved_statuses.get("beta_ppn_I", "target"), "dimension": {}},
    }
    for symbol in PPN_NO_SLIP_REQUIRED_SYMBOLS:
        symbols.setdefault(symbol, {"status": resolved_statuses.get(symbol, "derived_conditional"), "dimension": {}})
    return symbols


def no_slip_stress_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        NO_SLIP_STRESS_TARGET: {
            "status": resolved_statuses.get(NO_SLIP_STRESS_TARGET, "derived_conditional"),
            "dimension": {},
        },
        "Phi_I": {"status": resolved_statuses.get("Phi_I", "derived_conditional"), "dimension": {"L": 2, "T": -2}},
        "Psi_I": {"status": resolved_statuses.get("Psi_I", "target"), "dimension": {"L": 2, "T": -2}},
        "anisotropic_stress_I": {"status": resolved_statuses.get("anisotropic_stress_I", "target"), "dimension": {}},
        "non_gravity_slip_residual_I": {
            "status": resolved_statuses.get("non_gravity_slip_residual_I", "target"),
            "dimension": {},
        },
    }
    for symbol in NO_SLIP_STRESS_REQUIRED_SYMBOLS:
        symbols.setdefault(symbol, {"status": resolved_statuses.get(symbol, "derived_conditional"), "dimension": {}})
    return symbols


def source_stress_packet_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        SOURCE_STRESS_PACKET_TARGET: {
            "status": resolved_statuses.get(SOURCE_STRESS_PACKET_TARGET, "derived_conditional"),
            "dimension": {},
        },
        "source_stress_tensor_I": {
            "status": resolved_statuses.get("source_stress_tensor_I", "derived_conditional"),
            "dimension": {},
        },
        "isotropic_pressure_I": {
            "status": resolved_statuses.get("isotropic_pressure_I", "derived_conditional"),
            "dimension": {},
        },
        "anisotropic_stress_I": {"status": resolved_statuses.get("anisotropic_stress_I", "target"), "dimension": {}},
        "stress_coarse_grain_I": {
            "status": resolved_statuses.get("stress_coarse_grain_I", "derived_conditional"),
            "dimension": {},
        },
    }
    for symbol in SOURCE_STRESS_PACKET_REQUIRED_SYMBOLS:
        symbols.setdefault(symbol, {"status": resolved_statuses.get(symbol, "derived_conditional"), "dimension": {}})
    return symbols


def scale_residual_policy_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        SCALE_RESIDUAL_POLICY_TARGET: {
            "status": resolved_statuses.get(SCALE_RESIDUAL_POLICY_TARGET, "derived_conditional"),
            "dimension": {},
        },
        "validated_weak_field_domain_I": {
            "status": resolved_statuses.get("validated_weak_field_domain_I", "derived_conditional"),
            "dimension": {},
        },
        "transition_scale_I": {
            "status": resolved_statuses.get("transition_scale_I", "target"),
            "dimension": {},
        },
        "non_gravity_slip_residual_I": {
            "status": resolved_statuses.get("non_gravity_slip_residual_I", "target"),
            "dimension": {},
        },
        "dark_sector_residual_candidate_I": {
            "status": resolved_statuses.get("dark_sector_residual_candidate_I", "target"),
            "dimension": {},
        },
    }
    for symbol in SCALE_RESIDUAL_POLICY_REQUIRED_SYMBOLS:
        symbols.setdefault(symbol, {"status": resolved_statuses.get(symbol, "derived_conditional"), "dimension": {}})
    return symbols


def screened_slip_residual_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        SCREENED_SLIP_RESIDUAL_TARGET: {
            "status": resolved_statuses.get(SCREENED_SLIP_RESIDUAL_TARGET, "derived_conditional"),
            "dimension": {},
        },
        "residual_amplitude_I": {
            "status": resolved_statuses.get("residual_amplitude_I", "target"),
            "dimension": {},
        },
        "residual_transition_length_I": {
            "status": resolved_statuses.get("residual_transition_length_I", "target"),
            "dimension": {"L": 1},
        },
        "non_gravity_slip_residual_I": {
            "status": resolved_statuses.get("non_gravity_slip_residual_I", "target"),
            "dimension": {},
        },
        "dark_sector_residual_candidate_I": {
            "status": resolved_statuses.get("dark_sector_residual_candidate_I", "target"),
            "dimension": {},
        },
    }
    for symbol in SCREENED_SLIP_RESIDUAL_REQUIRED_SYMBOLS:
        symbols.setdefault(symbol, {"status": resolved_statuses.get(symbol, "derived_conditional"), "dimension": {}})
    return symbols


def screened_observational_gate_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        SCREENED_OBSERVATIONAL_GATE_TARGET: {
            "status": resolved_statuses.get(SCREENED_OBSERVATIONAL_GATE_TARGET, "derived_conditional"),
            "dimension": {},
        },
        SCREENED_SLIP_RESIDUAL_TARGET: {
            "status": resolved_statuses.get(SCREENED_SLIP_RESIDUAL_TARGET, "derived_conditional"),
            "dimension": {},
        },
        "validated_weak_field_domain_I": {
            "status": resolved_statuses.get("validated_weak_field_domain_I", "derived_conditional"),
            "dimension": {},
        },
        "galactic_residual_test_I": {
            "status": resolved_statuses.get("galactic_residual_test_I", "target"),
            "dimension": {},
        },
    }
    for symbol in SCREENED_OBSERVATIONAL_GATE_REQUIRED_SYMBOLS:
        symbols.setdefault(symbol, {"status": resolved_statuses.get(symbol, "derived_conditional"), "dimension": {}})
    return symbols


def primitive_tick_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        PRIMITIVE_TICK_TARGET: {
            "status": resolved_statuses.get(PRIMITIVE_TICK_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in PRIMITIVE_TICK_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def primitive_work_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        PRIMITIVE_WORK_TARGET: {
            "status": resolved_statuses.get(PRIMITIVE_WORK_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in PRIMITIVE_WORK_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def action_standard_work_time_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        ACTION_STANDARD_TARGET: {
            "status": resolved_statuses.get(ACTION_STANDARD_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in ACTION_STANDARD_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def qm_generator_translation_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        QM_GENERATOR_TRANSLATION_TARGET: {
            "status": resolved_statuses.get(QM_GENERATOR_TRANSLATION_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in QM_GENERATOR_TRANSLATION_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def qm_continuum_limit_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        QM_CONTINUUM_LIMIT_TARGET: {
            "status": resolved_statuses.get(QM_CONTINUUM_LIMIT_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in QM_CONTINUUM_LIMIT_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def qm_apparatus_facticity_symbols(statuses: dict[str, str] | None = None) -> dict[str, dict[str, object]]:
    resolved_statuses = {} if statuses is None else statuses
    symbols: dict[str, dict[str, object]] = {
        QM_APPARATUS_FACTICITY_TARGET: {
            "status": resolved_statuses.get(QM_APPARATUS_FACTICITY_TARGET, "target"),
            "dimension": {},
        }
    }
    for symbol in QM_APPARATUS_FACTICITY_REQUIRED_SYMBOLS:
        symbols[symbol] = {"status": resolved_statuses.get(symbol, "derived"), "dimension": {}}
    return symbols


def bell_contexts(signalling: bool) -> list[dict[str, object]]:
    contexts = maximal_chsh_contexts()
    if signalling:
        contexts[1] = {
            "x": 0,
            "y": 1,
            "probabilities": [
                {"a": 1, "b": 1, "p": 0.5},
                {"a": 1, "b": -1, "p": 0.5},
                {"a": -1, "b": 1, "p": 0.0},
                {"a": -1, "b": -1, "p": 0.0},
            ],
        }
    return contexts


def maximal_chsh_contexts() -> list[dict[str, object]]:
    positive = [
        {"a": 1, "b": 1, "p": 0.4267766952966369},
        {"a": 1, "b": -1, "p": 0.0732233047033631},
        {"a": -1, "b": 1, "p": 0.0732233047033631},
        {"a": -1, "b": -1, "p": 0.4267766952966369},
    ]
    negative = [
        {"a": 1, "b": 1, "p": 0.0732233047033631},
        {"a": 1, "b": -1, "p": 0.4267766952966369},
        {"a": -1, "b": 1, "p": 0.4267766952966369},
        {"a": -1, "b": -1, "p": 0.0732233047033631},
    ]
    return [
        {"x": 0, "y": 0, "probabilities": positive},
        {"x": 0, "y": 1, "probabilities": positive},
        {"x": 1, "y": 0, "probabilities": positive},
        {"x": 1, "y": 1, "probabilities": negative},
    ]


def bell_amplitude_contexts() -> list[dict[str, object]]:
    positive = [
        {"a": 1, "b": 1, "amp": 0.6532814824381883},
        {"a": 1, "b": -1, "amp": 0.27059805007309845},
        {"a": -1, "b": 1, "amp": 0.27059805007309845},
        {"a": -1, "b": -1, "amp": 0.6532814824381883},
    ]
    negative = [
        {"a": 1, "b": 1, "amp": 0.27059805007309845},
        {"a": 1, "b": -1, "amp": 0.6532814824381883},
        {"a": -1, "b": 1, "amp": 0.6532814824381883},
        {"a": -1, "b": -1, "amp": 0.27059805007309845},
    ]
    return [
        {"x": 0, "y": 0, "amplitudes": positive},
        {"x": 0, "y": 1, "amplitudes": positive},
        {"x": 1, "y": 0, "amplitudes": positive},
        {"x": 1, "y": 1, "amplitudes": negative},
    ]


def pr_box_contexts() -> list[dict[str, object]]:
    equal = [
        {"a": 1, "b": 1, "p": 0.5},
        {"a": 1, "b": -1, "p": 0.0},
        {"a": -1, "b": 1, "p": 0.0},
        {"a": -1, "b": -1, "p": 0.5},
    ]
    different = [
        {"a": 1, "b": 1, "p": 0.0},
        {"a": 1, "b": -1, "p": 0.5},
        {"a": -1, "b": 1, "p": 0.5},
        {"a": -1, "b": -1, "p": 0.0},
    ]
    return [
        {"x": 0, "y": 0, "probabilities": equal},
        {"x": 0, "y": 1, "probabilities": equal},
        {"x": 1, "y": 0, "probabilities": equal},
        {"x": 1, "y": 1, "probabilities": different},
    ]


def spectral_cost_phase_edges(use_bad_validation_phase: bool) -> list[dict[str, object]]:
    validation_x: list[list[object]]
    if use_bad_validation_phase:
        validation_x = [
            [
                {"re": 2.613924474185282, "im": 0.1570239424204274},
                {"re": 0.5859465745295532, "im": 0.03519904346473229},
            ],
            [
                {"re": 0.388873087018807, "im": 0.023360424460590876},
                {"re": 1.4101157492940875, "im": 0.08470861970574198},
            ],
        ]
    else:
        validation_x = [
            [
                {"re": 2.6179750535655044, "im": 0.05885825470355462},
                {"re": 0.5868545667596812, "im": 0.013193874982591104},
            ],
            [
                {"re": 0.3894756910050193, "im": 0.008756332261759188},
                {"re": 1.4123008873247482, "im": 0.03175185540099202},
            ],
        ]
    calibration_x: list[list[object]] = [
        [
            {"re": 2.2622416234451306, "im": 0.024203025688530763},
            {"re": 0.5019277526803017, "im": 0.00536997028346053},
        ],
        [
            {"re": 0.37100474292914626, "im": 0.003969265365211626},
            {"re": 1.744164059099928, "im": 0.018660273548994542},
        ],
    ]
    return [
        {
            "from": "a",
            "to": "b",
            "G0": [[2.0, 0.4], [0.4, 3.0]],
            "G1": [[4.0, 0.7], [0.7, 1.6]],
            "X": calibration_x,
        },
        {
            "from": "b",
            "to": "a",
            "G0": [[2.0, 0.4], [0.4, 3.0]],
            "G1": [[4.0, 0.7], [0.7, 1.6]],
            "X": calibration_x,
        },
        {
            "from": "a",
            "to": "c",
            "G0": [[2.0, 0.4], [0.4, 3.0]],
            "G1": [[7.0, 1.1], [1.1, 1.4]],
            "X": validation_x,
        },
        {
            "from": "c",
            "to": "a",
            "G0": [[2.0, 0.4], [0.4, 3.0]],
            "G1": [[7.0, 1.1], [1.1, 1.4]],
            "X": validation_x,
        },
    ]


if __name__ == "__main__":
    unittest.main()
