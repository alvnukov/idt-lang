from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from scripts.run_v8_experiment_suite import main
from theory_experiments.v8_runner import (
    ActionScaleFixture,
    BellAmplitudeFixture,
    ExperimentRunnerError,
    FixtureSet,
    MarkerEraserFixture,
    NoCloningFixture,
    PhaseAccumulationFixture,
    RepeatedContextZenoFixture,
    SpinTransitionFixture,
    ZenoSample,
    default_fixtures,
    parse_protocol_registry,
    run_experiment_suite,
    stats_json_text,
)


class V8ExperimentRunnerTests(unittest.TestCase):
    def test_lean_protocol_json_is_parseable(self) -> None:
        completed = subprocess.run(
            ["lake", "exe", "idt_v8_experiment_protocols", "--", "--json"],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        )

        registry = parse_protocol_registry(json.loads(completed.stdout))

        self.assertEqual(35, len(registry.protocols))
        self.assertIn("context_normalization", registry.logical_node_ids)
        self.assertIn("residual_fixture_not_implemented", registry.logical_node_ids)

    def test_unknown_logical_node_is_rejected(self) -> None:
        payload = sample_registry()
        protocols = require_list(payload["protocols"])
        first_protocol = require_mapping(protocols[0])
        first_protocol["logical_nodes"] = ["missing_node"]
        protocols[0] = first_protocol

        with self.assertRaisesRegex(ExperimentRunnerError, "unknown logical node"):
            parse_protocol_registry(payload)

    def test_forbidden_formal_proof_upgrade_is_required(self) -> None:
        payload = sample_registry()
        protocols = require_list(payload["protocols"])
        first_protocol = require_mapping(protocols[0])
        first_protocol["forbidden_upgrades"] = ["physical_formal_proof", "qm_formal_proof"]
        protocols[0] = first_protocol

        with self.assertRaisesRegex(ExperimentRunnerError, "formal_proof"):
            parse_protocol_registry(payload)

    def test_per_experiment_refit_is_rejected(self) -> None:
        registry = parse_protocol_registry(sample_registry())
        fixtures = default_fixtures()
        bad_fixtures = FixtureSet(
            action_scale=ActionScaleFixture(
                shared_action_scale=fixtures.action_scale.shared_action_scale,
                tolerance=fixtures.action_scale.tolerance,
                allow_per_experiment_refit=True,
                hbar_status=fixtures.action_scale.hbar_status,
                observations=fixtures.action_scale.observations,
            ),
            readout=fixtures.readout,
            bell=fixtures.bell,
            interference=fixtures.interference,
            sorkin=fixtures.sorkin,
            marker_eraser=fixtures.marker_eraser,
            phase=fixtures.phase,
            spin=fixtures.spin,
            unitary=fixtures.unitary,
            projective=fixtures.projective,
            bell_amplitude=fixtures.bell_amplitude,
            singlet_angle=fixtures.singlet_angle,
            decoherence=fixtures.decoherence,
            zeno=fixtures.zeno,
            context_transfer=fixtures.context_transfer,
            no_cloning=fixtures.no_cloning,
            barrier=fixtures.barrier,
            bosonic=fixtures.bosonic,
            single_quantum=fixtures.single_quantum,
            inheritance_swap=fixtures.inheritance_swap,
            multipartite=fixtures.multipartite,
            ks_contextuality=fixtures.ks_contextuality,
            temporal=fixtures.temporal,
            partial_facticity=fixtures.partial_facticity,
            graph_walk=fixtures.graph_walk,
        )

        payload = run_experiment_suite(
            registry=registry,
            repo_root=REPO_ROOT,
            experiment_filters=["calibrated_action_scale_reconstruction_demo"],
            fixtures=bad_fixtures,
        )

        telemetry = require_rows(payload["telemetry"])
        self.assertTrue(
            any(
                row["node_id"] == "no_refit_shared_parameter" and row["status"] == "fail"
                for row in telemetry
            )
        )

    def test_normal_run_contains_used_stressed_and_blocked_telemetry(self) -> None:
        registry = parse_protocol_registry(sample_registry())

        payload = run_experiment_suite(registry=registry, repo_root=REPO_ROOT)

        telemetry = require_rows(payload["telemetry"])
        roles = {str(row["role"]) for row in telemetry}
        self.assertIn("used", roles)
        self.assertIn("stressed", roles)
        self.assertIn("blocked", roles)

    def test_blocked_residual_protocol_summarizes_as_blocked(self) -> None:
        payload = sample_registry()
        logical_nodes = require_list(payload["logical_nodes"])
        logical_nodes.append(
            {
                "id": "residual_fixture_not_implemented",
                "label": "residual fixture missing",
                "claim_boundary": "blocked until fixture exists",
            }
        )
        protocols = require_list(payload["protocols"])
        protocols.append(
            {
                "id": "quantum_random_walk_protocol",
                "experiment_id": "quantum_random_walk",
                "fixture_class": "residual_not_implemented",
                "claim_boundary": "coverage only",
                "logical_nodes": ["residual_fixture_not_implemented"],
                "allowed_result_statuses": ["pass", "fail", "inconclusive", "blocked"],
                "forbidden_upgrades": ["formal_proof", "physical_formal_proof", "qm_formal_proof"],
            }
        )
        registry = parse_protocol_registry(payload)

        result = run_experiment_suite(
            registry=registry,
            repo_root=REPO_ROOT,
            experiment_filters=["quantum_random_walk"],
        )

        experiments = require_rows(result["experiments"])
        self.assertEqual("blocked", experiments[0]["status"])

    def test_wrong_phase_fixture_fails(self) -> None:
        registry = parse_protocol_registry(phase_registry())
        fixtures = default_fixtures()
        phase = dict(fixtures.phase)
        phase["ab_flux_period"] = PhaseAccumulationFixture(
            observed_phase=0.0,
            expected_phase=1.0,
            context_total=1.0,
            expected_total=1.0,
            tolerance=1.0e-10,
        )

        result = run_experiment_suite(
            registry=registry,
            repo_root=REPO_ROOT,
            experiment_filters=["ab_flux_period"],
            fixtures=FixtureSet(
                action_scale=fixtures.action_scale,
                readout=fixtures.readout,
                bell=fixtures.bell,
                interference=fixtures.interference,
                sorkin=fixtures.sorkin,
                marker_eraser=fixtures.marker_eraser,
                phase=phase,
                spin=fixtures.spin,
                unitary=fixtures.unitary,
                projective=fixtures.projective,
                bell_amplitude=fixtures.bell_amplitude,
                singlet_angle=fixtures.singlet_angle,
                decoherence=fixtures.decoherence,
                zeno=fixtures.zeno,
                context_transfer=fixtures.context_transfer,
                no_cloning=fixtures.no_cloning,
                barrier=fixtures.barrier,
                bosonic=fixtures.bosonic,
                single_quantum=fixtures.single_quantum,
                inheritance_swap=fixtures.inheritance_swap,
                multipartite=fixtures.multipartite,
                ks_contextuality=fixtures.ks_contextuality,
                temporal=fixtures.temporal,
                partial_facticity=fixtures.partial_facticity,
                graph_walk=fixtures.graph_walk,
            ),
        )

        self.assertEqual("fail", require_rows(result["experiments"])[0]["status"])

    def test_wrong_marker_eraser_fixture_fails(self) -> None:
        registry = parse_protocol_registry(marker_registry())
        fixtures = default_fixtures()
        marker_eraser = dict(fixtures.marker_eraser)
        marker_eraser["quantum_eraser"] = MarkerEraserFixture(
            marker_distinguishability=1.0,
            marker_visibility=0.0,
            eraser_visibility=0.1,
            expected_marker_visibility=0.0,
            expected_eraser_visibility=0.8,
            tolerance=1.0e-10,
        )

        result = run_experiment_suite(
            registry=registry,
            repo_root=REPO_ROOT,
            experiment_filters=["quantum_eraser"],
            fixtures=FixtureSet(
                action_scale=fixtures.action_scale,
                readout=fixtures.readout,
                bell=fixtures.bell,
                interference=fixtures.interference,
                sorkin=fixtures.sorkin,
                marker_eraser=marker_eraser,
                phase=fixtures.phase,
                spin=fixtures.spin,
                unitary=fixtures.unitary,
                projective=fixtures.projective,
                bell_amplitude=fixtures.bell_amplitude,
                singlet_angle=fixtures.singlet_angle,
                decoherence=fixtures.decoherence,
                zeno=fixtures.zeno,
                context_transfer=fixtures.context_transfer,
                no_cloning=fixtures.no_cloning,
                barrier=fixtures.barrier,
                bosonic=fixtures.bosonic,
                single_quantum=fixtures.single_quantum,
                inheritance_swap=fixtures.inheritance_swap,
                multipartite=fixtures.multipartite,
                ks_contextuality=fixtures.ks_contextuality,
                temporal=fixtures.temporal,
                partial_facticity=fixtures.partial_facticity,
                graph_walk=fixtures.graph_walk,
            ),
        )

        self.assertEqual("fail", require_rows(result["experiments"])[0]["status"])

    def test_wrong_spin_transition_fixture_fails(self) -> None:
        registry = parse_protocol_registry(spin_registry())
        fixtures = default_fixtures()
        spin = dict(fixtures.spin)
        spin["sequential_stern_gerlach"] = SpinTransitionFixture(
            probabilities=(1.0, 0.0),
            expected_probabilities=(0.5, 0.5),
            tolerance=1.0e-10,
        )

        result = run_experiment_suite(
            registry=registry,
            repo_root=REPO_ROOT,
            experiment_filters=["sequential_stern_gerlach"],
            fixtures=FixtureSet(
                action_scale=fixtures.action_scale,
                readout=fixtures.readout,
                bell=fixtures.bell,
                interference=fixtures.interference,
                sorkin=fixtures.sorkin,
                marker_eraser=fixtures.marker_eraser,
                phase=fixtures.phase,
                spin=spin,
                unitary=fixtures.unitary,
                projective=fixtures.projective,
                bell_amplitude=fixtures.bell_amplitude,
                singlet_angle=fixtures.singlet_angle,
                decoherence=fixtures.decoherence,
                zeno=fixtures.zeno,
                context_transfer=fixtures.context_transfer,
                no_cloning=fixtures.no_cloning,
                barrier=fixtures.barrier,
                bosonic=fixtures.bosonic,
                single_quantum=fixtures.single_quantum,
                inheritance_swap=fixtures.inheritance_swap,
                multipartite=fixtures.multipartite,
                ks_contextuality=fixtures.ks_contextuality,
                temporal=fixtures.temporal,
                partial_facticity=fixtures.partial_facticity,
                graph_walk=fixtures.graph_walk,
            ),
        )

        self.assertEqual("fail", require_rows(result["experiments"])[0]["status"])

    def test_wrong_bell_amplitude_fixture_fails(self) -> None:
        registry = parse_protocol_registry(bell_amplitude_registry())
        fixtures = default_fixtures()
        bad_fixture = BellAmplitudeFixture(
            contexts=fixtures.bell_amplitude["bell_chsh_from_amplitudes"].contexts,
            expected_abs_s=1.0,
            max_abs_s=2.8284271247461903,
            tolerance=1.0e-10,
        )
        result = run_experiment_suite(
            registry=registry,
            repo_root=REPO_ROOT,
            experiment_filters=["bell_chsh_from_amplitudes"],
            fixtures=FixtureSet(
                action_scale=fixtures.action_scale,
                readout=fixtures.readout,
                bell=fixtures.bell,
                interference=fixtures.interference,
                sorkin=fixtures.sorkin,
                marker_eraser=fixtures.marker_eraser,
                phase=fixtures.phase,
                spin=fixtures.spin,
                unitary=fixtures.unitary,
                projective=fixtures.projective,
                bell_amplitude={"bell_chsh_from_amplitudes": bad_fixture},
                singlet_angle=fixtures.singlet_angle,
                decoherence=fixtures.decoherence,
                zeno=fixtures.zeno,
                context_transfer=fixtures.context_transfer,
                no_cloning=fixtures.no_cloning,
                barrier=fixtures.barrier,
                bosonic=fixtures.bosonic,
                single_quantum=fixtures.single_quantum,
                inheritance_swap=fixtures.inheritance_swap,
                multipartite=fixtures.multipartite,
                ks_contextuality=fixtures.ks_contextuality,
                temporal=fixtures.temporal,
                partial_facticity=fixtures.partial_facticity,
                graph_walk=fixtures.graph_walk,
            ),
        )

        self.assertEqual("fail", require_rows(result["experiments"])[0]["status"])

    def test_wrong_zeno_fixture_fails(self) -> None:
        registry = parse_protocol_registry(zeno_registry())
        fixtures = default_fixtures()
        result = run_experiment_suite(
            registry=registry,
            repo_root=REPO_ROOT,
            experiment_filters=["quantum_zeno"],
            fixtures=FixtureSet(
                action_scale=fixtures.action_scale,
                readout=fixtures.readout,
                bell=fixtures.bell,
                interference=fixtures.interference,
                sorkin=fixtures.sorkin,
                marker_eraser=fixtures.marker_eraser,
                phase=fixtures.phase,
                spin=fixtures.spin,
                unitary=fixtures.unitary,
                projective=fixtures.projective,
                bell_amplitude=fixtures.bell_amplitude,
                singlet_angle=fixtures.singlet_angle,
                decoherence=fixtures.decoherence,
                zeno={
                    "quantum_zeno": RepeatedContextZenoFixture(
                        total_angle=1.0,
                        samples=(ZenoSample(1, 0.0),),
                        tolerance=1.0e-10,
                    )
                },
                context_transfer=fixtures.context_transfer,
                no_cloning=fixtures.no_cloning,
                barrier=fixtures.barrier,
                bosonic=fixtures.bosonic,
                single_quantum=fixtures.single_quantum,
                inheritance_swap=fixtures.inheritance_swap,
                multipartite=fixtures.multipartite,
                ks_contextuality=fixtures.ks_contextuality,
                temporal=fixtures.temporal,
                partial_facticity=fixtures.partial_facticity,
                graph_walk=fixtures.graph_walk,
            ),
        )

        self.assertEqual("fail", require_rows(result["experiments"])[0]["status"])

    def test_wrong_no_cloning_fixture_fails(self) -> None:
        registry = parse_protocol_registry(no_cloning_registry())
        fixtures = default_fixtures()
        no_cloning = dict(fixtures.no_cloning)
        no_cloning["no_cloning"] = NoCloningFixture(
            state_overlap=0.5,
            min_obstruction=0.1,
            expected_obstructed=False,
            tolerance=1.0e-10,
        )

        result = run_experiment_suite(
            registry=registry,
            repo_root=REPO_ROOT,
            experiment_filters=["no_cloning"],
            fixtures=FixtureSet(
                action_scale=fixtures.action_scale,
                readout=fixtures.readout,
                bell=fixtures.bell,
                interference=fixtures.interference,
                sorkin=fixtures.sorkin,
                marker_eraser=fixtures.marker_eraser,
                phase=fixtures.phase,
                spin=fixtures.spin,
                unitary=fixtures.unitary,
                projective=fixtures.projective,
                bell_amplitude=fixtures.bell_amplitude,
                singlet_angle=fixtures.singlet_angle,
                decoherence=fixtures.decoherence,
                zeno=fixtures.zeno,
                context_transfer=fixtures.context_transfer,
                no_cloning=no_cloning,
                barrier=fixtures.barrier,
                bosonic=fixtures.bosonic,
                single_quantum=fixtures.single_quantum,
                inheritance_swap=fixtures.inheritance_swap,
                multipartite=fixtures.multipartite,
                ks_contextuality=fixtures.ks_contextuality,
                temporal=fixtures.temporal,
                partial_facticity=fixtures.partial_facticity,
                graph_walk=fixtures.graph_walk,
            ),
        )

        self.assertEqual("fail", require_rows(result["experiments"])[0]["status"])

    def test_output_is_deterministic(self) -> None:
        registry = parse_protocol_registry(sample_registry())

        first = run_experiment_suite(registry=registry, repo_root=REPO_ROOT)
        second = run_experiment_suite(registry=registry, repo_root=REPO_ROOT)

        self.assertEqual(stats_json_text(first, pretty=False), stats_json_text(second, pretty=False))

    def test_cli_writes_compact_json_to_output_path(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            protocol_path = root / "protocols.json"
            output_path = root / "stats.json"
            report_path = root / "report.md"
            protocol_path.write_text(json.dumps(sample_registry(), sort_keys=True), encoding="utf-8")

            exit_code = main(
                [
                    "--protocol-json",
                    str(protocol_path),
                    "--output",
                    str(output_path),
                    "--report",
                    str(report_path),
                ]
            )

            self.assertEqual(0, exit_code)
            raw = output_path.read_text(encoding="utf-8")
            self.assertNotIn("\n  ", raw)
            parsed = json.loads(raw)
            self.assertEqual("idt-v8-experiment-node-stats/1", parsed["schema"])
            self.assertTrue(report_path.exists())


REPO_ROOT = Path(__file__).resolve().parents[1]


def sample_registry() -> dict[str, object]:
    return {
        "schema": "idt-v8-experiment-protocol-registry/1",
        "protocol_authority": "lean_checked_protocol",
        "result_boundary": "certified_executable_check",
        "proof_boundary": "experiment_results_are_not_formal_proofs",
        "logical_nodes": [
            {
                "id": "phase_action_conversion_I",
                "label": "calibrated universal action-to-phase anchor",
                "claim_boundary": "calibrated anchor only",
            },
            {
                "id": "no_refit_shared_parameter",
                "label": "one shared frozen parameter",
                "claim_boundary": "reject per-experiment refit",
            },
            {
                "id": "hbar_first_principles_boundary",
                "label": "hbar_I remains blocked",
                "claim_boundary": "no hbar proof upgrade",
            },
            {
                "id": "context_normalization",
                "label": "finite readout weights normalize",
                "claim_boundary": "finite check only",
            },
            {
                "id": "positive_measure_readout",
                "label": "finite readout weights nonnegative",
                "claim_boundary": "finite check only",
            },
            {
                "id": "bell_chsh_no_signalling",
                "label": "Bell table no-signalling",
                "claim_boundary": "finite table only",
            },
            {
                "id": "bounded_correlation_window",
                "label": "CHSH finite bound",
                "claim_boundary": "finite table only",
            },
        ],
        "protocols": [
            {
                "id": "calibrated_action_scale_reconstruction_protocol",
                "experiment_id": "calibrated_action_scale_reconstruction_demo",
                "fixture_class": "calibrated_action_scale_reconstruction",
                "claim_boundary": "shared calibrated action scale only",
                "logical_nodes": [
                    "phase_action_conversion_I",
                    "no_refit_shared_parameter",
                    "hbar_first_principles_boundary",
                ],
                "allowed_result_statuses": ["pass", "fail", "inconclusive", "blocked"],
                "forbidden_upgrades": ["formal_proof", "physical_formal_proof", "qm_formal_proof"],
            },
            {
                "id": "finite_readout_normalization_protocol",
                "experiment_id": "born_context_probability_tests",
                "fixture_class": "finite_readout_normalization",
                "claim_boundary": "finite normalization only",
                "logical_nodes": ["context_normalization", "positive_measure_readout"],
                "allowed_result_statuses": ["pass", "fail", "inconclusive", "blocked"],
                "forbidden_upgrades": ["formal_proof", "physical_formal_proof", "qm_formal_proof"],
            },
            {
                "id": "bell_chsh_table_protocol",
                "experiment_id": "bell_chsh_table",
                "fixture_class": "bell_chsh_table",
                "claim_boundary": "finite Bell table only",
                "logical_nodes": ["bell_chsh_no_signalling", "bounded_correlation_window"],
                "allowed_result_statuses": ["pass", "fail", "inconclusive", "blocked"],
                "forbidden_upgrades": ["formal_proof", "physical_formal_proof", "qm_formal_proof"],
            },
        ],
    }


def phase_registry() -> dict[str, object]:
    payload = sample_registry()
    logical_nodes = require_list(payload["logical_nodes"])
    logical_nodes.extend(
        [
            {
                "id": "phase_accumulation",
                "label": "phase accumulation",
                "claim_boundary": "calibrated phase fixture only",
            },
        ]
    )
    require_list(payload["protocols"]).append(
        {
            "id": "ab_flux_period_protocol",
            "experiment_id": "ab_flux_period",
            "fixture_class": "phase_accumulation",
            "claim_boundary": "calibrated phase fixture only",
            "logical_nodes": ["phase_accumulation", "phase_action_conversion_I"],
            "allowed_result_statuses": ["pass", "fail", "inconclusive", "blocked"],
            "forbidden_upgrades": ["formal_proof", "physical_formal_proof", "qm_formal_proof"],
        }
    )
    return payload


def marker_registry() -> dict[str, object]:
    payload = sample_registry()
    logical_nodes = require_list(payload["logical_nodes"])
    logical_nodes.extend(
        [
            {
                "id": "path_marker_distinguishability",
                "label": "marker distinguishability",
                "claim_boundary": "finite marker fixture only",
            },
            {
                "id": "interference_visibility",
                "label": "interference visibility",
                "claim_boundary": "finite visibility fixture only",
            },
        ]
    )
    require_list(payload["protocols"]).append(
        {
            "id": "quantum_eraser_protocol",
            "experiment_id": "quantum_eraser",
            "fixture_class": "marker_eraser_visibility",
            "claim_boundary": "finite eraser fixture only",
            "logical_nodes": ["path_marker_distinguishability", "interference_visibility"],
            "allowed_result_statuses": ["pass", "fail", "inconclusive", "blocked"],
            "forbidden_upgrades": ["formal_proof", "physical_formal_proof", "qm_formal_proof"],
        }
    )
    return payload


def spin_registry() -> dict[str, object]:
    payload = sample_registry()
    logical_nodes = require_list(payload["logical_nodes"])
    logical_nodes.append(
        {
            "id": "spin_axis_transition",
            "label": "spin transition",
            "claim_boundary": "finite spin fixture only",
        }
    )
    require_list(payload["protocols"]).append(
        {
            "id": "sequential_stern_gerlach_protocol",
            "experiment_id": "sequential_stern_gerlach",
            "fixture_class": "spin_axis_transition",
            "claim_boundary": "finite spin transition fixture only",
            "logical_nodes": ["spin_axis_transition", "positive_measure_readout"],
            "allowed_result_statuses": ["pass", "fail", "inconclusive", "blocked"],
            "forbidden_upgrades": ["formal_proof", "physical_formal_proof", "qm_formal_proof"],
        }
    )
    return payload


def bell_amplitude_registry() -> dict[str, object]:
    payload = sample_registry()
    logical_nodes = require_list(payload["logical_nodes"])
    logical_nodes.append(
        {
            "id": "amplitude_probability_readout",
            "label": "amplitude readout",
            "claim_boundary": "finite amplitude fixture only",
        }
    )
    require_list(payload["protocols"]).append(
        {
            "id": "bell_chsh_from_amplitudes_protocol",
            "experiment_id": "bell_chsh_from_amplitudes",
            "fixture_class": "bell_amplitude_table",
            "claim_boundary": "finite amplitude fixture only",
            "logical_nodes": [
                "amplitude_probability_readout",
                "bell_chsh_no_signalling",
                "bounded_correlation_window",
            ],
            "allowed_result_statuses": ["pass", "fail", "inconclusive", "blocked"],
            "forbidden_upgrades": ["formal_proof", "physical_formal_proof", "qm_formal_proof"],
        }
    )
    return payload


def zeno_registry() -> dict[str, object]:
    payload = sample_registry()
    logical_nodes = require_list(payload["logical_nodes"])
    logical_nodes.append(
        {
            "id": "repeated_context_survival",
            "label": "Zeno survival",
            "claim_boundary": "finite Zeno fixture only",
        }
    )
    require_list(payload["protocols"]).append(
        {
            "id": "quantum_zeno_protocol",
            "experiment_id": "quantum_zeno",
            "fixture_class": "repeated_context_zeno",
            "claim_boundary": "finite Zeno fixture only",
            "logical_nodes": ["repeated_context_survival", "context_normalization"],
            "allowed_result_statuses": ["pass", "fail", "inconclusive", "blocked"],
            "forbidden_upgrades": ["formal_proof", "physical_formal_proof", "qm_formal_proof"],
        }
    )
    return payload


def no_cloning_registry() -> dict[str, object]:
    payload = sample_registry()
    logical_nodes = require_list(payload["logical_nodes"])
    logical_nodes.append(
        {
            "id": "no_cloning_obstruction",
            "label": "no-cloning obstruction",
            "claim_boundary": "finite obstruction fixture only",
        }
    )
    require_list(payload["protocols"]).append(
        {
            "id": "no_cloning_protocol",
            "experiment_id": "no_cloning",
            "fixture_class": "no_cloning_context_invariance",
            "claim_boundary": "finite obstruction fixture only",
            "logical_nodes": ["no_cloning_obstruction"],
            "allowed_result_statuses": ["pass", "fail", "inconclusive", "blocked"],
            "forbidden_upgrades": ["formal_proof", "physical_formal_proof", "qm_formal_proof"],
        }
    )
    return payload


def require_list(value: object) -> list[object]:
    if not isinstance(value, list):
        raise AssertionError("expected list")
    return value


def require_mapping(value: object) -> dict[str, object]:
    if not isinstance(value, dict):
        raise AssertionError("expected mapping")
    output: dict[str, object] = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise AssertionError("expected string key")
        output[key] = item
    return output


def require_rows(value: object) -> list[dict[str, object]]:
    rows = require_list(value)
    output: list[dict[str, object]] = []
    for row in rows:
        output.append(require_mapping(row))
    return output


if __name__ == "__main__":
    unittest.main()
