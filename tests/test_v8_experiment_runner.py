from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from scripts.run_v8_experiment_suite import main
from theory_experiments.v8_runner import (
    ActionScaleFixture,
    ExperimentRunnerError,
    FixtureSet,
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

        self.assertEqual(3, len(registry.protocols))
        self.assertIn("context_normalization", registry.logical_node_ids)

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
        statuses = {str(row["status"]) for row in telemetry}
        self.assertIn("used", roles)
        self.assertIn("stressed", roles)
        self.assertIn("blocked", roles)
        self.assertIn("blocked", statuses)

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
