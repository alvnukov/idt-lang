from __future__ import annotations

import unittest
from pathlib import Path

from theory_verifier.declarative import (
    JsonObject,
    load_json_file,
    load_rule_documents,
    verify_declarative_rule_documents,
)


ROOT = Path(__file__).resolve().parents[1]


class DeclarativeVerifierTests(unittest.TestCase):
    def test_v8_rules_pass_current_manifest(self) -> None:
        manifest = load_json_file(ROOT / "theory_verifier_manifest.json")
        rules = load_rule_documents(ROOT / "rules/v8")

        report = verify_declarative_rule_documents(manifest, rules, ROOT)

        self.assertTrue(report.ok, report.to_jsonable())
        self.assertGreaterEqual(report.verification_rules_checked, 1)

    def test_proposed_vocabulary_term_requires_approval_gate(self) -> None:
        manifest: JsonObject = {
            "symbols": {},
            "equations": [],
            "derivations": [],
            "finite_gates": [],
            "qm_experiments": [],
            "qm_universal_patterns": [],
            "qm_core_proof_obligations": [],
            "theorem_cards": [],
        }
        rules: tuple[JsonObject, ...] = (
            {
                "id": "bad_vocab",
                "kind": "verification_specification",
                "language_version": "v8.0.0",
                "controlled_vocabulary": [
                    {
                        "term": "new-local-word",
                        "status": "proposed_term",
                        "domain": "IDT",
                        "definition": "A term introduced without approval.",
                    }
                ],
                "verification_rules": [],
            },
        )

        report = verify_declarative_rule_documents(manifest, rules, ROOT)

        self.assertFalse(report.ok)
        self.assertEqual(
            "declarative_proposed_term_without_approval_gate",
            report.issues[0].code,
        )

    def test_unknown_reference_is_rejected(self) -> None:
        manifest: JsonObject = {
            "symbols": {},
            "equations": [],
            "derivations": [],
            "finite_gates": [
                {
                    "id": "gate_a",
                    "type": "demo",
                    "route_gates": ["missing_gate"],
                }
            ],
            "qm_experiments": [],
            "qm_universal_patterns": [],
            "qm_core_proof_obligations": [],
            "theorem_cards": [],
        }
        rules: tuple[JsonObject, ...] = (
            {
                "id": "ref_spec",
                "kind": "verification_specification",
                "language_version": "v8.0.0",
                "controlled_vocabulary": [],
                "verification_rules": [
                    {
                        "id": "refs_exist",
                        "applies_to": {
                            "collection": "finite_gates"
                        },
                        "assertions": [
                            {
                                "predicate": "refs_exist",
                                "field_path": "route_gates[]",
                                "reference_collections": ["finite_gates"],
                            }
                        ],
                    }
                ],
            },
        )

        report = verify_declarative_rule_documents(manifest, rules, ROOT)

        self.assertFalse(report.ok)
        self.assertEqual("declarative_unknown_ref", report.issues[0].code)

    def test_qm_experiment_residual_status_must_remain_executable_gate(self) -> None:
        manifest: JsonObject = {
            "symbols": {},
            "equations": [],
            "derivations": [],
            "finite_gates": [{"id": "gate_a", "type": "demo"}],
            "qm_experiments": [
                {
                    "id": "experiment_a",
                    "title": "Experiment A",
                    "standard_result": "Declared readout.",
                    "stable_invariant": "Stable table.",
                    "claim_boundary": "Executable only.",
                    "status": "formal_proof",
                    "finite_gates": ["gate_a"],
                    "idt_primitives": {"readout": "declared"},
                }
            ],
            "qm_universal_patterns": [],
            "qm_core_proof_obligations": [],
            "theorem_cards": [],
        }
        rules = load_rule_documents(ROOT / "rules/v8/qm_experiment_residuals.idtl.json")

        report = verify_declarative_rule_documents(manifest, rules, ROOT)

        self.assertFalse(report.ok)
        self.assertEqual("declarative_field_value_not_allowed", report.issues[0].code)


if __name__ == "__main__":
    unittest.main()
