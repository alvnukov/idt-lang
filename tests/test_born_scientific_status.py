from __future__ import annotations

import unittest

from scripts.check_born_scientific_status import (
    EXPECTED_BORN_DIRECT_VERDICT,
    EXPECTED_BORN_READOUT_VERDICT,
    born_upgrade_markers,
    check_born_obligation_status,
    check_expected_verdict,
    check_workflow_runs_guard,
)


def manifest_with_born_status(status: str) -> dict[str, object]:
    return {
        "qm_core_proof_obligations": [
            {
                "id": "born_rule_derivation",
                "status": status,
            }
        ],
        "theorem_cards": [],
    }


class BornScientificStatusGuardTests(unittest.TestCase):
    def test_expected_verdict_rejects_direct_born_regression(self) -> None:
        check = check_expected_verdict(
            "route.born_direct_one_pass",
            "DIRECT_BORN_ROUTE_BLOCKED",
            EXPECTED_BORN_DIRECT_VERDICT,
        )

        self.assertFalse(check.passed)
        self.assertIn(EXPECTED_BORN_DIRECT_VERDICT, check.detail)

    def test_expected_verdict_rejects_born_readout_regression(self) -> None:
        check = check_expected_verdict(
            "route.born_readout_attempt",
            "OPEN_WALL",
            EXPECTED_BORN_READOUT_VERDICT,
        )

        self.assertFalse(check.passed)
        self.assertIn(EXPECTED_BORN_READOUT_VERDICT, check.detail)

    def test_born_obligation_must_remain_blocked(self) -> None:
        self.assertTrue(check_born_obligation_status(manifest_with_born_status("blocked")).passed)
        self.assertFalse(check_born_obligation_status(manifest_with_born_status("derived")).passed)
        self.assertFalse(check_born_obligation_status(manifest_with_born_status("derived_conditional")).passed)

    def test_missing_born_obligation_fails(self) -> None:
        check = check_born_obligation_status({"qm_core_proof_obligations": [], "theorem_cards": []})

        self.assertFalse(check.passed)
        self.assertIn("missing born_rule_derivation", check.detail)

    def test_formal_born_theorem_card_is_upgrade_marker(self) -> None:
        manifest = manifest_with_born_status("blocked")
        manifest["theorem_cards"] = [
            {
                "id": "bad_born_card",
                "target": "born_rule_derivation",
                "proof_status": "formal_proof",
            }
        ]

        self.assertEqual(("theorem_cards.bad_born_card.proof_status=formal_proof",), born_upgrade_markers(manifest))
        self.assertFalse(check_born_obligation_status(manifest).passed)

    def test_born_dependency_reference_is_upgrade_marker_only_when_formal(self) -> None:
        manifest = manifest_with_born_status("blocked")
        manifest["theorem_cards"] = [
            {
                "id": "open_born_dependency",
                "dependencies": ["born_rule_derivation"],
                "proof_status": "open",
            }
        ]

        self.assertEqual((), born_upgrade_markers(manifest))

    def test_workflow_runs_guard_after_born_probes(self) -> None:
        workflow = """
        run: |
          python scripts/evaluate_born_direct_one_pass.py
          python scripts/evaluate_born_readout_attempt.py
          python scripts/evaluate_s2_born_proof_search.py
          python scripts/evaluate_born_wall_separation.py
          python scripts/check_born_scientific_status.py
        """

        self.assertTrue(check_workflow_runs_guard(workflow).passed)

    def test_workflow_rejects_guard_before_latest_probe(self) -> None:
        workflow = """
        run: |
          python scripts/evaluate_born_direct_one_pass.py
          python scripts/check_born_scientific_status.py
          python scripts/evaluate_born_readout_attempt.py
          python scripts/evaluate_s2_born_proof_search.py
          python scripts/evaluate_born_wall_separation.py
        """

        self.assertFalse(check_workflow_runs_guard(workflow).passed)

    def test_workflow_requires_born_readout_attempt_probe(self) -> None:
        workflow = """
        run: |
          python scripts/evaluate_born_direct_one_pass.py
          python scripts/evaluate_s2_born_proof_search.py
          python scripts/evaluate_born_wall_separation.py
          python scripts/check_born_scientific_status.py
        """

        check = check_workflow_runs_guard(workflow)

        self.assertFalse(check.passed)
        self.assertIn("scripts/evaluate_born_readout_attempt.py", check.detail)


if __name__ == "__main__":
    unittest.main()
