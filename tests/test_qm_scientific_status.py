from __future__ import annotations

import unittest

from scripts.check_qm_scientific_status import (
    EXPECTED_BADGE_TOKEN,
    EXPECTED_BORN_VERDICT,
    check_expected_verdict,
    check_full_qm_not_upgraded_without_proof,
    check_readme_badge,
    check_workflow_runs_guard,
    full_qm_upgrade_markers,
)


def manifest_with_full_qm_status(status: str) -> dict[str, object]:
    return {
        "symbols": {
            "full_QM_I": {
                "status": status,
                "dimension": {},
            }
        },
        "theorem_cards": [],
        "finite_gates": [],
    }


class QMScientificStatusGuardTests(unittest.TestCase):
    def test_expected_verdict_rejects_route_regression(self) -> None:
        check = check_expected_verdict(
            "route.born_direct_one_pass",
            "DIRECT_BORN_ROUTE_BLOCKED",
            EXPECTED_BORN_VERDICT,
        )

        self.assertFalse(check.passed)
        self.assertIn(EXPECTED_BORN_VERDICT, check.detail)

    def test_readme_badge_requires_conditional_wall_status(self) -> None:
        self.assertTrue(check_readme_badge(f"badge {EXPECTED_BADGE_TOKEN}").passed)
        self.assertFalse(check_readme_badge("badge QM-proved-green").passed)

    def test_workflow_runs_guard_after_qm_route_probes(self) -> None:
        workflow = """
        run: |
          python scripts/evaluate_born_direct_one_pass.py
          python scripts/evaluate_qm_direct_one_pass.py
          python scripts/evaluate_cgsc_qm_one_pass_closure.py
          python scripts/check_qm_scientific_status.py
        """

        self.assertTrue(check_workflow_runs_guard(workflow).passed)

    def test_workflow_rejects_missing_guard_or_guard_before_probes(self) -> None:
        missing_guard = """
        run: |
          python scripts/evaluate_born_direct_one_pass.py
          python scripts/evaluate_qm_direct_one_pass.py
          python scripts/evaluate_cgsc_qm_one_pass_closure.py
        """
        guard_before_probe = """
        run: |
          python scripts/check_qm_scientific_status.py
          python scripts/evaluate_born_direct_one_pass.py
          python scripts/evaluate_qm_direct_one_pass.py
          python scripts/evaluate_cgsc_qm_one_pass_closure.py
        """

        self.assertFalse(check_workflow_runs_guard(missing_guard).passed)
        self.assertFalse(check_workflow_runs_guard(guard_before_probe).passed)

    def test_full_qm_target_status_is_not_an_upgrade(self) -> None:
        check = check_full_qm_not_upgraded_without_proof(
            manifest_with_full_qm_status("target"),
            "PROOF_ARTIFACTS_MISSING",
        )

        self.assertTrue(check.passed)

    def test_full_qm_derived_requires_full_qm_proved_closure(self) -> None:
        manifest = manifest_with_full_qm_status("derived")

        failing_check = check_full_qm_not_upgraded_without_proof(manifest, "PROOF_ARTIFACTS_MISSING")
        allowed_check = check_full_qm_not_upgraded_without_proof(manifest, "FULL_QM_PROVED")

        self.assertFalse(failing_check.passed)
        self.assertIn("symbols.full_QM_I.status=derived", failing_check.detail)
        self.assertTrue(allowed_check.passed)

    def test_full_qm_derived_conditional_is_still_an_upgrade(self) -> None:
        check = check_full_qm_not_upgraded_without_proof(
            manifest_with_full_qm_status("derived_conditional"),
            "CONDITIONAL_PACKAGE_ARTIFACTS_REGISTERED",
        )

        self.assertFalse(check.passed)
        self.assertIn("symbols.full_QM_I.status=derived_conditional", check.detail)

    def test_full_qm_formal_theorem_card_is_upgrade_marker(self) -> None:
        manifest = manifest_with_full_qm_status("target")
        manifest["theorem_cards"] = [
            {
                "id": "bad_full_qm_claim",
                "target": "full_QM_I",
                "proof_status": "formal_proof",
            }
        ]

        markers = full_qm_upgrade_markers(manifest)
        check = check_full_qm_not_upgraded_without_proof(manifest, "PROOF_ARTIFACTS_MISSING")

        self.assertEqual(("theorem_cards.bad_full_qm_claim.proof_status=formal_proof",), markers)
        self.assertFalse(check.passed)

    def test_full_qm_target_refs_are_upgrade_markers(self) -> None:
        manifest = manifest_with_full_qm_status("target")
        manifest["theorem_cards"] = [
            {
                "id": "bad_target_ref_claim",
                "proof_status": "formal_proof",
                "target_refs": [{"id": "full_QM_I"}],
            }
        ]

        self.assertEqual(
            ("theorem_cards.bad_target_ref_claim.proof_status=formal_proof",),
            full_qm_upgrade_markers(manifest),
        )

    def test_forbidden_upgrade_text_is_not_a_full_qm_target(self) -> None:
        manifest = manifest_with_full_qm_status("target")
        manifest["theorem_cards"] = [
            {
                "id": "finite_meta_claim",
                "proof_status": "formal_proof",
                "forbidden_upgrades": ["does_not_prove_full_QM_I"],
            }
        ]

        self.assertEqual((), full_qm_upgrade_markers(manifest))


if __name__ == "__main__":
    unittest.main()
