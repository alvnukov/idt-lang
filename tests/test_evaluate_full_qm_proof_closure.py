"""Regression tests for the full QM proof closure evaluator.

These tests pin down the card-ordering / shadowing behaviour of
``build_artifact_registry``: when a broad conditional package card and a
specific machine-checked card both reference the same
``full_qm_proof_closure.<id>`` obligation, the stronger (formal) artifact must
win regardless of the order in which the cards are listed in the manifest.

Background: the manifest legitimately lists broad conditional package cards
(``cgsc_finite_exposed_context_package_conditional_artifact`` and siblings)
alongside specific per-obligation machine-checked cards. Both groups carry the
same ``full_qm_proof_closure.<id>`` claim_ref. A naive first-match lookup
silently classified the four machine-checked Born-readout obligations as
``CONDITIONAL_ARTIFACT`` even though real Lean proofs existed on disk.
"""

from __future__ import annotations

import unittest
from pathlib import Path

from scripts.evaluate_full_qm_proof_closure import (
    FORMAL_PROOF_KINDS,
    OBLIGATIONS,
    ProofArtifact,
    ProofObligation,
    artifact_strength_rank,
    build_artifact_registry,
)
from scripts.evaluate_full_qm_proof_attempt import AttemptVerdict  # noqa: F401


REPO_ROOT = Path(__file__).resolve().parents[1]


def _card(
    card_id: str,
    proof_kind: str,
    claim_refs: tuple[str, ...],
    artifact_paths: tuple[str, ...] = ("Proofs/QMClosure/__fake__.lean",),
) -> dict[str, object]:
    """Build a minimal proof_card dict shaped like the manifest entries."""
    return {
        "id": card_id,
        "claim_refs": list(claim_refs),
        "proof_kind": proof_kind,
        "backend": "lean4",
        "artifact_paths": list(artifact_paths),
        "checker_commands": ["lake env lean Proofs/QMClosure/__fake__.lean"],
        "theorem": f"IDT.QMClosure.{card_id}",
    }


def _manifest_with_gate(cards: list[dict[str, object]]) -> dict[str, object]:
    return {
        "symbols": {},
        "theorem_cards": [],
        "finite_gates": [
            {
                "type": "formal_proof_ledger_audit",
                "proof_cards": cards,
            }
        ],
    }


class ArtifactStrengthRankTests(unittest.TestCase):
    def test_formal_proof_kinds_are_strongest(self) -> None:
        for kind in FORMAL_PROOF_KINDS:
            self.assertEqual(artifact_strength_rank(kind), 3)

    def test_conditional_beats_sketch(self) -> None:
        self.assertGreater(
            artifact_strength_rank("conditional_proof"),
            artifact_strength_rank("proof_sketch"),
        )

    def test_unknown_kind_is_weakest(self) -> None:
        self.assertEqual(artifact_strength_rank("something_else"), 0)
        self.assertGreater(artifact_strength_rank("proof_sketch"), 0)


class BuildArtifactRegistryTests(unittest.TestCase):
    """The core regression: shadowing direction must not depend on card order."""

    def setUp(self) -> None:
        # Use a real obligation so the claim_ref prefix matches.
        self.obligation: ProofObligation = next(
            o for o in OBLIGATIONS if o.id == "context_normalization"
        )
        self.ref = f"full_qm_proof_closure.{self.obligation.id}"

    def _write_and_build(self, cards: list[dict[str, object]]) -> dict[str, ProofArtifact]:
        import json
        import tempfile

        # build_artifact_registry reads the manifest from disk, so we materialize
        # an in-memory manifest into a temp file. The artifact path lookup is
        # only relevant for the later check_obligation step, not for registry
        # construction; build_artifact_registry never touches the filesystem
        # beyond reading the manifest JSON.
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".json", delete=False, encoding="utf-8"
        ) as tmp:
            json.dump(_manifest_with_gate(cards), tmp)
            tmp_path = Path(tmp.name)
        try:
            return build_artifact_registry(tmp_path)
        finally:
            tmp_path.unlink(missing_ok=True)

    def test_machine_checked_wins_over_conditional_when_listed_after(self) -> None:
        """Conditional package card appears FIRST; machine-checked SECOND.

        This is the exact ordering in the live manifest gate 173 that previously
        caused all 21 obligations to be classified as CONDITIONAL_ARTIFACT.
        """
        cards = [
            _card(
                "context_normalization_conditional_package_artifact",
                "conditional_proof",
                (self.ref,),
            ),
            _card(
                "context_normalization_machine_checked_artifact",
                "machine_checked_finite_proof",
                (self.ref,),
            ),
        ]
        registry = self._write_and_build(cards)
        self.assertIn(self.obligation.id, registry)
        self.assertEqual(
            registry[self.obligation.id].proof_kind,
            "machine_checked_finite_proof",
        )
        self.assertEqual(
            registry[self.obligation.id].source_card_id,
            "context_normalization_machine_checked_artifact",
        )

    def test_machine_checked_wins_over_conditional_when_listed_before(self) -> None:
        """Reverse order must give the same answer (order-independence)."""
        cards = [
            _card(
                "context_normalization_machine_checked_artifact",
                "machine_checked_finite_proof",
                (self.ref,),
            ),
            _card(
                "context_normalization_conditional_package_artifact",
                "conditional_proof",
                (self.ref,),
            ),
        ]
        registry = self._write_and_build(cards)
        self.assertEqual(
            registry[self.obligation.id].proof_kind,
            "machine_checked_finite_proof",
        )

    def test_conditional_wins_over_sketch(self) -> None:
        cards = [
            _card(
                "context_normalization_sketch_artifact",
                "proof_sketch",
                (self.ref,),
            ),
            _card(
                "context_normalization_conditional_package_artifact",
                "conditional_proof",
                (self.ref,),
            ),
        ]
        registry = self._write_and_build(cards)
        self.assertEqual(
            registry[self.obligation.id].proof_kind,
            "conditional_proof",
        )

    def test_obligation_with_no_matching_card_is_absent(self) -> None:
        cards = [
            _card(
                "unrelated_artifact",
                "machine_checked_finite_proof",
                ("full_qm_proof_closure.spectral_decomposition",),
            )
        ]
        registry = self._write_and_build(cards)
        self.assertNotIn(self.obligation.id, registry)


class LiveManifestFourBornReadoutProofsTest(unittest.TestCase):
    """Smoke check against the real manifest: the four machine-checked
    Born-readout artifacts must be selected for their obligations, not shadowed
    by the earlier conditional package cards.

    This is the test that would have caught the original bug. It does not
    depend on file presence on disk (registry construction ignores the FS);
    it only asserts that the *right card* is selected per obligation.
    """

    LIVE_MANIFEST = REPO_ROOT / "theory_verifier_manifest.json"

    @unittest.skipUnless(
        LIVE_MANIFEST.is_file(),
        "live manifest not present; run from repo root",
    )
    def test_four_born_readout_obligations_resolve_to_machine_checked(self) -> None:
        registry = build_artifact_registry(self.LIVE_MANIFEST)
        for obligation_id in (
            "context_normalization",
            "exclusivity_additivity",
            "coarse_graining_consistency",
            "operational_equivalence_probability",
        ):
            self.assertIn(obligation_id, registry, msg=f"{obligation_id} missing from registry")
            self.assertIn(
                registry[obligation_id].proof_kind,
                FORMAL_PROOF_KINDS,
                msg=(
                    f"{obligation_id} resolved to {registry[obligation_id].proof_kind}"
                    f" (card {registry[obligation_id].source_card_id});"
                    " expected a formal proof kind"
                ),
            )


if __name__ == "__main__":
    unittest.main()
