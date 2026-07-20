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
    FORBIDDEN_CONCEPTUAL_ONLY,
    FORBIDDEN_IMPORT_BODY_SYMBOLS,
    OBLIGATIONS,
    ProofArtifact,
    ProofObligation,
    _word_in_body,
    artifact_mentions_forbidden_import,
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


def _artifact(
    artifact_id: str = "test_artifact",
    file_path: str = "Proofs/QMClosure/ContextNormalizationProof.lean",
    proof_kind: str = "machine_checked_finite_proof",
) -> ProofArtifact:
    """Build a ProofArtifact for body-scan tests.

    The default file path points at a real existing Lean artifact so that
    ``_read_artifact_body`` returns its actual body. Tests that want a
    synthetic body should override ``file_path`` with a temp file.
    """
    return ProofArtifact(
        system="lean4",
        file=file_path,
        theorem=f"IDT.QMClosure.{artifact_id}",
        check_command=f"lake env lean {file_path}",
        proof_kind=proof_kind,
        verified=proof_kind in FORMAL_PROOF_KINDS,
        source_card_id=artifact_id,
    )


def _obligation(
    oid: str = "context_normalization",
    forbidden_imports: tuple[str, ...] = ("hilbert_space",),
) -> ProofObligation:
    return ProofObligation(
        id=oid,
        cluster="test_cluster",
        required_statement="test required statement",
        forbidden_imports=forbidden_imports,
    )


class WordInBodyTests(unittest.TestCase):
    """Unit tests for the body-symbol matcher.

    These pin down the word-boundary behaviour so that future edits to the
    matcher do not silently introduce substring false positives (e.g.
    ``inner`` matching inside ``innerProduct``).
    """

    def test_exact_identifier_match(self) -> None:
        self.assertTrue(_word_in_body("InnerProductSpace", "InnerProductSpace α"))

    def test_identifier_match_inside_larger_body(self) -> None:
        body = "import Mathlib\n\nvariable [InnerProductSpace α]\n"
        self.assertTrue(_word_in_body("InnerProductSpace", body))

    def test_substring_without_word_boundary_does_not_match(self) -> None:
        # ``inner`` is a substring of ``innerProduct`` but the matcher anchors
        # on word boundaries, so the needle ``@inner`` does not match.
        self.assertFalse(_word_in_body("@inner", "have innerProduct := 1"))

    def test_module_path_with_dots_matches(self) -> None:
        body = "import Mathlib.Analysis.InnerProductSpace.Basic\n"
        self.assertTrue(_word_in_body("Mathlib.Analysis.InnerProductSpace", body))

    def test_empty_needle_does_not_match(self) -> None:
        self.assertFalse(_word_in_body("", "any body"))
        self.assertFalse(_word_in_body("symbol", ""))


class ForbiddenImportBodyScanTests(unittest.TestCase):
    """Body-scan layer of ``artifact_mentions_forbidden_import``.

    These tests verify that:
      * real Lean bodies that DO invoke forbidden Mathlib machinery are flagged;
      * real Lean bodies that do NOT invoke forbidden machinery pass cleanly;
      * conceptual-only forbidden tokens (Born rule, Hamiltonian, etc.) are
        still enforced via the metadata scan and skipped by the body scan;
      * bare ``import Mathlib`` umbrella imports are NOT themselves flagged.
    """

    def test_real_born_readout_body_passes_hilbert_space_scan(self) -> None:
        """ContextNormalizationProof.lean uses only Finset/linarith and must
        pass the hilbert_space body scan."""
        artifact = _artifact(file_path="Proofs/QMClosure/ContextNormalizationProof.lean")
        obligation = _obligation(forbidden_imports=("hilbert_space",))
        self.assertIsNone(artifact_mentions_forbidden_import(artifact, obligation))

    def test_real_projective_action_body_passes_unitary_scan(self) -> None:
        """ProjectiveActionProof.lean must pass the unitary_evolution scan."""
        artifact = _artifact(
            artifact_id="projective_action",
            file_path="Proofs/QMClosure/ProjectiveActionProof.lean",
        )
        obligation = _obligation(
            oid="projective_action",
            forbidden_imports=("unitary_evolution",),
        )
        self.assertIsNone(artifact_mentions_forbidden_import(artifact, obligation))

    def test_synthetic_body_with_inner_product_space_is_flagged(self) -> None:
        """A Lean body that invokes ``InnerProductSpace`` is flagged for an
        obligation that forbids ``hilbert_space``."""
        import tempfile

        body = (
            "import Mathlib\n\n"
            "variable [InnerProductSpace α]\n\n"
            "theorem foo : True := trivial\n"
        )
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", delete=False, encoding="utf-8"
        ) as tmp:
            tmp.write(body)
            tmp_path = tmp.name
        rel_path = str(Path(tmp_path).relative_to(REPO_ROOT)) if str(REPO_ROOT) in tmp_path else tmp_path
        try:
            # If the temp file is not under REPO_ROOT, _read_artifact_body
            # resolves it relative to REPO_ROOT and returns "" — which would
            # make the test trivially pass. To make the test meaningful we
            # place the temp file inside the repo under tests/.
            tmp_in_repo = REPO_ROOT / "tests" / "_tmp_forbidden_import_probe.lean"
            tmp_in_repo.write_text(body, encoding="utf-8")
            try:
                artifact = ProofArtifact(
                    system="lean4",
                    file="tests/_tmp_forbidden_import_probe.lean",
                    theorem="IDT.test.probe",
                    check_command="lake env lean tests/_tmp_forbidden_import_probe.lean",
                    proof_kind="machine_checked_finite_proof",
                    verified=True,
                    source_card_id="probe_artifact",
                )
                obligation = _obligation(forbidden_imports=("hilbert_space",))
                flagged = artifact_mentions_forbidden_import(artifact, obligation)
                self.assertEqual(flagged, "hilbert_space")
            finally:
                tmp_in_repo.unlink(missing_ok=True)
        finally:
            Path(tmp_path).unlink(missing_ok=True)
        # Silence the unused rel_path warning; the variable exists only to
        # document the relative-path branch we explicitly avoided.
        del rel_path

    def test_synthetic_body_with_positive_semidefinite_is_flagged(self) -> None:
        """A Lean body that invokes ``PositiveSemidefinite`` is flagged for an
        obligation that forbids ``positive_operator``."""
        body = (
            "import Mathlib\n\n"
            "theorem foo (M : Matrix n n ℂ) (h : M.PositiveSemidefinite) : True := trivial\n"
        )
        tmp_in_repo = REPO_ROOT / "tests" / "_tmp_forbidden_import_probe.lean"
        tmp_in_repo.write_text(body, encoding="utf-8")
        try:
            artifact = ProofArtifact(
                system="lean4",
                file="tests/_tmp_forbidden_import_probe.lean",
                theorem="IDT.test.probe",
                check_command="lake env lean tests/_tmp_forbidden_import_probe.lean",
                proof_kind="machine_checked_finite_proof",
                verified=True,
                source_card_id="probe_artifact",
            )
            obligation = _obligation(
                oid="nonunital_stable_distinguishability",
                forbidden_imports=("positive_operator",),
            )
            flagged = artifact_mentions_forbidden_import(artifact, obligation)
            self.assertEqual(flagged, "positive_operator")
        finally:
            tmp_in_repo.unlink(missing_ok=True)

    def test_bare_import_mathlib_is_not_flagged_as_unitary(self) -> None:
        """A body that only has ``import Mathlib`` (umbrella) and uses no
        forbidden symbols must pass the unitary_evolution scan."""
        body = (
            "import Mathlib\n\n"
            "theorem foo (n : Nat) : n + 0 = n := by simp\n"
        )
        tmp_in_repo = REPO_ROOT / "tests" / "_tmp_forbidden_import_probe.lean"
        tmp_in_repo.write_text(body, encoding="utf-8")
        try:
            artifact = ProofArtifact(
                system="lean4",
                file="tests/_tmp_forbidden_import_probe.lean",
                theorem="IDT.test.probe",
                check_command="lake env lean tests/_tmp_forbidden_import_probe.lean",
                proof_kind="machine_checked_finite_proof",
                verified=True,
                source_card_id="probe_artifact",
            )
            obligation = _obligation(
                oid="d_cl_automorphism_dynamics",
                forbidden_imports=("unitary_evolution", "wigner_theorem", "hilbert_space"),
            )
            # wigner_theorem is conceptual-only; unitary_evolution and
            # hilbert_space have body mappings but the body uses none of them.
            self.assertIsNone(artifact_mentions_forbidden_import(artifact, obligation))
        finally:
            tmp_in_repo.unlink(missing_ok=True)

    def test_conceptual_only_token_skipped_by_body_scan(self) -> None:
        """A conceptual-only token (e.g. ``wigner_theorem``) has no body
        mapping and is skipped by the body scan, so a body that incidentally
        contains the substring 'wigner' would not be flagged via the body."""
        # Build a body that does NOT match any mapped Mathlib symbol for any
        # token in FORBIDDEN_IMPORT_BODY_SYMBOLS, and verify a conceptual-only
        # obligation returns None.
        body = "theorem foo : True := trivial\n"
        tmp_in_repo = REPO_ROOT / "tests" / "_tmp_forbidden_import_probe.lean"
        tmp_in_repo.write_text(body, encoding="utf-8")
        try:
            artifact = ProofArtifact(
                system="lean4",
                file="tests/_tmp_forbidden_import_probe.lean",
                theorem="IDT.test.probe",
                check_command="lake env lean tests/_tmp_forbidden_import_probe.lean",
                proof_kind="machine_checked_finite_proof",
                verified=True,
                source_card_id="probe_artifact",
            )
            obligation = _obligation(
                oid="rich_d_cl_reversible_symmetry",
                forbidden_imports=("wigner_theorem",),
            )
            self.assertIsNone(artifact_mentions_forbidden_import(artifact, obligation))
        finally:
            tmp_in_repo.unlink(missing_ok=True)

    def test_metadata_scan_still_catches_conceptual_token_in_metadata(self) -> None:
        """Even though ``wigner_theorem`` has no body mapping, it is still
        enforced via the metadata scan if the card declares it in metadata."""
        body = "theorem foo : True := trivial\n"
        tmp_in_repo = REPO_ROOT / "tests" / "_tmp_forbidden_import_probe.lean"
        tmp_in_repo.write_text(body, encoding="utf-8")
        try:
            artifact = ProofArtifact(
                # The metadata field "system" deliberately mentions the token.
                system="lean4_with_wigner_theorem",
                file="tests/_tmp_forbidden_import_probe.lean",
                theorem="IDT.test.probe",
                check_command="lake env lean tests/_tmp_forbidden_import_probe.lean",
                proof_kind="machine_checked_finite_proof",
                verified=True,
                source_card_id="probe_artifact",
            )
            obligation = _obligation(
                oid="rich_d_cl_reversible_symmetry",
                forbidden_imports=("wigner_theorem",),
            )
            flagged = artifact_mentions_forbidden_import(artifact, obligation)
            self.assertEqual(flagged, "wigner_theorem")
        finally:
            tmp_in_repo.unlink(missing_ok=True)

    def test_first_matching_forbidden_token_wins_in_declaration_order(self) -> None:
        """When multiple forbidden tokens could fire, the one declared first
        in ``obligation.forbidden_imports`` is reported."""
        body = (
            "import Mathlib\n\n"
            "variable [InnerProductSpace α]\n"
            "variable [PositiveSemidefinite M]\n"
        )
        tmp_in_repo = REPO_ROOT / "tests" / "_tmp_forbidden_import_probe.lean"
        tmp_in_repo.write_text(body, encoding="utf-8")
        try:
            artifact = ProofArtifact(
                system="lean4",
                file="tests/_tmp_forbidden_import_probe.lean",
                theorem="IDT.test.probe",
                check_command="lake env lean tests/_tmp_forbidden_import_probe.lean",
                proof_kind="machine_checked_finite_proof",
                verified=True,
                source_card_id="probe_artifact",
            )
            # hilbert_space is declared before positive_operator; the body
            # contains InnerProductSpace (hilbert_space mapping) and
            # PositiveSemidefinite (positive_operator mapping), so the
            # first-declared token wins.
            obligation = _obligation(
                oid="spectral_decomposition",
                forbidden_imports=("hilbert_space", "positive_operator"),
            )
            flagged = artifact_mentions_forbidden_import(artifact, obligation)
            self.assertEqual(flagged, "hilbert_space")
        finally:
            tmp_in_repo.unlink(missing_ok=True)


class ForbiddenImportMappingCoverageTests(unittest.TestCase):
    """Structural sanity checks on the curated mapping.

    These pin down the design invariant that every forbidden token used by
    any obligation is either in FORBIDDEN_CONCEPTUAL_ONLY or has at least one
    representative body symbol. This prevents a future obligation from
    introducing a forbidden token that silently falls through both layers.
    """

    def test_every_obligation_token_is_covered(self) -> None:
        all_tokens: set[str] = set()
        for obligation in OBLIGATIONS:
            all_tokens.update(obligation.forbidden_imports)
        uncovered = sorted(
            token
            for token in all_tokens
            if token not in FORBIDDEN_CONCEPTUAL_ONLY
            and token not in FORBIDDEN_IMPORT_BODY_SYMBOLS
        )
        self.assertEqual(
            uncovered,
            [],
            f"forbidden tokens have neither conceptual-only nor body-symbol "
            f"coverage: {uncovered}",
        )

    def test_every_mapped_token_has_at_least_one_symbol(self) -> None:
        empty_mappings = sorted(
            token
            for token, symbols in FORBIDDEN_IMPORT_BODY_SYMBOLS.items()
            if not symbols
        )
        self.assertEqual(
            empty_mappings,
            [],
            f"FORBIDDEN_IMPORT_BODY_SYMBOLS has empty mappings for: {empty_mappings}",
        )

    def test_conceptual_only_and_body_symbol_sets_are_disjoint(self) -> None:
        overlap = sorted(FORBIDDEN_CONCEPTUAL_ONLY & set(FORBIDDEN_IMPORT_BODY_SYMBOLS))
        self.assertEqual(
            overlap,
            [],
            f"tokens classified as both conceptual-only and body-symbol: {overlap}",
        )


class LiveManifestForbiddenImportScanTests(unittest.TestCase):
    """End-to-end: against the live manifest, the four Born-readout + one
    projective_action machine-checked cards must all pass the body scan.

    This is the test that would catch a future edit that adds forbidden
    Mathlib machinery to a proof body while the card still claims a clean
    forbidden-import contract.
    """

    LIVE_MANIFEST = REPO_ROOT / "theory_verifier_manifest.json"

    @unittest.skipUnless(
        LIVE_MANIFEST.is_file(),
        "live manifest not present; run from repo root",
    )
    def test_five_machine_checked_cards_pass_body_scan(self) -> None:
        registry = build_artifact_registry(self.LIVE_MANIFEST)
        expected_proved = (
            "context_normalization",
            "exclusivity_additivity",
            "coarse_graining_consistency",
            "operational_equivalence_probability",
            "projective_action",
        )
        for obligation_id in expected_proved:
            self.assertIn(obligation_id, registry)
            artifact = registry[obligation_id]
            obligation = next(o for o in OBLIGATIONS if o.id == obligation_id)
            flagged = artifact_mentions_forbidden_import(artifact, obligation)
            self.assertIsNone(
                flagged,
                msg=(
                    f"{obligation_id} body scan flagged forbidden token "
                    f"{flagged!r}; the Lean artifact must not invoke "
                    "InnerProductSpace / PositiveSemidefinite / IsUnitary / "
                    "TensorProduct / etc."
                ),
            )


if __name__ == "__main__":
    unittest.main()
