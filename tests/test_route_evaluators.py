"""Regression tests for route/probe evaluator scripts.

These scripts feed the badge-guarded direct evaluators
(``evaluate_born_direct_one_pass``, ``evaluate_qm_direct_one_pass``) and the
human-readable scientific-boundary lane (README "older QM status lane"). They
were previously untested; this file pins their verdict contracts so that a
silent regression (e.g. an imported Hilbert/Born control starting to pass, or
a structural-wall probe collapsing to "no wall detected") is caught here
rather than corrupting the public scientific status.

Design rules:
  * Pure-Python probes (affine_readout_principle,
    born_from_overlap_affine_readout, overlap_uniqueness,
    phase_bundle_j_derivation, fpd_projective_derivation,
    primitive_boundary_qm_chain) are exercised by calling
    ``evaluate_candidate`` / ``evaluate_route`` directly on the module's
    CANDIDATES tuple. No lake, no subprocess.
  * Lake-dependent probes (qm_semantic_kernel_route,
    qm_semantic_content_scaffolds) are NOT exercised via ``build_probe()``
    because that would shell out to ``lake build``. Their contracts are pinned
    via module-level constants (LEAN_COMMAND, MACHINE_CHECKED_SCAFFOLDS,
    STRUCTURAL_TARGET_BLOCKERS, B1_CGSC_CLOSED_CORE, SCAFFOLD_CLOSED_CORE) and
    pure helper functions (``status_from_route``).
  * Manifest-consuming probes (qm_hard_wall_probe, qm_inevitability_route)
    are exercised against the live manifest to pin the *current* scientific
    boundary: the verdict must NOT be the "proved / no-wall" value.
"""

from __future__ import annotations

import os
import unittest
from pathlib import Path
from typing import Any, Iterable

from scripts import evaluate_affine_readout_principle as affine
from scripts import evaluate_born_from_overlap_affine_readout as born_overlap
from scripts import evaluate_fpd_projective_derivation as fpd_projective
from scripts import evaluate_overlap_uniqueness as overlap_unique
from scripts import evaluate_phase_bundle_j_derivation as phase_j
from scripts import evaluate_primitive_boundary_qm_chain as primitive_boundary
from scripts import evaluate_qm_hard_wall_probe as hard_wall
from scripts import evaluate_qm_inevitability_route as inevitability
from scripts import evaluate_qm_semantic_content_scaffolds as scaffolds
from scripts import evaluate_qm_semantic_kernel_route as semantic_kernel


REPO_ROOT = Path(__file__).resolve().parents[1]
LIVE_MANIFEST = REPO_ROOT / "theory_verifier_manifest.json"


def _candidate_by_name(candidates: Iterable[Any], name: str) -> Any:
    """Look up a candidate dataclass by its ``name`` field.

    Works for any candidate type whose instances carry a ``name`` attribute
    (MixCandidate, SelectorCandidate, Candidate, DerivationRoute,
    PrimitiveBoundaryCandidate, etc.).
    """
    for c in candidates:
        if c.name == name:
            return c
    raise AssertionError(f"candidate {name!r} not found in {candidates!r}")


# ---------------------------------------------------------------------------
# Pure-Python Born-side probes (transitive feed into evaluate_born_direct_one_pass)
# ---------------------------------------------------------------------------


class AffineReadoutPrincipleTests(unittest.TestCase):
    """``evaluate_affine_readout_principle`` is imported by
    ``evaluate_born_direct_one_pass``. Regression here silently corrupts the
    badge-guarded DIRECT_FINITE_BORN_ROUTE verdict."""

    def test_intended_winner_hits(self) -> None:
        winner = _candidate_by_name(affine.CANDIDATES, "operational_frequency_affine_mix")
        result = affine.evaluate_candidate(winner)
        self.assertEqual(result.verdict, "AFFINE_READOUT_PRINCIPLE_HIT")
        self.assertNotEqual(result.imports, ("convex_probability_axiom",))

    def test_imported_probability_axiom_control_is_not_clean_hit(self) -> None:
        """Regression guard: if this candidate starts hitting cleanly, the
        Born derivation is being upgraded by importing the target axiom."""
        imported = _candidate_by_name(
            affine.CANDIDATES, "imported_convex_probability_control"
        )
        result = affine.evaluate_candidate(imported)
        self.assertEqual(result.verdict, "IMPORTED_HIT")


class BornFromOverlapAffineReadoutTests(unittest.TestCase):
    """Feeds ``evaluate_born_direct_one_pass``; regression corrupts
    DIRECT_FINITE_BORN_ROUTE_HIT_NOT_UNIVERSAL_PROOF."""

    def test_intended_winner_hits(self) -> None:
        winner = _candidate_by_name(
            born_overlap.CANDIDATES, "affine_born_from_signed_overlap"
        )
        result = born_overlap.evaluate_candidate(winner)
        self.assertEqual(result.verdict, "AFFINE_BORN_SELECTOR_HIT")

    def test_absolute_overlap_selector_is_not_clean_hit(self) -> None:
        """Loses orientation sign, so complement_symmetry / unbiased_zero
        must fail. Regression would mean an absolute-overlap Born selector
        is being accepted as the affine HIT."""
        rejected = _candidate_by_name(born_overlap.CANDIDATES, "absolute_overlap_selector")
        result = born_overlap.evaluate_candidate(rejected)
        self.assertNotEqual(result.verdict, "AFFINE_BORN_SELECTOR_HIT")


class OverlapUniquenessTests(unittest.TestCase):
    """Feeds ``evaluate_born_direct_one_pass``; the UNIQUE_HIT winner is the
    basis for the affine Born selector above."""

    def test_intended_winner_is_unique_hit(self) -> None:
        winner = _candidate_by_name(overlap_unique.CANDIDATES, "normalized_bilinear_overlap")
        result = overlap_unique.evaluate_candidate(winner)
        self.assertEqual(result.verdict, "UNIQUE_HIT")

    def test_absolute_overlap_is_not_unique_hit(self) -> None:
        """Absolute overlap loses orientation sign and must NOT be UNIQUE_HIT;
        the project treats normalized-bilinear overlap as the unique selector,
        not absolute overlap."""
        rejected = _candidate_by_name(overlap_unique.CANDIDATES, "absolute_overlap")
        result = overlap_unique.evaluate_candidate(rejected)
        self.assertNotEqual(result.verdict, "UNIQUE_HIT")


class PhaseBundleJDerivationTests(unittest.TestCase):
    """Feeds ``evaluate_born_direct_one_pass``; the J_DERIVATION_HIT winner
    pins the canonical-quadrature transport that selects the Born square."""

    def test_intended_winner_hits(self) -> None:
        winner = _candidate_by_name(phase_j.CANDIDATES, "canonical_quadrature_J")
        result = phase_j.evaluate_candidate(winner)
        self.assertEqual(result.verdict, "J_DERIVATION_HIT")

    def test_half_speed_rotation_is_not_hit(self) -> None:
        """Regression guard: omega=0.5 must fail quadrature_scale; if it
        passes, the J-derivation no longer selects the canonical quadrature."""
        rejected = _candidate_by_name(phase_j.CANDIDATES, "half_speed_rotation")
        result = phase_j.evaluate_candidate(rejected)
        self.assertNotEqual(result.verdict, "J_DERIVATION_HIT")


# ---------------------------------------------------------------------------
# Pure-Python QM-side route (transitive feed into evaluate_qm_direct_one_pass)
# ---------------------------------------------------------------------------


class FpdProjectiveDerivationTests(unittest.TestCase):
    """Feeds ``evaluate_qm_direct_one_pass`` (and verify_finite_qm_route).
    Regression here silently corrupts the badge-guarded
    DIRECT_FINITE_QM_ROUTE verdict."""

    def test_intended_route_is_derivation_candidate(self) -> None:
        winner = _candidate_by_name(
            fpd_projective.ROUTES, "nusd_plus_conservative_projective_gluing"
        )
        result = fpd_projective.evaluate_route(winner)
        self.assertEqual(result.verdict, "DERIVATION_CANDIDATE")

    def test_b2_core_only_route_is_open_wall(self) -> None:
        """Regression guard: a route that supplies neither NUSD nor gluing
        must be OPEN_WALL, not silently upgraded to DERIVATION_CANDIDATE."""
        rejected = _candidate_by_name(fpd_projective.ROUTES, "b2_core_only")
        result = fpd_projective.evaluate_route(rejected)
        self.assertEqual(result.verdict, "OPEN_WALL")


# ---------------------------------------------------------------------------
# Primitive boundary chain (pure-Python; lake only via build_gate, not tested)
# ---------------------------------------------------------------------------


class PrimitiveBoundaryQMChainTests(unittest.TestCase):
    """Imported by ``evaluate_born_direct_one_pass``. The
    ``full_primitive_boundary_candidate`` is the load-bearing primitive-boundary
    witness; the gate invariant requires exactly one such candidate."""

    def test_full_primitive_boundary_candidate_verdict(self) -> None:
        candidate = _candidate_by_name(
            primitive_boundary.CANDIDATES, "full_primitive_boundary_candidate"
        )
        result = primitive_boundary.evaluate_candidate(candidate)
        self.assertEqual(result.verdict, "PRIMITIVE_BOUNDARY_CANDIDATE")

    def test_exactly_one_primitive_boundary_candidate_exists(self) -> None:
        """The gate invariant that ``build_gate`` relies on: exactly one
        candidate carries verdict ``PRIMITIVE_BOUNDARY_CANDIDATE``. If a future
        edit silently produces two, the primitive-boundary identification is
        no longer unambiguous."""
        primitive_count = sum(
            1
            for c in primitive_boundary.CANDIDATES
            if primitive_boundary.evaluate_candidate(c).verdict
            == "PRIMITIVE_BOUNDARY_CANDIDATE"
        )
        self.assertEqual(primitive_count, 1)


# ---------------------------------------------------------------------------
# Lake-dependent probes: pin contracts WITHOUT calling build_probe
# ---------------------------------------------------------------------------


class SemanticContentScaffoldsContractTests(unittest.TestCase):
    """``evaluate_qm_semantic_content_scaffolds`` invokes
    ``lake build Proofs.QMClosure.QMSemanticContentScaffoldBundle`` at runtime.
    Tests here pin the auditable inventory without invoking lake."""

    def test_lean_command_targets_scaffold_bundle(self) -> None:
        self.assertEqual(
            scaffolds.LEAN_COMMAND,
            "lake build Proofs.QMClosure.QMSemanticContentScaffoldBundle",
        )

    def test_machine_checked_scaffold_inventory_has_seven_entries(self) -> None:
        self.assertEqual(len(scaffolds.MACHINE_CHECKED_SCAFFOLDS), 7)

    def test_structural_target_blockers_match_six_qm_clusters(self) -> None:
        """The structural target blockers must be the six QM structural
        obligations. If this set drifts, the scaffold bundle's auditable
        scope drifts with it."""
        self.assertGreaterEqual(len(scaffolds.STRUCTURAL_TARGET_BLOCKERS), 6)


class SemanticKernelRouteContractTests(unittest.TestCase):
    """``evaluate_qm_semantic_kernel_route`` invokes
    ``lake build Proofs.QMClosure.QMSemanticKernelRoute`` at runtime. Tests
    here pin the auditable constants and the pure helper ``status_from_route``
    without invoking lake."""

    def test_lean_command_targets_semantic_kernel_route(self) -> None:
        self.assertEqual(
            semantic_kernel.LEAN_COMMAND,
            "lake build Proofs.QMClosure.QMSemanticKernelRoute",
        )

    def test_b1_cgsc_closed_core_has_documented_ids(self) -> None:
        """The B1 CGSC closed-core set must be non-empty and contain only
        non-empty strings; this is the auditable set of clusters the route
        treats as closed by the B1 derivation."""
        self.assertGreater(len(semantic_kernel.B1_CGSC_CLOSED_CORE), 0)
        for cid in semantic_kernel.B1_CGSC_CLOSED_CORE:
            self.assertIsInstance(cid, str)
            self.assertTrue(cid)

    def test_status_from_route_rejects_imports(self) -> None:
        """A route with no forbidden imports is CONDITIONAL_READY; the same
        route with any forbidden import is IMPORT_REJECTED. Regression here
        would let an imported Hilbert/Born cluster silently become
        CONDITIONAL_READY."""
        self.assertEqual(
            semantic_kernel.status_from_route("CONDITIONAL_FOO", ()),
            "CONDITIONAL_READY",
        )
        self.assertEqual(
            semantic_kernel.status_from_route("CONDITIONAL_FOO", ("hilbert_space",)),
            "IMPORT_REJECTED",
        )


# ---------------------------------------------------------------------------
# Manifest-consuming probes: pin the CURRENT scientific boundary
# ---------------------------------------------------------------------------


class HardWallProbeTests(unittest.TestCase):
    """``evaluate_qm_hard_wall_probe`` reads the live manifest and reports
    whether the full-QM frontier is open, fatal, or already closed.

    The contract is pinned via the module-level ``OBLIGATION_SPECS`` inventory
    (fast). The slow ``build_probe`` invocation (reads the live manifest,
    ~35s) is gated behind the ``IDT_RUN_SLOW_TESTS`` environment variable so
    the default test lane stays fast; set ``IDT_RUN_SLOW_TESTS=1`` to exercise
    the live scientific-boundary check.
    """

    def test_obligation_specs_classifies_all_21_obligations(self) -> None:
        """Each of the 21 full-QM-closure obligations must appear in the
        hard-wall probe's ``OBLIGATION_SPECS`` with a wall classification
        (``bridge_scaffold`` / ``structural_wall`` / ``boundary``). If a new
        obligation is added to the closure evaluator but not classified here,
        the hard-wall probe silently loses coverage."""
        from scripts.evaluate_full_qm_proof_closure import OBLIGATIONS

        spec_ids = set(hard_wall.OBLIGATION_SPECS.keys())
        obligation_ids = {o.id for o in OBLIGATIONS}
        missing = sorted(obligation_ids - spec_ids)
        extra = sorted(spec_ids - obligation_ids)
        self.assertEqual(
            missing,
            [],
            msg=f"hard-wall probe missing classifications for: {missing}",
        )
        self.assertEqual(
            extra,
            [],
            msg=f"hard-wall probe classifies unknown obligations: {extra}",
        )

    @unittest.skipUnless(
        LIVE_MANIFEST.is_file(), "live manifest not present; run from repo root"
    )
    @unittest.skipUnless(
        os.environ.get("IDT_RUN_SLOW_TESTS"),
        "slow live-manifest probe; set IDT_RUN_SLOW_TESTS=1 to enable",
    )
    def test_wall_is_open_not_fatal_not_closed(self) -> None:
        probe = hard_wall.build_probe(LIVE_MANIFEST)
        self.assertFalse(
            probe.fatal_now,
            msg=(
                f"hard-wall probe reports fatal_now=True (verdict={probe.verdict}); "
                "the public scientific boundary claims an OPEN structural wall"
            ),
        )
        self.assertNotEqual(
            probe.verdict,
            "NO_WALL_DETECTED",
            msg="hard-wall probe reports NO_WALL_DETECTED; the public boundary claims a wall exists",
        )
        self.assertNotEqual(
            probe.verdict,
            "FATAL_WALL",
            msg="hard-wall probe reports FATAL_WALL; the public boundary claims the wall is open",
        )


class InevitabilityRouteProbeTests(unittest.TestCase):
    """``evaluate_qm_inevitability_route`` reads the live manifest and the
    QMInevitabilityRouteDraft.json.

    The contract is pinned via the module-level ``EXPECTED_*`` constants
    (fast). The slow ``build_probe`` invocation (~125s; pulls in many
    transitive evaluators) is gated behind ``IDT_RUN_SLOW_TESTS`` so the
    default test lane stays fast.
    """

    def test_expected_artifact_status_is_route_draft_not_formal_proof(self) -> None:
        """The inevitability artifact is a route draft, NOT a formal proof.
        Regression here would silently upgrade the public claim."""
        self.assertEqual(
            inevitability.EXPECTED_ARTIFACT_STATUS,
            "route_draft_not_formal_proof",
        )

    def test_expected_proof_status_is_open(self) -> None:
        """The inevitability proof must remain OPEN; if this constant ever
        becomes ``formal_proof`` or ``proved``, the route is being upgraded
        to a public claim it cannot support."""
        self.assertEqual(inevitability.EXPECTED_PROOF_STATUS, "open")

    def test_expected_route_status_is_open(self) -> None:
        self.assertEqual(inevitability.EXPECTED_ROUTE_STATUS, "open")

    def test_expected_target_status_is_conditional_route_ready(self) -> None:
        """The target status must remain ``conditional_route_ready``, not
        ``proved`` or ``derived``; the inevitability route is conditional,
        not closed."""
        self.assertEqual(
            inevitability.EXPECTED_TARGET_STATUS, "conditional_route_ready"
        )

    def test_expected_theorem_id_pins_the_inevitability_route(self) -> None:
        """The route theorem id must point at the documented
        hilbert_born_unitary_tensor_follow_from_primitives route, not at a
        derived or proved theorem."""
        self.assertEqual(
            inevitability.EXPECTED_THEOREM_ID,
            "hilbert_born_unitary_tensor_follow_from_primitives_route",
        )

    @unittest.skipUnless(
        LIVE_MANIFEST.is_file(), "live manifest not present; run from repo root"
    )
    @unittest.skipUnless(
        os.environ.get("IDT_RUN_SLOW_TESTS"),
        "slow live-manifest probe; set IDT_RUN_SLOW_TESTS=1 to enable",
    )
    def test_route_is_conditionally_validated_not_proved(self) -> None:
        draft = inevitability.DEFAULT_DRAFT
        if not draft.is_file():
            self.skipTest(f"draft not present: {draft}")
        probe = inevitability.build_probe(draft, LIVE_MANIFEST)
        self.assertNotEqual(
            probe.verdict,
            "INEVITABILITY_PROVED",
            msg=(
                "inevitability probe upgraded to INEVITABILITY_PROVED; "
                "this would be a public overclaim"
            ),
        )
        self.assertNotIn(
            probe.verdict,
            ("ROUTE_DRAFT_INVALID", "TARGET_IMPORT_REJECTED", "TARGET_ROUTE_NOT_READY"),
            msg=(
                f"inevitability probe failed: verdict={probe.verdict}; "
                "the route draft must be valid for the conditional scientific status"
            ),
        )


if __name__ == "__main__":
    unittest.main()
