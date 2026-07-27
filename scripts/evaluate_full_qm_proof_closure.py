from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import scripts.evaluate_full_qm_proof_attempt as full_attempt  # noqa: E402

ClosureVerdict = Literal[
    "FULL_QM_PROVED",
    "CONDITIONAL_PACKAGE_ARTIFACTS_REGISTERED",
    "PROOF_ARTIFACTS_MISSING",
    "IMPORTED_ASSUMPTION_REJECTED",
    "ROUTE_NOT_READY",
]
CheckStatus = Literal[
    "PROVED",
    "CONDITIONAL_ARTIFACT",
    "MISSING_ARTIFACT",
    "SKETCH_ARTIFACT",
    "INCOMPLETE_ARTIFACT",
    "IMPORT_REJECTED",
]


@dataclass(frozen=True)
class ProofArtifact:
    system: str
    file: str
    theorem: str
    check_command: str
    proof_kind: str
    verified: bool
    source_card_id: str


@dataclass(frozen=True)
class ProofObligation:
    id: str
    cluster: str
    required_statement: str
    forbidden_imports: tuple[str, ...]


@dataclass(frozen=True)
class ObligationCheck:
    id: str
    cluster: str
    status: CheckStatus
    reason: str
    artifact: ProofArtifact | None


@dataclass(frozen=True)
class ClosureAttempt:
    verdict: ClosureVerdict
    route_status: full_attempt.AttemptVerdict
    proved: int
    conditional_artifacts: int
    missing_artifacts: int
    sketch_artifacts: int
    incomplete_artifacts: int
    imported_artifacts: int
    checks: list[ObligationCheck]


OBLIGATIONS: tuple[ProofObligation, ...] = (
    ProofObligation(
        id="finite_projection_determinacy",
        cluster="residual_closure",
        required_statement="Derive finite projection determinacy from IDT primitive rules.",
        forbidden_imports=("hilbert_space", "projector_axiom", "born_rule"),
    ),
    ProofObligation(
        id="projective_consistency",
        cluster="residual_closure",
        required_statement="Derive projective consistency without assuming Hilbert projectors.",
        forbidden_imports=("hilbert_space", "projector_axiom", "born_rule"),
    ),
    ProofObligation(
        id="nonunital_stable_distinguishability",
        cluster="fpd_projective_derivation",
        required_statement="Prove NUSD as an IDT theorem or mark it as an explicit boundary assumption.",
        forbidden_imports=("positive_operator", "hilbert_space", "born_rule"),
    ),
    ProofObligation(
        id="conservative_projective_gluing",
        cluster="fpd_projective_derivation",
        required_statement="Prove conservative projective gluing from finite context/facticization rules.",
        forbidden_imports=("projector_axiom", "hilbert_space", "born_rule"),
    ),
    ProofObligation(
        id="spectral_decomposition",
        cluster="representation",
        required_statement="Prove spectral decomposition for admissible carriers from IDT constraints.",
        forbidden_imports=("spectral_theorem_assumed", "hilbert_space", "self_adjoint_operator"),
    ),
    ProofObligation(
        id="rich_d_cl_reversible_symmetry",
        cluster="representation",
        required_statement="Prove enough D_cl-preserving reversible symmetry without importing unitary groups.",
        forbidden_imports=("unitary_group", "wigner_theorem", "hilbert_space"),
    ),
    ProofObligation(
        id="context_normalization",
        cluster="born_readout",
        required_statement="Prove stable normalization for every admissible finite readout context.",
        forbidden_imports=("born_rule", "probability_axiom", "hilbert_space"),
    ),
    ProofObligation(
        id="exclusivity_additivity",
        cluster="born_readout",
        required_statement="Prove additivity over facticized exclusive alternatives.",
        forbidden_imports=("born_rule", "kolmogorov_axioms_assumed", "hilbert_space"),
    ),
    ProofObligation(
        id="coarse_graining_consistency",
        cluster="born_readout",
        required_statement="Prove readout stability under admissible coarse-graining.",
        forbidden_imports=("born_rule", "hilbert_space", "projective_measurement"),
    ),
    ProofObligation(
        id="operational_equivalence_probability",
        cluster="born_readout",
        required_statement="Prove equal probabilities for operationally equivalent readout events.",
        forbidden_imports=("born_rule", "hilbert_space", "trace_rule"),
    ),
    ProofObligation(
        id="d_cl_automorphism_dynamics",
        cluster="dynamics",
        required_statement="Prove reversible inheritance acts as D_cl automorphisms.",
        forbidden_imports=("unitary_evolution", "wigner_theorem", "hilbert_space"),
    ),
    ProofObligation(
        id="overlap_preservation_dynamics",
        cluster="dynamics",
        required_statement="Prove reversible inheritance preserves normalized overlap.",
        forbidden_imports=("unitary_evolution", "inner_product_axiom", "hilbert_space"),
    ),
    ProofObligation(
        id="projective_action",
        cluster="dynamics",
        required_statement="Prove admissible reversible inheritance acts on projective facts.",
        forbidden_imports=("projective_hilbert_space", "wigner_theorem", "unitary_evolution"),
    ),
    ProofObligation(
        id="continuous_inheritance_family",
        cluster="dynamics",
        required_statement="Prove the needed continuous inheritance family or state it as a boundary assumption.",
        forbidden_imports=("stone_theorem", "unitary_group", "schrodinger_equation"),
    ),
    ProofObligation(
        id="generator_closure",
        cluster="dynamics",
        required_statement="Prove generator closure for admissible continuous inheritance.",
        forbidden_imports=("hamiltonian_assumed", "stone_theorem", "unitary_group"),
    ),
    ProofObligation(
        id="product_context_exhaustion",
        cluster="composites",
        required_statement="Prove product-context exhaustion for admissible finite composites.",
        forbidden_imports=("tensor_product_axiom", "hilbert_space", "born_rule"),
    ),
    ProofObligation(
        id="local_tomography",
        cluster="composites",
        required_statement="Prove product readouts separate stable composite facts.",
        forbidden_imports=("complex_hilbert_assumed", "tensor_product_axiom", "trace_rule"),
    ),
    ProofObligation(
        id="monoidal_associativity",
        cluster="composites",
        required_statement="Prove associative composition for admissible context products.",
        forbidden_imports=("tensor_category_assumed", "hilbert_space", "quantum_channel"),
    ),
    ProofObligation(
        id="entanglement_closure",
        cluster="composites",
        required_statement="Prove non-product composite stable facts are represented without hidden joint-only imports.",
        forbidden_imports=("tensor_product_axiom", "hilbert_space", "born_rule"),
    ),
    ProofObligation(
        id="projective_limit_consistency",
        cluster="composites",
        required_statement="Prove consistency of the finite route under admissible projective limits.",
        forbidden_imports=("infinite_dimensional_hilbert_assumed", "c_star_algebra_assumed", "born_rule"),
    ),
    ProofObligation(
        id="physical_phase_scale_boundary",
        cluster="physical_scale",
        required_statement="Keep hbar_I calibrated or provide an independent action-scale theorem artifact.",
        forbidden_imports=("hbar_derived_by_assumption", "planck_units", "known_quantum_scale"),
    ),
)

DEFAULT_MANIFEST = REPO_ROOT / "theory_verifier_manifest.json"
FORMAL_PROOF_KINDS = ("machine_checked_finite_proof", "external_formal_proof")
CONDITIONAL_PROOF_KINDS = ("conditional_proof",)

# Conceptual forbidden-import tokens that have no direct Mathlib representation.
# These are physical or mathematical *principles* (Born rule, Hamiltonian,
# Schrodinger equation, Stone theorem, Wigner theorem, Planck units, etc.)
# rather than Mathlib module/symbol names. They cannot be detected by scanning
# a Lean file body or import list; they are only enforceable at the level of
# the obligation statement and the proof card's declared scope. The metadata
# scan in ``artifact_mentions_forbidden_import`` remains the only check for
# these tokens.
FORBIDDEN_CONCEPTUAL_ONLY: frozenset[str] = frozenset(
    {
        "born_rule",
        "hamiltonian_assumed",
        "hbar_derived_by_assumption",
        "known_quantum_scale",
        "planck_units",
        "probability_axiom",
        "schrodinger_equation",
        "stone_theorem",
        "trace_rule",
        "wigner_theorem",
        "quantum_channel",
    }
)

# Mapping from conceptual forbidden-import tokens to representative Mathlib
# symbols and module path fragments whose presence in a Lean artifact body or
# import list indicates that the forbidden machinery is actually being used.
#
# Design choices:
#   * Conservative: only tokens with a clear Mathlib representation are mapped.
#     A token absent from this mapping (and absent from
#     ``FORBIDDEN_CONCEPTUAL_ONLY``) is checked only via the legacy metadata
#     scan; this preserves backward compatibility with any future obligation
#     that introduces a new forbidden token.
#   * Module path fragments (``Mathlib.Analysis.InnerProductSpace``) catch the
#     case where a Lean file explicitly imports a forbidden module, including
#     via ``import Mathlib.Analysis.InnerProductSpace.Basic``. A bare
#     ``import Mathlib`` is NOT matched as a module path fragment; it is
#     treated as a convenience umbrella import whose actual dependencies are
#     verified by the symbol scan below.
#   * Symbol names (``InnerProductSpace``, ``PositiveSemidefinite``) catch the
#     case where the Lean file body invokes the forbidden machinery directly,
#     even when the import was a bare ``import Mathlib``. Matched as whole
#     identifiers (word-bounded) to avoid incidental substring matches.
FORBIDDEN_IMPORT_BODY_SYMBOLS: dict[str, tuple[str, ...]] = {
    "hilbert_space": (
        "InnerProductSpace",
        "Mathlib.Analysis.InnerProductSpace",
        "HilbertSpace",
    ),
    "complex_hilbert_assumed": (
        "InnerProductSpace",
        "Mathlib.Analysis.InnerProductSpace",
        "HilbertSpace",
    ),
    "infinite_dimensional_hilbert_assumed": (
        "InnerProductSpace",
        "Mathlib.Analysis.InnerProductSpace",
        "HilbertSpace",
        "NormedSpace",
    ),
    "projective_hilbert_space": (
        "Projectivization",
        "Mathlib.LinearAlgebra.Projectivization",
        "OrthogonalProjection",
    ),
    "inner_product_axiom": (
        "InnerProductSpace",
        "Mathlib.Analysis.InnerProductSpace",
        "@inner",
        "inner_product",
    ),
    "kolmogorov_axioms_assumed": (
        "ProbabilityTheory",
        "Mathlib.ProbabilityTheory",
    ),
    "positive_operator": (
        "PositiveSemidefinite",
        "PosSemidefinite",
        "Matrix.PosSemidefinite",
        "Mathlib.LinearAlgebra.Matrix.PosDef",
    ),
    "self_adjoint_operator": (
        "IsHermitian",
        "IsSelfAdjoint",
        "Mathlib.LinearAlgebra.Matrix.Hermitian",
        "Matrix.Hermitian",
    ),
    "spectral_theorem_assumed": (
        "Mathlib.LinearAlgebra.Matrix.SpectralTheorem",
        "SpectralTheorem",
    ),
    "unitary_group": (
        "UnitaryGroup",
        "IsUnitary",
        "Mathlib.LinearAlgebra.UnitaryGroup",
    ),
    "unitary_evolution": (
        "UnitaryGroup",
        "IsUnitary",
        "Mathlib.LinearAlgebra.UnitaryGroup",
    ),
    "tensor_product_axiom": (
        "TensorProduct",
        "Mathlib.LinearAlgebra.TensorProduct",
    ),
    "tensor_category_assumed": (
        "MonoidalCategory",
        "Mathlib.CategoryTheory.Monoidal",
    ),
    "c_star_algebra_assumed": (
        "CStarAlgebra",
        "Mathlib.Analysis.CStarAlgebra",
        "StarAlgebra",
    ),
    "projector_axiom": (
        "OrthogonalProjection",
        "Mathlib.LinearAlgebra.AffineSpace.Projection",
    ),
    "projective_measurement": (
        "OrthogonalProjection",
    ),
}

# Structural patterns for hand-rolled forbidden machinery.
#
# ``FORBIDDEN_IMPORT_BODY_SYMBOLS`` above matches *named Mathlib types*. That is
# necessary but not sufficient: an artifact can build the same mathematical
# object from primitive pieces and never mention the type name. The audit in
# ``INVENTORY_AUDIT.md`` found exactly this. For example
# ``ExclusivityAdditivityProof.lean`` declares
# ``Forbidden imports: born_rule, kolmogorov_axioms_assumed, hilbert_space``
# while defining
#
#     variable (W : H -> C)
#     variable (Gamma : H -> H -> C)
#     sum over A, sum over A, W h * star (W h') * Gamma h h'
#
# which is a sesquilinear form on a complex space with Hermitian kernel, i.e.
# the Hilbert structure without the name. Likewise
# ``ContextNormalizationProof.lean`` states positive semidefiniteness directly
# as ``forall v, sum sum v * v * Gamma >= 0`` while the symbol scan looks for
# ``PositiveSemidefinite``.
#
# These patterns close that gap. They are deliberately conjunctive (several
# independent markers must co-occur) so that incidental use of ``star`` or a
# single summation does not trip the check.
FORBIDDEN_IMPORT_BODY_PATTERNS: dict[str, tuple[tuple[str, str], ...]] = {
    "hilbert_space": (
        ("hand_rolled_complex_sesquilinear_form", "SESQUILINEAR"),
    ),
    "complex_hilbert_assumed": (
        ("hand_rolled_complex_sesquilinear_form", "SESQUILINEAR"),
    ),
    "inner_product_axiom": (
        ("hand_rolled_complex_sesquilinear_form", "SESQUILINEAR"),
    ),
    "positive_operator": (
        ("hand_rolled_positive_semidefinite_form", "PSD_FORM"),
    ),
}

# Concrete regexes for the named structural patterns above.
#
# SESQUILINEAR: complex scalars, conjugation, and a double summation occurring
# together in one artifact body. Any one alone is innocuous; all three together
# are a hand-built sesquilinear form.
#
# PSD_FORM: a universally quantified double summation asserted nonnegative,
# which is the definition of a positive semidefinite form.
_STRUCTURAL_PATTERNS: dict[str, tuple[re.Pattern[str], ...]] = {
    "SESQUILINEAR": (
        re.compile(r"(?:ℂ|\bComplex\b)"),
        re.compile(r"\bstar\b"),
        re.compile(r"∑[\s\S]{0,400}?∑"),
    ),
    "PSD_FORM": (
        re.compile(
            r"∀[^,]{0,120},[\s\S]{0,400}?"
            r"∑[\s\S]{0,400}?∑[\s\S]{0,400}?"
            r"(?:≥\s*0|>=\s*0)"
        ),
    ),
}


_LOCAL_IMPORT = re.compile(r"^import\s+(Proofs\.[A-Za-z0-9_.]+)", re.M)


def _expand_local_imports(body: str, root: Path, _seen: set[str] | None = None) -> str:
    """Return ``body`` concatenated with the bodies of the local modules it imports.

    An artifact that writes ``import Proofs.QMClosure.ExclusivityAdditivityProof``
    and then uses ``actualizationMeasure`` depends on the structure defined
    there just as surely as if it had inlined it. Scanning only the artifact's
    own text lets a forbidden structure enter through a one-line import, which
    is how ``operational_equivalence_probability`` inherits the complex
    sesquilinear measure without mentioning ``star`` itself.

    Cycles and repeated imports are visited once. Missing modules are skipped
    silently: a broken import is a compile-time problem, not a scan problem.
    """
    if _seen is None:
        _seen = set()
    collected = [body]
    for module in _LOCAL_IMPORT.findall(body):
        if module in _seen:
            continue
        _seen.add(module)
        path = root / (module.replace(".", "/") + ".lean")
        try:
            imported = path.read_text(encoding="utf-8")
        except OSError:
            continue
        collected.append(_expand_local_imports(imported, root, _seen))
    return "\n".join(collected)


def _structural_pattern_in_body(pattern_key: str, body: str) -> bool:
    """True when every regex making up ``pattern_key`` matches ``body``.

    Conjunctive by design: a structural pattern is only reported when all of
    its independent markers are present, which keeps incidental matches (a lone
    ``star`` in an unrelated lemma) from being flagged.
    """
    regexes = _STRUCTURAL_PATTERNS.get(pattern_key)
    if not regexes:
        return False
    return all(regex.search(body) for regex in regexes)


# A bare ``import Mathlib`` is treated as a convenience umbrella import. It is
# NOT itself a forbidden-module signal; whether the artifact actually depends
# on forbidden machinery is decided by scanning the Lean body for the
# representative symbols in ``FORBIDDEN_IMPORT_BODY_SYMBOLS``. This list exists
# so that future code can distinguish "umbrella import" from "explicit
# forbidden module import" without hard-coding the string in multiple places.
UMBRELLA_IMPORT_LINES: frozenset[str] = frozenset(
    {
        "import Mathlib",
        "import Mathlib.Tactic",
        "import Mathlib.Data.Nat.Basic",
    }
)


def require_mapping(value: object, field: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise ValueError(f"{field} must be an object")
    return value


def require_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise ValueError(f"{field} must be a list")
    return value


def require_string(value: object, field: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{field} must be a string")
    return value


def require_string_tuple(value: object, field: str) -> tuple[str, ...]:
    return tuple(require_string(item, f"{field}[]") for item in require_list(value, field))


def obligation_ref(obligation_id: str) -> str:
    return f"full_qm_proof_closure.{obligation_id}"


def load_manifest(path: Path) -> dict[str, object]:
    raw: object = json.loads(path.read_text(encoding="utf-8"))
    return require_mapping(raw, "manifest")


def proof_cards_from_manifest(manifest: dict[str, object]) -> list[dict[str, object]]:
    cards: list[dict[str, object]] = []
    for gate_index, raw_gate in enumerate(require_list(manifest.get("finite_gates", []), "finite_gates")):
        gate = require_mapping(raw_gate, f"finite_gates[{gate_index}]")
        if gate.get("type") != "formal_proof_ledger_audit":
            continue
        for card_index, raw_card in enumerate(require_list(gate.get("proof_cards", []), f"finite_gates[{gate_index}].proof_cards")):
            cards.append(require_mapping(raw_card, f"finite_gates[{gate_index}].proof_cards[{card_index}]"))
    return cards


def artifact_from_card(card: dict[str, object], obligation: ProofObligation) -> ProofArtifact | None:
    claim_refs = set(require_string_tuple(card.get("claim_refs", []), "proof_card.claim_refs"))
    accepted_refs = {obligation.id, obligation_ref(obligation.id)}
    if claim_refs.isdisjoint(accepted_refs):
        # A formal_proof card may also cite the long formal-claim reference
        # emitted by ``iter_formal_claims_in_payload`` in the verifier, of the
        # form ``finite_gates.<gate_id>.full_qm_proof_closure.<id>.<field>``.
        # Such a ref is not an exact match for the short obligation ref, so we
        # additionally accept any cited ref that ends with the dotted path
        # ``.<obligation_ref>`` followed by a single status-field segment. This
        # keeps the existing short-ref behaviour intact while allowing cards to
        # satisfy both the closure-evaluator and proof-ledger namespaces.
        obligation_path = obligation_ref(obligation.id)
        long_ref_suffix = f".{obligation_path}."
        if not any(ref.startswith("finite_gates.") and long_ref_suffix in ref for ref in claim_refs):
            return None
    artifact_paths = require_string_tuple(card.get("artifact_paths", []), "proof_card.artifact_paths")
    checker_commands = require_string_tuple(card.get("checker_commands", []), "proof_card.checker_commands")
    proof_kind = require_string(card.get("proof_kind"), "proof_card.proof_kind")
    backend = require_string(card.get("backend"), "proof_card.backend")
    card_id = require_string(card.get("id"), "proof_card.id")
    theorem = require_string(card.get("theorem", card_id), "proof_card.theorem")
    artifact_path = artifact_paths[0] if artifact_paths else ""
    check_command = checker_commands[0] if checker_commands else ""
    return ProofArtifact(
        system=backend,
        file=artifact_path,
        theorem=theorem,
        check_command=check_command,
        proof_kind=proof_kind,
        verified=proof_kind in FORMAL_PROOF_KINDS,
        source_card_id=card_id,
    )


def artifact_strength_rank(proof_kind: str) -> int:
    """Rank proof kinds so a stronger artifact wins over a weaker one when both
    reference the same obligation. Higher rank = stronger evidence.

    Rationale: a `machine_checked_finite_proof` / `external_formal_proof` card
    is a real Lean/verifier artifact and must not be silently shadowed by an
    earlier-listed `conditional_proof` / `proof_sketch` package card that merely
    registers coverage. See the card-ordering hazard audit note: the manifest
    legitimately lists broad conditional package cards alongside specific
    machine-checked cards, and both can carry the same `full_qm_proof_closure.<id>`
    claim_ref. Picking the first match by list order hid real proofs.
    """
    if proof_kind in FORMAL_PROOF_KINDS:
        return 3
    if proof_kind in CONDITIONAL_PROOF_KINDS:
        return 2
    if proof_kind == "proof_sketch":
        return 1
    return 0


def build_artifact_registry(manifest_path: Path) -> dict[str, ProofArtifact]:
    manifest = load_manifest(manifest_path)
    proof_cards = proof_cards_from_manifest(manifest)
    artifacts: dict[str, ProofArtifact] = {}
    for obligation in OBLIGATIONS:
        best: ProofArtifact | None = None
        for card in proof_cards:
            artifact = artifact_from_card(card, obligation)
            if artifact is None:
                continue
            if best is None or artifact_strength_rank(artifact.proof_kind) > artifact_strength_rank(best.proof_kind):
                best = artifact
        if best is not None:
            artifacts[obligation.id] = best
    return artifacts


def _read_artifact_body(artifact: ProofArtifact) -> str:
    """Best-effort read of the artifact's Lean source body.

    Returns the file's text if it exists and is readable; returns the empty
    string otherwise. The body is used only as advisory input to
    ``artifact_mentions_forbidden_import``; an unreadable file falls back to
    the metadata-only check and is reported as INCOMPLETE_ARTIFACT by the
    separate ``artifact_file_is_present`` gate downstream.
    """
    if not artifact.file:
        return ""
    path = REPO_ROOT / artifact.file
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return ""


def _word_in_body(needle: str, body: str) -> bool:
    """Word-boundary substring match.

    Used to scan Lean bodies for representative Mathlib symbols (e.g.
    ``InnerProductSpace``, ``PositiveSemidefinite``) without flagging
    incidental substring matches (e.g. ``inner`` inside ``innerProduct``
    would not match the needle ``@inner``).
    """
    if not needle:
        return False
    # ``re.search`` with ``\b`` boundaries handles identifier-style needles
    # (``InnerProductSpace``, ``IsUnitary``). For module-path needles that
    # contain dots (``Mathlib.Analysis.InnerProductSpace``) ``\b`` still works
    # because ``.`` is not a word character, so the leading ``M`` and trailing
    # ``e``/``c`` etc. anchor the match.
    pattern = r"\b" + re.escape(needle).replace(r"\ ", r"\s+") + r"\b"
    return re.search(pattern, body) is not None


def artifact_mentions_forbidden_import(
    artifact: ProofArtifact, obligation: ProofObligation
) -> str | None:
    """Return the first forbidden import the artifact mentions, else None.

    Two-layer check, evaluated in order:

    1. Legacy metadata scan: the concatenation of card metadata strings
       (``system``, ``file``, ``theorem``, ``check_command``) is searched for
       any forbidden conceptual token as a substring. This is the original
       check and remains the only check for tokens in
       ``FORBIDDEN_CONCEPTUAL_ONLY`` (Born rule, Hamiltonian, Schrodinger
       equation, Stone theorem, Wigner theorem, etc.) — these are physical or
       mathematical principles with no direct Mathlib representation, so they
       can only be enforced at the level of the obligation statement and card
       metadata.

    2. Body scan (new): the artifact Lean file body is searched for
       representative Mathlib symbols and module paths declared in
       ``FORBIDDEN_IMPORT_BODY_SYMBOLS`` for each forbidden token. This catches
       the case where a card claims "does not import hilbert_space" while the
       Lean proof body actually invokes ``InnerProductSpace``,
       ``PositiveSemidefinite``, ``IsUnitary``, ``TensorProduct``, etc. A bare
       ``import Mathlib`` umbrella import is NOT itself flagged; only the
       actual usage of forbidden machinery in the body or an explicit
       forbidden module path in an ``import`` line counts.

    The first forbidden token detected (in ``obligation.forbidden_imports``
    order) wins, so the reported reason is deterministic.
    """
    searchable = " ".join(
        (artifact.system, artifact.file, artifact.theorem, artifact.check_command)
    ).lower()
    body = _read_artifact_body(artifact)
    expanded_body = _expand_local_imports(body, REPO_ROOT)
    for forbidden_import in obligation.forbidden_imports:
        # Layer 1: metadata substring scan (applies to every forbidden token).
        if forbidden_import.lower() in searchable:
            return forbidden_import
        # Layer 2: body symbol scan (applies only to tokens with a known
        # Mathlib representation; conceptual-only tokens are skipped here
        # because they cannot be detected by body inspection).
        if forbidden_import in FORBIDDEN_CONCEPTUAL_ONLY:
            continue
        symbols = FORBIDDEN_IMPORT_BODY_SYMBOLS.get(forbidden_import)
        if symbols and any(_word_in_body(symbol, body) for symbol in symbols):
            return forbidden_import
        # Layer 3: structural pattern scan over the artifact body together with
        # the bodies of the local Proofs modules it imports. Catches machinery
        # that is built by hand from primitive pieces (and therefore never
        # mentions the Mathlib type name layer 2 looks for), including the case
        # where it is inherited through a local import.
        patterns = FORBIDDEN_IMPORT_BODY_PATTERNS.get(forbidden_import)
        if patterns and any(
            _structural_pattern_in_body(key, expanded_body)
            for _name, key in patterns
        ):
            return forbidden_import
    return None


def artifact_has_required_fields(artifact: ProofArtifact) -> bool:
    fields = (artifact.system, artifact.file, artifact.theorem, artifact.check_command)
    return all(field.strip() for field in fields)


def artifact_file_is_present(artifact: ProofArtifact) -> bool:
    artifact_path = REPO_ROOT / artifact.file
    return artifact_path.is_file()


def check_obligation(obligation: ProofObligation, artifacts: dict[str, ProofArtifact]) -> ObligationCheck:
    artifact = artifacts.get(obligation.id)
    if artifact is None:
        return ObligationCheck(
            id=obligation.id,
            cluster=obligation.cluster,
            status="MISSING_ARTIFACT",
            reason="no machine-checkable proof artifact is registered",
            artifact=None,
        )
    forbidden_import = artifact_mentions_forbidden_import(artifact, obligation)
    if forbidden_import is not None:
        return ObligationCheck(
            id=obligation.id,
            cluster=obligation.cluster,
            status="IMPORT_REJECTED",
            reason=f"artifact mentions forbidden target import: {forbidden_import}",
            artifact=artifact,
        )
    if artifact.proof_kind == "proof_sketch":
        return ObligationCheck(
            id=obligation.id,
            cluster=obligation.cluster,
            status="SKETCH_ARTIFACT",
            reason="proof-ledger card is explicitly a proof sketch, not a formal proof",
            artifact=artifact,
        )
    if not artifact_has_required_fields(artifact):
        return ObligationCheck(
            id=obligation.id,
            cluster=obligation.cluster,
            status="INCOMPLETE_ARTIFACT",
            reason="artifact exists but lacks required fields",
            artifact=artifact,
        )
    if not artifact_file_is_present(artifact):
        return ObligationCheck(
            id=obligation.id,
            cluster=obligation.cluster,
            status="INCOMPLETE_ARTIFACT",
            reason="artifact file is not present in the repository",
            artifact=artifact,
        )
    if artifact.proof_kind in CONDITIONAL_PROOF_KINDS:
        return ObligationCheck(
            id=obligation.id,
            cluster=obligation.cluster,
            status="CONDITIONAL_ARTIFACT",
            reason="machine-checkable conditional package artifact is registered, but this is not a formal proof from primitives",
            artifact=artifact,
        )
    if not artifact.verified:
        return ObligationCheck(
            id=obligation.id,
            cluster=obligation.cluster,
            status="INCOMPLETE_ARTIFACT",
            reason="artifact exists but proof_kind is not a recognized formal or conditional machine-checked artifact",
            artifact=artifact,
        )
    return ObligationCheck(
        id=obligation.id,
        cluster=obligation.cluster,
        status="PROVED",
        reason="registered proof artifact is complete and locally grounded",
        artifact=artifact,
    )


def build_closure_attempt(manifest_path: Path = DEFAULT_MANIFEST) -> ClosureAttempt:
    route_attempt = full_attempt.build_attempt()
    if route_attempt.verdict not in ("CONDITIONAL_FULL_QM_ROUTE", "FULL_QM_PROVED"):
        return ClosureAttempt(
            verdict="ROUTE_NOT_READY",
            route_status=route_attempt.verdict,
            proved=0,
            conditional_artifacts=0,
            missing_artifacts=0,
            sketch_artifacts=0,
            incomplete_artifacts=0,
            imported_artifacts=0,
            checks=[],
        )
    artifacts = build_artifact_registry(manifest_path)
    checks = [check_obligation(obligation, artifacts) for obligation in OBLIGATIONS]
    proved = sum(1 for check in checks if check.status == "PROVED")
    conditional = sum(1 for check in checks if check.status == "CONDITIONAL_ARTIFACT")
    missing = sum(1 for check in checks if check.status == "MISSING_ARTIFACT")
    sketch = sum(1 for check in checks if check.status == "SKETCH_ARTIFACT")
    incomplete = sum(1 for check in checks if check.status == "INCOMPLETE_ARTIFACT")
    imported = sum(1 for check in checks if check.status == "IMPORT_REJECTED")
    if imported > 0:
        verdict: ClosureVerdict = "IMPORTED_ASSUMPTION_REJECTED"
    elif missing > 0 or sketch > 0 or incomplete > 0:
        verdict = "PROOF_ARTIFACTS_MISSING"
    elif conditional > 0:
        verdict = "CONDITIONAL_PACKAGE_ARTIFACTS_REGISTERED"
    else:
        verdict = "FULL_QM_PROVED"
    return ClosureAttempt(
        verdict=verdict,
        route_status=route_attempt.verdict,
        proved=proved,
        conditional_artifacts=conditional,
        missing_artifacts=missing,
        sketch_artifacts=sketch,
        incomplete_artifacts=incomplete,
        imported_artifacts=imported,
        checks=checks,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Try to close the conditional full-QM route as a proof.")
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--output-json", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    attempt = build_closure_attempt(Path(str(args.manifest)))
    print(
        f"full_qm_proof_closure={attempt.verdict} "
        f"route_status={attempt.route_status} proved={attempt.proved} "
        f"conditional_artifacts={attempt.conditional_artifacts} "
        f"missing_artifacts={attempt.missing_artifacts} "
        f"sketch_artifacts={attempt.sketch_artifacts} "
        f"incomplete_artifacts={attempt.incomplete_artifacts} "
        f"imported_artifacts={attempt.imported_artifacts}"
    )
    for check in attempt.checks:
        print(f"{check.status} {check.id} [{check.cluster}]: {check.reason}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(attempt), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if attempt.verdict in ("IMPORTED_ASSUMPTION_REJECTED", "ROUTE_NOT_READY"):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
