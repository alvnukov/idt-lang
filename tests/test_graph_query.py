from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.graph_query import (
    GraphQueryError,
    add_object,
    edit_field,
    edit_root_field,
    graph_summary,
    incoming_refs,
    manifest_sha256,
    replace_object,
)


class GraphQueryTests(unittest.TestCase):
    def test_summary_and_refs(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            manifest_path = write_sample_manifest(Path(raw_dir))
            summary = graph_summary(manifest_path)
            counts = summary["counts"]
            if not isinstance(counts, dict):
                self.fail("summary counts must be a mapping")
            self.assertEqual(2, counts["symbols"])
            self.assertEqual(1, counts["theorem_cards"])

            refs = incoming_refs(manifest_path, "hbar_I")
            self.assertEqual(
                [{"collection": "theorem_cards", "id": "hbar_lock", "path": "dependencies[0]"}],
                refs,
            )

    def test_safe_edit_requires_current_sha(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            manifest_path = write_sample_manifest(Path(raw_dir))
            old_sha = manifest_sha256(manifest_path)
            new_sha = edit_field(manifest_path, "symbols", "hbar_I", "status", "blocked", old_sha)
            self.assertNotEqual(old_sha, new_sha)

            updated = json.loads(manifest_path.read_text(encoding="utf-8"))
            self.assertEqual("blocked", updated["symbols"]["hbar_I"]["status"])
            with self.assertRaises(GraphQueryError):
                edit_field(manifest_path, "symbols", "hbar_I", "status", "open", old_sha)

    def test_safe_edit_rejects_disallowed_field(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            manifest_path = write_sample_manifest(Path(raw_dir))
            with self.assertRaises(GraphQueryError):
                edit_field(manifest_path, "symbols", "hbar_I", "dimension", "{}", manifest_sha256(manifest_path))

    def test_safe_edit_allows_conditional_proof_status(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            manifest_path = write_sample_manifest(Path(raw_dir))
            edit_field(
                manifest_path,
                "theorem_cards",
                "hbar_lock",
                "proof_status",
                "conditional_proof",
                manifest_sha256(manifest_path),
            )

            updated = json.loads(manifest_path.read_text(encoding="utf-8"))
            self.assertEqual("conditional_proof", updated["theorem_cards"][0]["proof_status"])

    def test_safe_root_edit_updates_theory_version(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            manifest_path = write_sample_manifest(Path(raw_dir))
            old_sha = manifest_sha256(manifest_path)
            new_sha = edit_root_field(manifest_path, "theory_version", "v6.10.1", old_sha)
            self.assertNotEqual(old_sha, new_sha)

            updated = json.loads(manifest_path.read_text(encoding="utf-8"))
            self.assertEqual("v6.10.1", updated["theory_version"])
            with self.assertRaises(GraphQueryError):
                edit_root_field(manifest_path, "theory_version", "6.10.2", new_sha)

    def test_add_object_requires_current_sha_and_unique_id(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            manifest_path = write_sample_manifest(Path(raw_dir))
            old_sha = manifest_sha256(manifest_path)
            new_card = {
                "id": "new_card",
                "statement": "new theorem",
                "role": "theorem",
                "assumptions": [],
                "dependencies": ["hbar_lock"],
                "proof_status": "open",
                "verifier": "",
                "known_failures": [],
                "physical_scope": "test",
                "forbidden_claims": [],
            }

            new_sha = add_object(manifest_path, "theorem_cards", json.dumps(new_card), "hbar_lock", old_sha)
            self.assertNotEqual(old_sha, new_sha)

            updated = json.loads(manifest_path.read_text(encoding="utf-8"))
            self.assertEqual(["hbar_lock", "new_card"], [item["id"] for item in updated["theorem_cards"]])
            with self.assertRaises(GraphQueryError):
                add_object(manifest_path, "theorem_cards", json.dumps(new_card), "hbar_lock", old_sha)

    def test_replace_object_requires_matching_id(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            manifest_path = write_sample_manifest(Path(raw_dir))
            old_sha = manifest_sha256(manifest_path)
            replacement = {
                "id": "hbar_lock",
                "statement": "updated theorem",
                "role": "theorem",
                "assumptions": ["full_QM_I"],
                "dependencies": ["hbar_I"],
                "proof_status": "open",
                "verifier": "",
                "known_failures": [],
                "physical_scope": "updated",
                "forbidden_claims": [],
            }

            replace_object(manifest_path, "theorem_cards", "hbar_lock", json.dumps(replacement), old_sha)

            updated = json.loads(manifest_path.read_text(encoding="utf-8"))
            self.assertEqual("updated theorem", updated["theorem_cards"][0]["statement"])
            with self.assertRaises(GraphQueryError):
                replace_object(
                    manifest_path,
                    "theorem_cards",
                    "hbar_lock",
                    json.dumps({**replacement, "id": "wrong_id"}),
                    manifest_sha256(manifest_path),
                )


def write_sample_manifest(directory: Path) -> Path:
    manifest = {
        "schema_version": "test",
        "theory_version": "test",
        "symbols": {
            "hbar_I": {"status": "open", "dimension": {}},
            "full_QM_I": {"status": "target", "dimension": {}},
        },
        "equations": [],
        "derivations": [],
        "forbidden_paths": [],
        "qm_experiments": [],
        "qm_universal_patterns": [],
        "qm_core_proof_obligations": [],
        "theorem_cards": [
            {
                "id": "hbar_lock",
                "statement": "hbar lock test",
                "role": "theorem",
                "assumptions": [],
                "dependencies": ["hbar_I"],
                "proof_status": "open",
                "verifier": "",
                "known_failures": [],
                "physical_scope": "test",
                "forbidden_claims": [],
            }
        ],
        "finite_gates": [],
    }
    manifest_path = directory / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return manifest_path


if __name__ == "__main__":
    unittest.main()
