from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.graph_query import GraphQueryError, edit_field, graph_summary, incoming_refs, manifest_sha256


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
