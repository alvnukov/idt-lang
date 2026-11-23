"""Every new bench_* campaign must have immutable, replayable source submissions."""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from scripts.replay_primitive_probe_campaign import TOPIC_BUNDLES

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"


class BenchSourcePacks(unittest.TestCase):
    def test_campaigns_have_pinned_source_submissions(self) -> None:
        prefix, suffix = "primitive_", "_inventory.json"
        packs = {
            path.name.removeprefix(prefix).removesuffix(suffix): path
            for path in DATA.glob("primitive_bench_*_inventory.json")
        }
        campaigns = {key for key in TOPIC_BUNDLES if key.startswith("bench_")}
        self.assertIn("bench_contact_composition", campaigns)
        self.assertEqual(set(packs), campaigns)
        for key, path in sorted(packs.items()):
            with self.subTest(campaign=key), tempfile.TemporaryDirectory() as scratch:
                # The existing archiver validates source hashes/spans and emits
                # canonical submissions. Never update the published baselines here.
                subprocess.run(
                    [
                        sys.executable, "-B", "scripts/archive_existing_primitives.py",
                        "--inventory", str(path), "--history-dir", scratch,
                    ],
                    cwd=ROOT, check=True, capture_output=True,
                )
                submitted: list[str] = []
                for request in sorted((Path(scratch) / "submissions").glob("*.json")):
                    self.assertRegex(request.stem, r"^[0-9a-f]{64}$")
                    raw = request.read_bytes()
                    published = DATA / "candidate_history"
                    self.assertEqual(raw, (published / "submissions" / request.name).read_bytes())
                    # The initial observation, unlike the submission, includes
                    # provenance of the environment at deposit time.
                    pin = json.loads((published / "baselines" / request.name).read_bytes())
                    self.assertEqual(pin["submission"], request.stem)
                    observation = pin["observation"]
                    self.assertIsInstance(observation, str)
                    self.assertTrue(re.fullmatch(r"[0-9a-f]{64}", observation))
                    self.assertTrue((published / "observations" / (observation + ".json.gz")).is_file())
                    candidate, = json.loads(raw)["candidates"]
                    source, = candidate["sources"]
                    self.assertEqual(source["first_line"], 1)
                    name: str = source["path"]
                    self.assertRegex(name, r"^scripts/probe_[a-z0-9_]+\.py$")
                    self.assertEqual(source["last_line"], len((ROOT / name).read_bytes().splitlines()))
                    submitted.append(Path(name).stem)
                self.assertCountEqual(submitted, TOPIC_BUNDLES[key])
