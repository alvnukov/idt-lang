from __future__ import annotations

import io
import json
import subprocess
import sys
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

from scripts import replay_primitive_probe_campaign as campaign


class PrimitiveProbeCampaignTests(unittest.TestCase):
    def test_stock_certificates_and_carrier_controls_execute(self) -> None:
        for probe in ("probe_stock_error_certificates", "probe_carrier_resolution"):
            with self.subTest(probe=probe):
                result = campaign.replay(probe, 20)
                self.assertEqual(result["status"], "replayed", result["stderr"])

    def test_registry_is_explicit_ordered_and_unique(self) -> None:
        all_probes = campaign.BUNDLES["all"]
        self.assertEqual(
            all_probes, tuple(probe for probes in campaign.TOPIC_BUNDLES.values() for probe in probes)
        )
        self.assertEqual(len(all_probes), 42)
        self.assertEqual(len(set(all_probes)), 42)
        self.assertLess(len(campaign.BUNDLES["fast"]), len(all_probes))
        self.assertLessEqual(set(campaign.BUNDLES["fast"]), set(all_probes))
        for probe in all_probes:
            with self.subTest(probe=probe):
                self.assertTrue((campaign.ROOT / "scripts" / f"{probe}.py").is_file())

    def test_list_is_read_only_and_can_filter_bundle(self) -> None:
        out = io.StringIO()
        with patch.object(campaign, "replay") as replay, redirect_stdout(out):
            code = campaign.main(["--list", "--bundle", "benchmarks", "--json"])
        self.assertEqual(code, 0)
        self.assertEqual(
            json.loads(out.getvalue())["bundles"],
            {
                "benchmarks": [
                    "probe_interferometer_benchmark",
                    "probe_trigger_alignment",
                    "probe_transparency_shutter",
                ]
            },
        )
        replay.assert_not_called()

    def test_replay_exit_codes_not_output_determine_process_status(self) -> None:
        probe = campaign.BUNDLES["fast"][0]
        for returncode, status in ((0, "replayed"), (2, "nonzero_exit"), (-9, "nonzero_exit")):
            with self.subTest(returncode=returncode):
                process = subprocess.CompletedProcess(
                    args=[], returncode=returncode, stdout=b"passed\nfailure\n", stderr=b"\xff"
                )
                with patch.object(subprocess, "run", return_value=process) as run:
                    result = campaign.replay(probe, 9)
                self.assertEqual(
                    result,
                    {
                        "probe": probe,
                        "status": status,
                        "returncode": returncode,
                        "stdout": "passed\nfailure\n",
                        "stderr": "�",
                        "error": None,
                    },
                )
                run.assert_called_once_with(
                    [sys.executable, "-B", "-E", "-O", "-m", f"scripts.{probe}"],
                    cwd=campaign.ROOT,
                    capture_output=True,
                    stdin=subprocess.DEVNULL,
                    timeout=9,
                    check=False,
                )

    def test_timeout_captures_partial_output(self) -> None:
        probe = campaign.BUNDLES["fast"][0]
        error = subprocess.TimeoutExpired(probe, 3, output=b"partial\n")
        with patch.object(subprocess, "run", side_effect=error):
            result = campaign.replay(probe, 3)
        self.assertEqual(result["status"], "timeout")
        self.assertIsNone(result["returncode"])
        self.assertEqual(result["stdout"], "partial\n")
        self.assertEqual(result["error"], "exceeded 3s")

    def test_launch_failure_and_missing_source_are_errors(self) -> None:
        probe = campaign.BUNDLES["fast"][0]
        with patch.object(subprocess, "run", side_effect=OSError("launch failed")):
            result = campaign.replay(probe, 3)
        self.assertEqual(result["status"], "error")
        self.assertIsNone(result["returncode"])
        self.assertEqual(result["error"], "launch failed")
        with patch.object(Path, "is_file", return_value=False), patch.object(
            subprocess, "run"
        ) as run:
            missing = campaign.replay(probe, 3)
        self.assertEqual(missing["status"], "error")
        self.assertEqual(missing["error"], f"missing probe source: scripts/{probe}.py")
        run.assert_not_called()

    def test_bundle_continues_after_error_and_returns_nonzero(self) -> None:
        out = io.StringIO()
        process = subprocess.CompletedProcess(args=[], returncode=0, stdout=b"", stderr=b"")
        with patch.object(
            subprocess, "run", side_effect=[OSError("launch failed"), process]
        ), redirect_stdout(out):
            code = campaign.main(["--json"])
        payload = json.loads(out.getvalue())
        self.assertEqual(code, 1)
        self.assertFalse(payload["ok"])
        self.assertEqual(payload["bundle"], "fast")
        self.assertEqual([result["probe"] for result in payload["results"]], list(campaign.BUNDLES["fast"]))
        self.assertEqual([result["status"] for result in payload["results"]], ["error", "replayed"])

    def test_rejects_unknown_probe_bundle_and_invalid_timeout(self) -> None:
        with patch.object(subprocess, "run") as run, redirect_stderr(io.StringIO()):
            with self.assertRaisesRegex(ValueError, "not allowlisted"):
                campaign.replay("../arbitrary", 3)
            for args in (["--bundle", "../arbitrary"], ["--timeout", "0"]):
                with self.subTest(args=args), self.assertRaises(SystemExit) as raised:
                    campaign.main(args)
                self.assertEqual(raised.exception.code, 2)
        run.assert_not_called()
