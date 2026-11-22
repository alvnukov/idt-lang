"""Execute finite path/readout documentation examples, not physical proofs."""

from __future__ import annotations

import doctest
import io
import sys
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]


class PathReadoutExamplesTests(unittest.TestCase):
    def check_examples(self, filename: str, expected_attempts: int) -> None:
        output = io.StringIO()
        # Absolute document paths and temporary import-path changes also work
        # outside the checkout. Restore interpreter settings after each test.
        with (
            patch.object(sys, "path", [str(ROOT), *sys.path]),
            patch.object(sys, "dont_write_bytecode", True),
            patch.object(doctest, "master", None),
            redirect_stdout(output),
        ):
            result = doctest.testfile(
                str(ROOT / "scripts" / filename),
                module_relative=False,
                encoding="utf-8",
                verbose=False,
            )
        self.assertEqual(result.failed, 0, output.getvalue())
        self.assertGreater(result.attempted, 0)
        self.assertEqual(result.attempted, expected_attempts)

    def test_marked_relay_examples(self) -> None:
        self.check_examples("MARKED_RELAYS.md", 6)

    def test_hidden_mode_examples(self) -> None:
        self.check_examples("HIDDEN_MODE_CANDIDATES.md", 10)


if __name__ == "__main__":
    unittest.main()
