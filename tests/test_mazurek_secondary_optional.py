"""Optional numerical-method controls. No author code execution or network access."""

from __future__ import annotations

import base64
import struct
import unittest
import zlib
from importlib.util import find_spec
from itertools import permutations


@unittest.skipUnless(
    find_spec("numpy") is not None and find_spec("scipy") is not None,
    "secondary-procedure audit needs optional NumPy and SciPy",
)
class SecondaryMethodsTests(unittest.TestCase):
    def test_bounded_inert_plot_parser_checks_every_row_and_stream_boundary(
        self,
    ) -> None:
        from scripts.reproduce_mazurek_secondary import decode_plot_numbers

        header = b"!boRe" + struct.pack("<III", 2, 100, 2)
        pairs = b"".join(struct.pack("<dd", float(i), i / 100) for i in range(1, 101))

        def encoded(payload: bytes) -> str:
            return base64.b64encode(payload).decode("ascii")

        def packed(raw: bytes) -> str:
            return encoded(zlib.compress(raw))

        values = decode_plot_numbers(packed(header + pairs))
        self.assertEqual((len(values), values[0], values[-1]), (100, 0.01, 1.0))
        for bad in (
            "",
            "###",
            "A" * 2204,
            encoded(b"not a zlib stream"),
            packed(header + pairs + b"excess"),
            packed(header + pairs[:-1]),
            packed(header[:-1] + b"\xff" + pairs),
            packed(b"Z" * 10000),
            encoded(zlib.compress(header + pairs)[:-1]),
            encoded(zlib.compress(header + pairs) + zlib.compress(b"ignored")),
            packed(header + struct.pack("<dd", 2, 0.1) + pairs[16:]),
            *(
                packed(header + struct.pack("<dd", 1, y) + pairs[16:])
                for y in (float("nan"), float("inf"), 1.1, -0.1)
            ),
        ):
            with self.subTest(prefix=bad[:12]), self.assertRaises(ValueError):
                decode_plot_numbers(bad)

    def test_another_valid_in_range_series_is_not_the_author_plot(self) -> None:
        from scripts.reproduce_mazurek_secondary import archived_plot

        with self.assertRaisesRegex(ValueError, "template"):
            archived_plot("arbitrary text, no plot")
        lo, hi = 0.995292505365083, 0.998559704622935
        raw = b"!boRe" + struct.pack("<III", 2, 100, 2)
        raw += b"".join(
            struct.pack("<dd", i, lo if i % 2 else hi) for i in range(1, 101)
        )
        enc = base64.b64encode(zlib.compress(raw)).decode("ascii")
        plot = [" "] * 47
        plot[0], plot[1] = "Cell[BoxData[", " GraphicsBox["
        plot[3] = f'LineBox[CompressedData["1:{enc}"]]'
        plot[39] = "PlotRange->{{0., 100.}, {0.995292505365083, 0.998559704622935}}"
        plot[-1] = ']], "Output",'
        with self.assertRaisesRegex(ValueError, "unexpected archived A series"):
            archived_plot("\n" * 7015 + "\n".join(plot))

    def test_universal_convex_bound_depends_on_a_self_weight_floor_not_a_solver(
        self,
    ) -> None:
        import numpy as np

        from scripts.reproduce_mazurek_secondary import (
            primary_success,
            score,
            self_weight_bounds,
        )

        rng = np.random.default_rng(17)
        p = rng.uniform(0, 1, (8, 4))
        e = np.column_stack([p, 1 - p[:, 3], np.ones(8), np.zeros(8)])
        for delta in (0, 0.001, 0.1):
            u = (1 - delta) * np.eye(6, 8) + delta * rng.dirichlet(np.ones(8), size=6)
            v = (1 - delta) * np.eye(3, 7) + delta * rng.dirichlet(np.ones(7), size=3)
            m = primary_success(p)
            strong, weak = self_weight_bounds(
                m, float(np.trace(u) / 6), float(np.trace(v) / 3)
            )
            self.assertLessEqual(weak, strong + 1e-12)
            self.assertLessEqual(strong, score(e, u, v) + 1e-12)
            if delta == 0:
                self.assertAlmostEqual(weak, score(e, u, v))

    def test_exact_noncontextual_saturation_with_both_equivalences(self) -> None:
        import numpy as np

        from scripts.reproduce_mazurek_secondary import fit_primary, secondaries

        # A genuine noncontextual model with both operational equalities:
        # M_t(0|lambda)=lambda_t for uniform permutations of (0, 1/2, 1).
        # mu_(t,0)=2 rho lambda_t, mu_(t,1)=2 rho(1-lambda_t).
        ontic = np.array(list(permutations((0, 0.5, 1))))
        effects = np.column_stack([ontic, [0, 1, 1, 0, 0, 1]])
        stocks = [s / 3 for t in range(3) for s in (ontic[:, t], 1 - ontic[:, t])]
        stocks.extend([effects[:, 3] / 3, (1 - effects[:, 3]) / 3])
        raw = np.array(stocks) @ effects
        fit = fit_primary(raw, np.full((8, 4), 0.001))
        self.assertLess(fit.chi2, 1e-18)
        result = secondaries(fit.primary, audit=True)
        self.assertAlmostEqual(result.cp, 1)
        self.assertAlmostEqual(result.cm, 1)
        self.assertAlmostEqual(result.a, 5 / 6)
        self.assertAlmostEqual(result.alternate_a, result.a)
        self.assertIsNotNone(result.face)
        if result.face is not None:
            self.assertLess(result.face.radius, 1e-7)

    def test_perfect_primary_correlation_is_not_the_secondary_witness(self) -> None:
        import numpy as np

        from scripts.reproduce_mazurek_secondary import secondaries

        # Three identical readers perfectly discriminate a single pair.
        # Their uniform mixture is NOT a fair coin. Once repaired, their
        # three correlations must average to 1/2 on this same pair.
        raw = np.array(
            [[1, 1, 1, 0.5], [0, 0, 0, 0.5]] * 3
            + [[0.5, 0.5, 0.5, 0], [0.5, 0.5, 0.5, 1]]
        )
        result = secondaries(raw)
        self.assertAlmostEqual(result.a, 0.5)
        self.assertAlmostEqual(result.cp, 1)
        self.assertLess(result.cm, 1)

    def test_published_ordinal_errors_are_not_realigned_poisson_errors(self) -> None:
        import numpy as np

        from scripts.reproduce_mazurek_secondary import variances

        one = np.arange(1, 65, dtype=float).reshape(8, 8)
        runs = np.repeat(one[None, :, :], 100, axis=0)
        aggregate = runs.sum(axis=0)[[0, 1, 2, 3, 4, 5, 7, 6]]
        original = variances(aggregate, runs, "author")
        ordinal = variances(aggregate, runs, "poisson")
        aligned = variances(aggregate, runs, "aligned-poisson")
        np.testing.assert_array_equal(original[:7], ordinal[:7])
        self.assertFalse(np.array_equal(original[7], ordinal[7]))
        a, b, a_other = one[6, 0], one[6, 1], one[7, 0]
        self.assertAlmostEqual(
            original[7, 0], (a * a * b + b * b * a_other) / (a + b) ** 4
        )
        self.assertAlmostEqual(aligned[6, 0], a * b / (a + b) ** 3)
        with self.assertRaisesRegex(ValueError, "aggregate mapping"):
            variances(runs.sum(axis=0), runs, "author")

    def test_real_data_anchored_at_fit_and_objectives_not_a_specific_lp_vertex(
        self,
    ) -> None:
        import numpy as np

        from scripts.reproduce_mazurek_secondary import (
            fit_primary,
            raw_probabilities,
            secondaries,
            variances,
        )
        from theory_experiments.mazurek_primary import load_counts

        counts = load_counts()
        agg, runs = (
            np.asarray(counts.aggregate, dtype=float),
            np.asarray(counts.runs, dtype=float),
        )
        v = variances(agg, runs, "author")
        for k, chi, objective in (
            (0, 5.378290032119363, 8.964215554245778),
            (99, 8.429531790064267, 8.980620331779194),
        ):
            with self.subTest(run=k + 1):
                fit = fit_primary(raw_probabilities(runs[k]), v)
                self.assertAlmostEqual(fit.chi2, chi, places=7)
                r = secondaries(fit.primary)
                self.assertLess(abs(6 * r.cp + 3 * r.cm - objective), 3e-7)
                self.assertGreater(r.a, 0.99)


if __name__ == "__main__":
    unittest.main()
