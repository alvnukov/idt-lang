from __future__ import annotations

import unittest
from fractions import Fraction as F

from scripts import probe_collision_cone_stability as stability
from scripts import probe_routed_diamond_cones as routed


class SpatialCollisionControls(unittest.TestCase):
    def test_nonzero_corner_not_a_zero_momentum_weyl_certificate(self) -> None:
        a = routed.multiply(routed.G, stability.RA)
        b = routed.multiply(routed.G, stability.RB)
        self.assertIsNone(routed.double_sector(routed.multiply(b, a), b))
        v = routed.conjugate(routed.diag((1, -1, 1, 1)), b)
        cone = routed.double_sector(routed.multiply(v, a), v)
        self.assertIsNotNone(cone)
        if cone is None:
            self.fail("missing representative")
        self.assertEqual(routed.determinant(cone.grams), F(1, 432))
        self.assertEqual(cone.tilt, (0, 0, 0))
        self.assertEqual(
            sorted(cone.spatial[j][j] for j in range(3)), [F(2, 3), F(2, 3), F(4, 3)]
        )
