"""Regression checks for the finite three-context coincidence probe."""

import unittest

from scripts import probe_native_phase_coincidence as probe


class NativePhaseCoincidenceTest(unittest.TestCase):
    def test_all_color_maps_and_two_independent_partitions(self) -> None:
        report = probe.run_probe()
        self.assertEqual(report.color_maps, {pi: 16 for pi in (
            "ABC", "ACB", "BAC", "BCA", "CAB", "CBA"
        )})
        self.assertEqual(report.orientation_counts, {"W": 48, "W_inverse": 48})
        for mode in report.modes.values():
            self.assertEqual(mode.product_orbits, 64)
            self.assertEqual(mode.equalizer_classes, 64)
            self.assertTrue(mode.partitions_agree)

    def test_all_mask_offers_detect_ambiguous_inverse_even_with_spectators(self) -> None:
        for mode in probe.run_probe().modes.values():
            factored = mode.factored
            self.assertEqual(factored.forward_offers, {1: 256})
            self.assertEqual(factored.reverse_offers, {1: 256})
            self.assertEqual(factored.exact_reverse, 256)
            self.assertEqual(factored.output_footprints, 256)
            self.assertEqual((factored.class_rails, factored.residue_rails), (64, 8))
            self.assertEqual(mode.private.reverse_offers, {1: 256})
            self.assertEqual(mode.class_dyad.reverse_offers, {4: 256})
            self.assertEqual(mode.class_dyad.output_footprints, 64)
            self.assertEqual(mode.class_dyad_with_spectators.forward_offers, {1: 256})
            self.assertEqual(mode.class_dyad_with_spectators.reverse_offers, {4: 256})
            self.assertEqual(mode.class_dyad_with_spectators.output_footprints, 256)
            self.assertEqual(mode.lossy_z_edges.residue_rails, 8)
            self.assertEqual(mode.lossy_z_edges.output_footprints, 128)
            self.assertEqual(mode.lossy_z_edges.reverse_offers, {2: 256})

    def test_partial_sheet_and_fixed_instrument_do_not_certify_null(self) -> None:
        report = probe.run_probe()
        for mode in report.modes.values():
            self.assertEqual(mode.aligned_offers, {0: 240, 1: 16})
            self.assertFalse(mode.certified_null)
        self.assertEqual(report.fixed_equality_counts, {
            "independent": (4, 16), "D_common": (4, 4), "H_common": (2, 4),
        })
        self.assertTrue(report.preparation_marginals_equal)

    def test_equivariant_one_hot_residue_bound_and_odd_edge_transport(self) -> None:
        bound = probe.run_probe().restricted_bound
        self.assertEqual(bound.color_preserving_order, 16)
        self.assertEqual(bound.central_w_order, 4)
        self.assertTrue(bound.z_is_nonidentity_commutator)
        self.assertEqual(bound.max_disjoint_stabilizer, 2)
        self.assertEqual(bound.min_class_rails, 64)
        self.assertEqual(bound.min_residue_rails, 8)
        self.assertTrue(bound.c_edges_covariant)


if __name__ == "__main__":
    unittest.main()
