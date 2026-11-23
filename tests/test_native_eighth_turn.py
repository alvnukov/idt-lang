"""Independent finite controls for the supplied native eight-setting circuit."""

import unittest
from collections import Counter
from importlib.util import find_spec
from itertools import product


class NativeEighthTurnTests(unittest.TestCase):
    def setUp(self) -> None:
        self.assertIsNotNone(find_spec("scripts.probe_native_eighth_turn"),
                             "native eight-setting replay is missing")
        from scripts import probe_native_eighth_turn
        self.p = probe_native_eighth_turn

    def test_source_generates_one_orbit_once_and_restores_the_three_inputs(self) -> None:
        p = self.p
        for backend in ("B", "CS"):
            seen = set()
            for g, u, v in product((1, 2), repeat=3):
                bits = (u == 1 or v == 1, u == 1, u == 1 and v == 1, False)
                expected = tuple(1 + (b ^ (g == 1)) for b in bits)
                seed = {"L_m": 3, "g": g, "u": u, "v": v}
                state = p.execute(p.source(), backend, seed)
                for arm in p.ARMS:
                    self.assertEqual(tuple(state[s] for s in arm), expected)
                self.assertTrue(all(state[s] == value for s, value in seed.items()))
                self.assertEqual(list(state.values()).count(3), 1)
                seen.add(expected)
            self.assertEqual(len(seen), 8)

    def test_local_compiler_preserves_token_and_allows_dirty_parity_balance(self) -> None:
        p = self.p
        for x, y in product((1, 2, 3), repeat=2):
            state = p.execute((("local", (("x", "y"),)),), "CS", {"x": x, "y": y})
            self.assertEqual((state["x"], state["y"]), (y, x) if 1 in (x, y) else (x, y))
            self.assertEqual(state["cat_local"], 1)
        for x, bal in product((1, 2, 3), (1, 2)):
            state = p.execute((("local", (("zero_x", "x"),)),), "CS", {"x": x, "bal_zero_x": bal})
            self.assertEqual((state["x"], state["bal_zero_x"], state["cat_local"]),
                             (3 - x, 3 - bal, 1) if x != 3 else (3, bal, 1))

    def test_clock_and_restricted_walls(self) -> None:
        p = self.p
        for seed in product((1, 2), repeat=4):
            for bal in (1, 2):
                raw = dict(zip(p.ARMS[0], seed, strict=True)) | {"parity": bal}
                after = p.execute((("plate", p.cs_blank_plate(p.ARMS[0], "parity")),),
                                  "CS_raw", raw)
                self.assertEqual(tuple(after[s] for s in p.ARMS[0]),
                                 (3 - seed[-1], *seed[:-1]))
                self.assertEqual(after["parity"], 3 - bal)
        self.assertEqual(p.signed_wall(3, False), (48, 0))
        self.assertEqual(p.signed_wall(4, True), (192, 0))
        self.assertEqual(p.marker_orbit(), ("q",) * 4 + ("m",) * 4)

    def test_full_grid_and_unconditional_shutters(self) -> None:
        p = self.p
        report = p.verify()
        self.assertEqual(report["main_launches_per_backend"], 3 * 4 * 64 * 16)
        self.assertEqual(report["D0_per_16_by_difference"], [16, 12, 8, 4, 0, 4, 8, 12])
        self.assertEqual(report["shared_stock_removed_checks"], 64)
        self.assertGreater(report["raw_contacts"]["CS"], report["raw_contacts"]["B"])

    def test_shutter_position_changes_what_the_dump_physically_keeps(self) -> None:
        p = self.p
        clean_input = {"L_m": 3, "g": 2, "u": 2, "v": 2, "coin": 1}
        for power, backend, shutter in product(range(8), ("B", "CS"),
                                              ("upstream_full", "return", "upstream_token_only")):
            stages = p.schedule(shutter, (False, True), (power, 0), backend)
            final = p.execute(stages, backend, clean_input)
            dumps = {k: v for k, v in final.items() if k.startswith("dump_")}
            expected = {"dump_L_m": 3}
            if shutter == "upstream_full":
                expected.update(("dump_" + q, 1) for q in p.ARMS[0])
            elif shutter == "return":
                expected["dump_L_q0"] = (1, 2, 2, 2, 2, 1, 1, 1)[power]
            self.assertEqual(dumps, expected)
            if backend == "CS":
                self.assertTrue(all(value in (1, 2, 3) for value in final.values()))
                self.assertTrue(all(value == 1 for k, value in final.items() if k.startswith("cat_")))

    def test_uniform_four_bit_stock_is_not_uniform_thermometer_stock(self) -> None:
        p = self.p
        for delta in range(8):
            matched: Counter[bool] = Counter()
            for seed in product((1, 2), repeat=4):
                cells = dict(zip(p.ARMS[0], seed, strict=True))
                state = p.execute((("plate", p.plate(p.ARMS[0], "L") * delta),), "B", cells)
                matched[seed[0] == state.get(p.ARMS[0][0], seed[0])] += 1
            self.assertEqual(matched[True], (16, 8, 8, 8, 0, 8, 8, 8)[delta])
