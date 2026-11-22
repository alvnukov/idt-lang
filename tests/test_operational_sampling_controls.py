"""Independent small oracles for the sampling and two-state probes."""

from fractions import Fraction as F
from itertools import combinations, permutations, product
from unittest import TestCase

from scripts import probe_exchangeable_event_labels as ex
from scripts import probe_two_state_readout_barrier as barrier
from scripts import probe_unread_tick_instruments as ticks


class SamplingControls(TestCase):
    def test_without_replacement_word_against_literal_deals(self) -> None:
        for n in range(3, 7):
            for ones in range(n + 1):
                deck = (1,) * ones + (0,) * (n - ones)
                deals = tuple(permutations(deck, 3))
                for w in product((0, 1), repeat=3):
                    self.assertEqual(
                        ex.conditional_word(ones, n, sum(w), 3),
                        F(deals.count(w), len(deals)),
                    )

    def test_sharp_exchangeable_law_has_fair_pairs_but_third_parity(self) -> None:
        for n in (3, 4, 7, 8):
            law = ex.extremal(n)
            mean, pair, third = F(0), F(0), F(0)
            for sign, weight in law.items():
                bits = (1,) * ((n + sign) // 2) + (-1,) * ((n - sign) // 2)
                pairs = tuple(x * y for x, y in combinations(bits, 2))
                triples = tuple(x * y * z for x, y, z in combinations(bits, 3))
                mean += weight * sum(bits) / n
                pair += weight * sum(pairs) / len(pairs)
                third += weight * sum(triples) / len(triples)
            self.assertEqual(
                (mean, pair, third), (0, 0, F(1, n - 2 if n % 2 else n - 1))
            )

    def test_cesaro_projector_is_stationary_on_periodic_swap(self) -> None:
        swap = (ticks.vector(0, 1), ticks.vector(1, 0))
        pi = ticks.cesaro_projector(swap).projector
        self.assertEqual(pi, (ticks.vector(F(1, 2), F(1, 2)),) * 2)
        # Read out the CURRENT state, then swap. The one-shot marginal is
        # stationary but the second observed label reveals an unread tick.
        model = ticks.Instrument(
            (
                (ticks.vector(0, 1), ticks.vector(0, 0)),
                (ticks.vector(0, 0), ticks.vector(1, 0)),
            ),
            ticks.vector(F(1, 2), F(1, 2)),
        )
        self.assertFalse(ticks.unread_certificate(model).invariant)
        self.assertEqual(ticks.record_probability(model, (0, 0)), 0)
        self.assertEqual(ticks.record_probability(model, (0, 0), (0, 1, 0)), F(1, 2))

    def test_hidden_coin_mixture_is_not_uniform_iid(self) -> None:
        z, v = ticks.vector(0, 0), ticks.vector
        model = ticks.Instrument(((v(1, 0), z), (z, v(0, 1))), v(F(1, 2), F(1, 2)))
        self.assertTrue(ticks.unread_certificate(model).invariant)
        mix = ticks.mixture_certificate(model, ticks.cesaro_projector(model.transition))
        self.assertEqual(mix.collision, 1)
        self.assertFalse(mix.uniform_on_support)
        self.assertEqual(ticks.record_probability(model, (0, 1)), 0)

    def test_memory_exclusion_stays_conditional_on_loss_and_order(self) -> None:
        observed = barrier.tuple_interval(barrier.TARGET)
        for eta, expected in ((F(9, 10), "inconclusive"), (F(91, 100), "excluded")):
            self.assertEqual(
                barrier.diagnose(observed, (eta, eta, eta)).status, expected
            )
        clock = barrier.tuple_interval((F(0), F(1), F(0)))
        self.assertEqual(barrier.diagnose(clock).status, "inconclusive")
