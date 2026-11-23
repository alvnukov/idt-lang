# Three tests on the same packet: changing paths, waiting, and returning

Start from the same [twenty-state packet on a cube](WHEN_A_PACKET_STAYS_LOCAL.md). All probabilities below are for stipulated classical schedules or preparations. Neither amplitudes nor a clock probability law are hidden in the native shell update.

### A three-shutter difference can measure the shutters

Prepare a singleton at one corner and read its arrival **as a singleton** at the opposite corner after a stated number of offers. Use the first corner's three neighboring upper centers as shutters. For each of the eight opening subsets S, count the probability P(S) per original preparation, without conditioning on survival. Take I₃=P(ABC)−P(AB)−P(AC)−P(BC)+P(A)+P(B)+P(C)−P(∅).

| What changes when a shutter closes? | First nonzero I₃ |
| --- | --- |
| Offer a uniform one of 16 raw centers; veto the closed center's change, leaving a waiting step | Tick 8: 9/2147483648 |
| Draw uniformly from the **remaining enabled** centers; wait only if none | Tick 6: 7/144 |
| Use the original fully open proposal law but absorb a history when it actually toggles a closed slit | Tick 10: 9/549755813888 |
| Label a fully open history by its *first* successful slit only, then filter that label | Zero for all times by additivity |

The last two operations are not interchangeable: a path can touch more than one slit. For absorption, I₃ counts exactly the arriving mass with all three slit labels in its history. For veto-and-wait it need not: the same eight-offer word `1,3,4,0,5,4,6,5` reaches the sink only with shutter 4 alone open; it touches at most one distinct slit under each of the eight contexts. No negative path weights were used. The number is an operational inclusion–exclusion difference, not evidence of higher-order quantum interference.

Real comparisons have an apparatus and normalization. The photon experiment by [Sinha et al.](https://arxiv.org/abs/1007.4193) bounded a third-order contribution at the percent scale relative to the expected pairwise signal. [Kauten et al.](https://arxiv.org/abs/1508.03253) used a stabilized five-path apparatus and explicitly studied detector nonlinearity. [Magaña-Loaiza et al.](https://www.nature.com/articles/ncomms13987) enhanced looped optical paths in a three-slit geometry. These are not three versions of the cube data. Do not compare the dimensionless fractions above directly to reported normalized optical bounds.

### Fair scheduling does not set a travel time

The minimum is five events for first rung contact and six for isolated arrival. Yet a repeated 17-offer word touches *every* raw center and keeps the packet trapped in just two configurations. A stricter menu repeatedly offers each of the eight non-idle-capable upper centers once per sweep (the eight lower centers can be inserted anywhere). Of all 40,320 orders, 3,360 visit only four singleton sites, 6,720 visit six, and 30,240 visit all eight. No fixed sweep visits all 20 raw states, even counting intermediate offers. Even requiring each label enabled infinitely often to *fire* infinitely often allows a seven-state tour missing the target. A requirement on each enabled transition **at each recurrent state**, on the other hand, forces exploration of this finite connected orbit, but sets no deadline.

If one instead independently samples uniformly among active events, the exact *mean* to the opposite singleton is 40 events. For uniform offers among all 16 centers, including idle ones, it is 800/3 offers. These are different averages, neither of them the six-event minimum.

### When can a purely positive process have a return dip and revival?

For a reversible stochastic transition P on a finite state space, prepare its stationary distribution π conditioned on a nonempty event F, then read **that same F**. Its even-step return is ⟨1_F,P²ᵏ1_F⟩π/π(F). Since P is self-adjoint in this weighting, this is a positive mixture of uᵏ, 0 ≤ u ≤ 1. It cannot fall and then rise. The checker tests all signed forward differences through k=12 for 268 events on each of two raw cube kernels. Uniform active offers from the root singleton give 1, 1/2, 1/3, 1/4 at 0, 2, 4 and 6 events.

Two controls break the conclusion without any quantum mechanism. Repeating the ordered word `(1,0)` with the **same reversible elementary updates** gives 1, 0, 0, 1. Alternatively keep the random active clock and report the five singleton sites not neighboring the root, including the root itself. Preparing only the root gives 1, 1/2, 1/2, 19/36, 5/9; preparing the same readout set according to its conditional stationary law instead gives 1, 7/10, 2/3, 13/20, 173/270. A binary readout label does not determine a preparation distribution.

### An empirical anchor, not a calibrated packet prediction

The [KamLAND collaboration release](https://www.awa.tohoku.ac.jp/KamLAND/4th_result_data_release/4th_result_data_release.html) gives 76 prompt-energy bins. The optional local-file adapter verifies the exact release hash and sums three illustrative windows. For each it computes (observed candidates − modeled nonreactor contributions) / no-oscillation reactor expectation; it never uses the fitted oscillated reactor column.

| Prompt energy (MeV) | Candidates | No-osc. reactor | Modeled nonreactor | Descriptive ratio ± counting-only uncertainty |
| --- | ---: | ---: | ---: | ---: |
| [4.4, 5.0) | 227 | 280.1990 | 9.1812 | 0.777 ± 0.054 |
| [2.6, 3.1) | 205 | 438.5270 | 27.9275 | 0.404 ± 0.033 |
| [1.7, 2.2) | 270 | 316.0680 | 89.3786 | 0.571 ± 0.052 |

The uncertainty here is √N divided by the reactor template, **not total error**. The windows were chosen with the known oscillation scale in mind; they are not a blind holdout, a likelihood, or the collaboration's own plotted L/E points. The [KamLAND analysis](https://arxiv.org/abs/1009.4771) includes multiple reactor baselines, energy response and backgrounds. [Super-Kamiokande](https://arxiv.org/abs/hep-ex/0404034) observed an atmospheric L/E dip in an independent event stream. Neither result identifies an IDT event with neutrino flavor or L/E with a stationary raw clock. In particular, even increasing **mean** true time across detector bins does not preserve monotonicity under arbitrary mixing. An operational preparation, forward response and uncertainties are required before excluding a physical candidate.

Replay the [shutter protocols](probe_shell_shutter_protocols.py), [fairness and exact waiting times](probe_packet_scheduler_fairness.py), and [return kernels](probe_reversible_packet_return.py) with `python3 scripts/replay_primitive_probe_campaign.py --bundle bench_packet_clock_and_observation`. Default replay is offline and labels its empirical numbers as stored references. For an independent recalculation, download the collaboration's [spectrum table](https://www.awa.tohoku.ac.jp/KamLAND/4th_result_data_release/4th_result_data_release_files/EnergySpectrum_0.1MeVbin_4th_result.dat) and run `python3 -m scripts.probe_reversible_packet_return --spectrum PATH`.
