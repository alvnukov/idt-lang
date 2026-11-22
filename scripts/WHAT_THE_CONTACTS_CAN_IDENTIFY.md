# What can an observer identify from these contacts?

The [previous cluster](CONTACT_ORIGINS_AND_READOUT.md) constrained a candidate
stock (a nonnegative count before normalization) and exposed several different
wirings with identical first readouts. Here we ask what further *operations*
can tell the alternatives apart. None of the trials below is physical data.

| Question | Available readout | What remains invisible |
| --- | --- | --- |
| Which pure neutral triangle current? | Two calibrated swap settings on repeated preparations fix its real projective ray. | Scale, overall sign, preparation history and graph. |
| Which connected tagged graph? | A signal echo can separate some graphs with identical currents. | Every frozen stock circuit misses the difference; the propagation rule and clock are extra. |
| Which real neutral population? | A sequence of calibrated neighboring swaps reconstructs its normalized symmetric second moment. | Imaginary part, ensemble decomposition and arbitrary apparatus faults. |
| Which three-packet exchange sector? | A cycle contact or two different pair contacts distinguish two actual preparations. | No universal choice of particle statistics follows. |

### Same stock, different space

There are connected bipartite graphs with two uniquely tagged terminals and
exactly the same signed boundary, not merely the same normalized frequencies.
Growing a neutral corridor and attaching bipartite squares preserves that
boundary while changing both distance and cycle rank. Since relabeling,
copy contact and Cartesian pairing all act through the boundary for these
stocks, no composition of the frozen stock operations can distinguish the
family. The finite replay also compares 29 actual graph branch tables.
With an extra unit-hop signal law the terminal echoes in five examples return
after 6, 10, 14, 18 and 22 ticks. Even matching the counts of vertices, edges
and tags does not force the same return time; conversely the same return
time does not fix the graph. [Graph and signal probe](probe_boundary_geometry_aliases.py).

### Same first readout, different later contacts

For a known connected graph of channels, earlier unselected exchange branches
average an unchanged and a permuted second moment. Reading one final
neighboring pair after such a path suffices to infer a non-neighbor pair
without physically installing its contact. One exact program per unordered
pair recovers the centered real second moment by subtracting the known
shorter-path contributions. The cost of resolving small differences can
grow exponentially with path length; this is not a shot-efficient claim.
Exact tests include 120 reconstructions on three to seven rails, an
uncalibrated spectator wire giving second minus fraction **1/12 rather than
3/4**, and a complex-conjugation negative control.
[Sequential tomography](probe_connected_contact_tomography.py).

Use `python3 -B scripts/check_contact_tomogram.py TABLE.json` for **exact
supplied populations**, not measured count ratios. It returns the centered
matrix, rank, positivity, trace and consistency under the declared protocol.
For example, this path table is compatible with a real trace-one population:

```json
{"schema":"idt-contact-tomogram/1","rails":["a","b","c"],"edges":[["a","b"],["b","c"]],
 "measurements":[{"pair":["a","b"],"h":"1/2"},{"pair":["a","c"],"h":"1/2"},
                 {"pair":["b","c"],"h":"1/2"}]}
```

Do not feed observed counts into an exact positivity test and reject a
candidate on rounding or statistical fluctuation.
[Checker and input contract](check_contact_tomogram.py).

There is also a **prospective count test** requiring no repeated pure state.
Always apply the same first swap. With a fresh random choice stop with
probability 1/3 and score the first minus port, or continue to a different
swap and score its minus port. Conditional on a lit first plus or minus,
the next minus probability under the quadratic model is respectively
3/4 or 1/4. The combined score is therefore fair for *either* first flag.
A lit modulo-three alternative scores minus every time. Ten out of ten minus
scores would have a predeclared one-sided probability of 1/1024 under the
quadratic null. This is an example, **not an observation**. The count tool
declines a tail when an attempted trial has no recorded score; drift between
trials is allowed, but unfair routing, reused sampling seeds, optional
stopping and treating descendants as independent trials invalidate the
comparison. A device that just tosses a coin also passes the overall null.
[Finite-count test](check_triangle_null_trials.py).

A separate [prespecified statistical witness](check_triangle_population_witness.py)
tests whether three programs share one positive real second moment. It uses
the worst of three exact directional binomial tails, not measured frequencies
as exact inputs. With synthetic minus counts `(8064,4096,4096)` in 8192
trials per program, the p-value rounded **up** is 0.002416. Each program is
individually possible. Drifting sources or correlated repeated tickets can
fake the joint discrepancy; complete reporting, a common preparation and
independent units within each program must be justified outside the checker.

### Pairwise agreement is not the Pauli principle

Three orthogonal neutral four-rail currents can each be prepared on a
bipartite path. From their ordered product, a coherent sum of the three
cyclic permutations and its complementary output give two routed preparations.
A further pair contact on the cyclic sum, keeping **both** flags as a
mixture, prepares symmetric and antisymmetric sectors in equal proportions.
Every individual pair has plus fraction 1/2 for that mixture and for the
mixed-symmetry preparation. A subsequent cyclic contact instead has plus
fraction **1 versus 0**; agreement of two successive different pair flags
is **1 versus 1/4**. On three neutral rails the local rank is only two and
the completely antisymmetric three-packet source vanishes. None of these
calculations explains why physical fermions occupy an antisymmetric sector.
[Addressed three-packet probe](probe_three_packet_exchange_sector.py).

**Can this certify the sign of exchange of the *whole* object?** No. Attach
three orthogonal unread labels to the three packets, and coherently add all
six simultaneous permutations with either equal or alternating signs.
The two total states then have opposite exchange characters but precisely
the same visible state. Even repeated visible-only instruments, an accessible
reference and visible postselection cannot distinguish them. The remaining
visible state is a permutation average: only permutation-invariant readings
are guaranteed to agree with the original, unaveraged preparation. Simply
reading the hidden labels or applying an uncontrolled full swap does not
recover their relative signs. A coherent comparison of *full* exchange
against identity could do so; its apparatus is an additional assumption.
[Hidden-label control](probe_hidden_exchange_colors.py).

Relaxing exact hidden orthogonality gives a quantitative boundary. For one
orthogonal visible word and three independent pure hidden tags, the largest
possible visible difference between the two signs depends only on the three
squared pair overlaps. The triad phase can change each visible state but not
their distance. For example, with squared overlaps `(1/4,1/4,0)`, a supplied
letter-exchange contact achieves contrast 1/4; allowing **all** mathematical
visible measurements raises the optimum to 1/3. Achievability of that optimum
with the available apparatus is not presumed.
[Partial-overlap probe](probe_partial_hidden_exchange.py).

For an actual comparison, [Tschernig et al.](https://www.nature.com/articles/s41566-021-00818-7)
interfered exchanged and reference photon amplitudes and reported an
exchange phase of −0.04 ± 0.07 rad (95% confidence interval; see their
[Fig. 3](https://arxiv.org/abs/2011.08777)). That is a measurement on
photons in a specified interferometer, not a readout of arbitrary hidden tags.

These labels are not quark color and the control does not violate the
exclusion principle. [Matthews et al.](https://www.nature.com/articles/srep01539)
simulated bosonic and fermionic output distributions using entangled photons;
the exchange-like readout did not turn the photons into fermions. The
[VIP-2 copper experiment](https://link.springer.com/article/10.1140/epjc/s10052-024-12599-8)
instead counted X-rays at the energies expected for anomalous atomic
transitions. A bound on that rate is not a bound on an abstract hidden
label with no transition-energy or capture-rate prediction.

This differs from [three-photon experiments](https://arxiv.org/abs/1609.09804)
on independent partially distinguishable inputs in an optical tritter and
from our [prior bosonic benchmarks](MULTIPHOTON_EXCHANGE.md): here both sector
preparations and the discriminator are routed on the same supplied carrier;
no measured photon probabilities are assigned to this apparatus.
Likewise the earlier stock arguments do not replace
[orthogonal-additivity results on real vector spaces](https://msp.org/pjm/1975/58-2/p14.xhtml):
the domain, available directions and gain assumptions are different.

Replay the identifiability probes with
`python3 -B -m scripts.replay_primitive_probe_campaign --bundle operational_identifiability`.
The [candidate register](../data/primitive_identifiability_inventory.json)
retains the source proposals without binding a physical prediction adapter.
