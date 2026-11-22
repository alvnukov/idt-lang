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

This differs from [three-photon experiments](https://arxiv.org/abs/1609.09804)
on independent partially distinguishable inputs in an optical tritter and
from our [prior bosonic benchmarks](MULTIPHOTON_EXCHANGE.md): here both sector
preparations and the discriminator are routed on the same supplied carrier;
no measured photon probabilities are assigned to this apparatus.
Likewise the earlier stock arguments do not replace
[orthogonal-additivity results on real vector spaces](https://msp.org/pjm/1975/58-2/p14.xhtml):
the domain, available directions and gain assumptions are different.

Replay the three source probes with
`python3 -B -m scripts.replay_primitive_probe_campaign --bundle operational_identifiability`.
The [candidate register](../data/primitive_identifiability_inventory.json)
retains the three source proposals without binding a physical prediction adapter.
