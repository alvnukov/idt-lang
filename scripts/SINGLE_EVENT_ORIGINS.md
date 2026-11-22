# Where can one click come from?

The earlier [contact probes](WHAT_THE_CONTACTS_CAN_IDENTIFY.md) construct
integer currents and a population of possible detector tickets. Selecting a
uniform ticket is a different operation from counting them. Here we ask what
a persistent detector can do **without a random seed, a table of squared
weights, or an explicit list of occurrence pairs**. A click below is one
named output per specified clock tick. This is not yet a physical theory of
the trigger, microscopic energy transfer or the measurement of unknown
changing preparations.

## Three local detector candidates

Take a fixed connected bipartite packet with named channels. A serial
collector compares the path parity of incoming occurrences and cancels
opposite roles on each channel, leaving a unary chain of length
`n_i=|v_i|`. Changing the common parity convention changes no length.
This collector, reusable hardware, stable channel identity and a clock
are hypotheses, not consequences of an undifferentiated graph.

| Device | Measured at every tick | Control that changes the answer |
| --- | --- | --- |
| [First-passage chain](probe_unary_first_passage_detector.py) | A cursor reflects at the root and each switch alternates its outgoing direction. Reaching the far end takes exactly `n_i²` hops from the prepared switch state. Passage restores that switch state; no long list of pairs. | The first passage can take only `n_i` steps from the opposite initial state. Resetting the whole apparatus at every trigger can repeatedly select the same channel. |
| [Closed physical petals](probe_reciprocal_detector_petals.py) | Identify root and exit at different ports of one hub, and subdivide each logical edge into four local hops. A simple bipartite network counts **all** physical hops with no instantaneous return; one tour spends `4 n_i²` ticks on rail i. | Replace only the port-sensitive hub with an ordinary rotor: asymptotic frequencies are linear. Unequal wire delays can change square-law timing even at equal edge count. |
| [Reversible marker](probe_reversible_excitation_detector.py) | Each interior swaps the traveling lane bit with its own bit. The hub sends an arriving marked lane on to the next petal. A single circulating mark makes `n_i` laps of length `4 n_i`. Local rules are reversible on **all** states, not just on the selected orbit. | One mark stored on an inactive petal can remain trapped. Uniform time over all states has linear weights. Looking only when the cursor changes rails gives equal counts per live rail. |

For the reversible example with channel lengths `(2,1,3)` the active tour
spends **16, 4, 36 ticks** on the channels. Of 192 one-marker states, 112
belong to the active part. A change of rail heralds activity if at least two
rails are live. This does **not** make 112/192 an experimentally measured
preparation probability. With `m_i` marked cells left in petal i on arrivals
with a marked carrier and perimeter `P_i`, the mean ticks per visit equal
`n_i P_i/(1+m_i)`. The weights, therefore, are a consequence of both
the dynamics and the prepared sector. On the [earlier three-register
instrument](probe_exclusive_triangle_detector.py), the new active device
counts 96, 24 and 216 local hops with no unassigned hop; three changing
unknown particles are not being measured 336 independent times.

## What if the setting changes?

For a finite total deterministic machine, demand a target rate separately
on every recurring setting, for **every** finite initial drive followed by
a periodic drive. If the reduced target denominators are `q_c`, a reachable
closed loop must visit each setting a multiple of its denominator. Paths
ending in the same state of a closed strongly connected region must have
equal count residues after a common return. This requires at least
**the product of the denominators**, not just their largest value. Separate
target-aware counters attain that state bound; the bound is not a proof
that nature supplies those counters.

The [driven-memory probe](probe_driven_readout_memory.py) exhausts 46,916
one- through three-state two-setting machines and preserves a four-state
construction with separate half rates. For native circuits with rates
1/2 and 1/8 the bound is 16 states; the implemented clocks counting actual
microscopic tickets use 4096 joint phases. A shared-clock countermodel can
give perfect pooled balance but opposite extreme rates conditional on a
setting chosen using earlier outcomes. Counting external clocks, when the
device learns the setting, and allowing fresh inputs change the problem.

### Test a submitted device cheaply

The [selector adapter](../theory_experiments/driven_event_selector.py) takes
a finite transition/output table, initial state, and up to eight named-by-index
contexts. Each context supplies a neutral current and a fixed rail of a swap;
the **reference**, not the submitted device, computes the quadratic minus-port
rate. Two identical reference settings may represent distinct knob labels.
The device must actually generate its outputs and state updates. A supplied
zero current has no normalized reference: that case cannot pass by convention.

For each reachable strongly connected group of states, the checker tries to
assign integer potentials. Along an edge for context c the potential change
in its coordinate must be `denominator * emitted_bit - numerator`; all other
coordinates stay unchanged. When this works every internal cycle has zero
residual. Failure produces an actual prefix from the initial state and a
repeatable closed word giving the wrong rate. It checks reachable groups
even if some drive can leave them. A truncated search without a counterexample
does not pass. This is a machine check of a **submitted mathematical device**,
not experimental evidence for it, and not a Lean proof of a physics law.

```sh
python3 -B scripts/screen_hypotheses.py --batch-file data/driven_event_selector_controls.json --max-cases 32 --no-cache --history-dir "$(mktemp -d)"
```

The [five explicit submissions](../data/driven_event_selector_controls.json)
include a separated quarter-rate counter, a shared-phase impostor, unreachable
versus reachable defects, and an undefined reference. The batch intentionally
contains counterexamples; an exit code indicating a counterexample is not
a process failure. Source-only proposals stay unassessed unless explicitly
submitted as prediction-bearing tables.

## Measured records: two narrow diagnostics, not a claim of randomness

**Delft 2015.** The [finite memory witness](probe_event_memory_witness.py)
uses the previously [pinned author selection](replay_hensen2015.py). For
a deterministic device with only M possible starting states and specified
inputs, one input *word* cannot generate more than M different output
words. The witness reports actual windows. For noisy observations it
counts incompatible **nonoverlapping** windows and takes a maximum, not
a sum across competing partitions. This does not require an iid hypothesis.

On the 245 accepted [Hensen et al. records](https://doi.org/10.4121/uuid:6e19e9b2-4a2d-40b5-8dd3-a660bf3c0a31),
grouped by day/run, local-setting words require at least four starting
states on either side under this ideal *closed-machine* contract. Allowing
new states at every rejected released row leaves 228 segments (longest:
three accepted events). A two-state local-setting device still leaves
at least four incompatible disjoint windows on Alice's side and two on
Bob's. Reveal **both** settings as inputs and those counts become zero and
one. Even adjacent released rows are not necessarily adjacent physical
attempts. An unmeasured changing source can provide fresh input, so these
are **not** lower bounds on the memory of the physical detector.

**Delft second run.** [Authors' publication](https://doi.org/10.1038/srep30289);
[4TU release](https://doi.org/10.4121/uuid:53644d31-d862-4f9f-9ad2-0b571874b829).
The [second-run replay](probe_delft_second_rotor.py) independently reduces
the pinned raw archive without executing the analysis shipped with it.
The old/new detector eras have 56/244 accepted trials, with 237 CHSH wins
in 300 total. This is another run by the same group, not an independent
laboratory. The histogram of heralded outcomes alone does not identify an
event selector.

Under a specified ideal `0011` rotor on Alice's **accepted** subsequences,
allow an unknown phase for every detector era/day/run and both settings and
herald type. There are 252 singleton subsequences and 24 pairs: *every*
possible such binary record fits some phases. The test consequently has
**zero power**, not evidence for the model. The secondary analysis indexes
only Alice's own setting (within era/day/run). Four of eight triples cannot
match any phase, requiring at least four bit substitutions with the clock
fixed. This is a retrospective incompatibility count, not a p-value;
missed ticks or a different preparation/reset contract can remove it.

```sh
python3 -B -m scripts.replay_primitive_probe_campaign --bundle single_event_origins
python3 -B -m scripts.probe_event_memory_witness --raw-file /path/to/2015/bell_open_data.txt
python3 -B -m scripts.probe_delft_second_rotor --raw-file /path/to/second-run/data.zip
```

The campaign runs only synthetic controls by default. Both optional
empirical commands check the raw checksum, and neither data set is
redistributed. [Candidate history inputs](../data/primitive_event_origin_inventory.json)
keep the detector constructions and diagnostics distinct from tested
physical predictions. No new fundamental axiom or public claim is adopted.
