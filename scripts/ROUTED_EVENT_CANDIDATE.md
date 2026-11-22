# A signed cloud and one whole event

[Port-only stock selection](PORT_STOCK_ORIGIN.md) gives the **weight** as
a lattice index without a supplied metric. [Separate internal counts](SEPARABLE_STOCK_SELECTION.md)
also fix the raw table up to orientation. This next question
is different: can discrete objects enact those weights through an entire
interferometer, with every selected trial exiting and no table of target
probabilities inside the routing rule? Replay the cluster with
`python3 -m unittest tests.test_routed_event_candidates`.

### What propagates, what is counted

The [explicit router](probe_cancellation_event_router.py) propagates signed
children from an integer matrix with orthogonal equal-gain columns. Opposite
children cancel within each outgoing rail. A tag is an ordered pair of live
token addresses on the **same** rail, possibly the same token twice. A local
pairing on output children and a second pairing on distinct input axes
route every input tag and seed to exactly one surviving output tag,
invertibly. This uses the gate, the cloud and its addressable matching,
not the desired detector probabilities. A uniform input tag and seed give
a uniform output tag. On one injected token its starting address is unique.

After two mixers all 16 routed trials from a single input exit. Among
independent raw histories only 16/256 meet the terminal coincidence and
survival criterion, or 4/256 if enforced at both stages. A bypass must
amplify by two when its neighbors are mixed; a bare identity would change
relative gain. Two overlapping mixers give the three-port counts
(8,4,4)/16. Changing the cancellation matching changed individual
destinations in 124/160 tested cases without changing the ensemble.
The hidden trajectories are not unique predictions. The raw matrix is
twice the normalized amplitude matrix: its square is **four times** a port
exchange, not a literal permutation of a fixed alphabet.

The [ranked router](probe_ranked_event_routing.py) reconstructs individual
addresses without listing the entire cloud. It agrees with the explicit
algorithm and its inverse on 90,000 tickets across 2,500 cases. Mean
pairing steps are at most the maximal number of occupied parents entering
a row minus one (uniform ticket); this is not a worst-case time bound.
An exceeded computational limit is an error, not a discarded trial.

### Stronger probes and their controls

- [Composite event test](probe_routed_pair_bell.py): 20 emitted trials per
  setting, half marginals, CHSH 14/5, unchanged by analyzer order.
  Removing the entangling preparation gives CHSH zero. Changing an earlier
  setting can change a later individual tag on the other side. This uses
  joint configuration space: it is not a Bell-local explanation or an
  experimental measurement of CHSH.
- [Integer phase orbit](probe_integer_phase_orbit.py): two supplied
  multipliers with gain five give relative phase (3+4i)/5 of infinite
  order. Unbounded repetition gives density, not every phase exactly or at
  bounded resource. It uses an additional gate.
- [Paired encoding](probe_paired_rail_encoding.py): using only addressed
  copies of the original mixer gives a logical quarter-turn once opposite
  amplitudes have been prepared. The coherent preparation flag succeeds
  on 8/16 injections; identifying the surviving rail changes the preparation.
  With a fixed orientation reference two conjugate three-port words give
  different probabilities (13/32,17/32,1/16) vs (13/32,1/32,9/16) **per
  successful preparation**. Conjugating the entire apparatus changes none.
  This is a relative phase witness, not physical CP violation.
- [Fixed-input recurrence](probe_native_recurrence_witness.py): the first
  thirteen return probabilities give a seven-by-seven Hankel matrix of rank
  seven. A homogeneous linear model with at most six coordinates must miss
  at least one by 3312/242641 or more. Over unlimited time the best uniform
  error for a fixed finite homogeneous stochastic competitor is 361/756.
  A finite clock can memorize any fixed prefix exactly: the experiment
  cannot rule out unrestricted classical memory from finite records.

### What has not been derived

The candidate gives a conditional reason for a weight and a mechanism for
routing whole tags with that weight. It supplies cancellation, independent
raw channels, transparent two-step exchange, a common gain, seeds, and an
address/readout convention. The full cloud is required alongside the event.
Stock is not itself a probability, and a single click is not a derivation
of stored energy. Composite space, physical scale and the preparation of
the measuring apparatus remain distinct problems. No claim status changes.
