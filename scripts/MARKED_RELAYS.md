# When is a return signal evidence for the primitive?

Put a persistent mark at one site and issue a word of named port commands.
The signal traverses actual reciprocal links. A return means that it reaches
the marked site, not that an exterior observer looked up its displacement.
This still supplies the finite state update, globally comparable ports, a
clock and the ability to mark and recognize a site. It does not derive an
observer. The earlier [path-identity probe](probe_internal_signal_geometry.py)
used a path quotient directly; these probes test when finite machines imitate
it. None assumes that a port or a machine state is a physical spatial axis.

**A false positive on the native flags.** The
[24-flag search](probe_flag_local_reunions.py) exhausts the port rules on one
regular tetrahedral flag orbit, requiring a reciprocal move and covariance
under a simultaneous relabeling of ports and flags. Of 264 rules with four
distinct neighbors and no fixed port move, twelve return for `abcabc` but
not `ababab` (different letters denote distinct ports). These twelve are the
same rule up to an equivariant change of flag names. Every one is three
disconnected copies of the complete bipartite graph on four plus four
vertices. Each has 36 premature non-retracing returns at four ticks, where
the intended model has none. This excludes this particular connected
24-flag implementation, **not** larger carriers, different covariance
contracts or the opposition candidate as a whole.

**Positive finite rivals.** The [finite-relay probe](probe_minimal_signal_relay.py)
checks at every origin, without discarding failed trials. All four networks
have twelve different endpoints after two non-retracing ticks, no returns
before tick six on such walks, and pass the nominated pair of protocols.
Their behavior on *other* commands differs:

| Sites | Global permutations of the four ports realized | Rooted six-tick return words out of 972 |
| ---: | ---: | ---: |
| 26 | 3 | 108 |
| 32 | 24 | 72 |
| 64 | 24 | 24 |
| 128 | 24 | 24 |

The 26-site bound uses only a simple four-regular bipartite graph of girth
six: the two nonbacktracking trees of depth two on either side of an edge
must be disjoint, giving at least 26 sites. The cyclic construction attains
it, at the cost of the full compass symmetry. Under the **narrower** contract
of a finite connected abelian endpoint quotient with all port permutations,
32 sites suffice and are minimal for the nominated pair with no early
returns; 64 are minimal for the entire six-tick return language. The code
checks finite controls; the general bound is an algebraic argument, not a
registered Lean proof. Briefly, if all root differences have order `m`,
port swaps force every identified zero displacement to have all coordinates
equal modulo `m`. The diagonal subgroup has at most `gcd(4,m)` elements,
so each junction role has at least `m³/gcd(4,m)` sites. Girth and the
two-port nonreturn require `m ≥ 4`. At four, the largest diagonal subgroup
allows the unwanted six-step displacement `(-3,1,1,1)`; retaining only the
even diagonal removes it. A finite model can therefore agree with every
short-path observation in this test. None of these counts measures the
dimension or size of our universe.

**Can the same loops carry a sign?** The
[binary transport probe](probe_relay_loop_parity.py) supplies one extra bit
to the signal. Traversing a link toggles the bit if that link is marked;
traversing it backwards undoes the toggle. Ask for an odd change on every
`abcabc` with distinct ports. No assignment can do this on the 26-site
relay: multiplying the thirteen translated loop constraints for one triple
uses every contributing edge an even number of times but requests an odd
total. On both the 32- and 64-site relays, solutions exist. Even after
identifying local choices of which bit value to call positive, eight distinct
assignments remain **up to that equivalence**. A physically flat choice with
no odd loops is possible on the same underlying graphs. Signs that depend
only on the port, not the link, always give even parity on these words.

Thus a transport test can distinguish networks that both pass the same
selected clock tests. The extra bit, the odd-loop requirement and the link
marks are inputs. A carried classical bit is not a complex amplitude, and
a detector distinguishing its values is not an interference or Born-rule
experiment.

Replay the finite experiments with
`python3 -B scripts/replay_primitive_probe_campaign.py --bundle marked_relays`.
