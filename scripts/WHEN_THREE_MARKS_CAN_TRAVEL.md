# A moving three-edge pattern, a bound pair, and an ambiguous exchange

A reversible rule can move a localized pattern without specifying a global
matching at each step. It does not follow that the pattern has a preferred
direction, a wavefunction, or the exchange sign of a fermion.

## Where a track comes from

Use [shell rule 16](WHEN_A_PAIR_OF_LOOP_DEFECTS_CAN_MOVE.md): act only at a
half-filled four-edge star when the four outside neighbor counts form two
equal pairs and the two marked ports come one from each pair. Complement
the four local bits. With just **three marked edges on the whole graph**,
a firing configuration must be a simple occupied path a–b–c–d. The contact
at b is legal precisely if b is also joined to d. Its successor is the
occupied path x–b–d–c, where x is the fourth neighbor of b. The condition
at c is the reflected one. An occupied triangle has two equally scored
marked ports and does not qualify. Thus no three-mark state branches into
more than two different moves.

This predicts the raw moves without coordinates. A second move that does
not immediately undo the first needs another triangle sharing an edge. On
the 3×3 rook graph triangles share no edges: of the 816 three-mark states,
744 are inert and the others form 36 isolated reversible pairs. The
triangle-free complete bipartite graph K₄,₄ has 560 inert three-mark states.

On the square of an n-cycle, each site is joined at cyclic distances one
and two. Write Sᵢ for the three edges (i,i+2), (i+1,i+2), (i+1,i+3):
these are the edges crossing one short cut through the track. A single
contact shifts the entire pattern to Sᵢ₋₁ or Sᵢ₊₁. The raw census at
n=7,8,9,10,12,16 finds one n-cycle, 3n isolated reversible pairs, n
three-state paths and otherwise inert states. Half the 256 shell rules
move this particular pattern and the other half leave it inert. Reflection
exchanges its two moves. Remembering the previous event and forbidding
immediate reversal would select a direction, but that memory is not in an
isolated three-mark state.

The small-triangle parity of Sᵢ is zero for n≥7 in these tests, while the
nearest-neighbor circuit winding around the ring is odd. Shifting Sᵢ by
one full star preserves **every** circuit parity. A full circuit reader
can distinguish a single seam from vacuum globally but cannot localize it.
Two seams Sᵢ XOR Sⱼ are the vertex cut of an interval; all circuit parities
then agree even with vacuum. The raw offers still distinguish some of those
states. In rules 66 and 130 the individual seam is inert, yet a pair at
distance three or four forms a closed 2n-state motion at n=14,16,20.
“Bound” here means closure under the actual allowed moves, not a measured
force or binding energy.

## Does going around one another produce a sign?

For rule 16, two sufficiently separated seams have four offers. At distance
four the inward offers stop; only outward moves remain. In the raw orbit
from a separated pair on each size n=12 through 24, the unordered pair of
seam positions is circuit-resolved by the *full edge state*, not by the
circuit-parity detector. To compare exchange histories, identify two orders
of distinct-packet moves only if both are actually legal and reach the
same raw state. Each such identification supplies one square:

| Track size | Raw states | Undirected moves | Legal squares | Independent cycles left modulo the squares, over GF(2) |
|---:|---:|---:|---:|---:|
| 12 | 30 | 48 | 18 | 1 |
| 16 | 72 | 128 | 56 | 1 |
| 24 | 204 | 384 | 180 | 1 |

Lifting to two temporary tracking labels, a shortest exchange from opposite
or nearly opposite positions has length n. Both flat sign assignments,
trivial and nontrivial on exchange, pass every observed square. On **every
edge**, changing the order of the sorted tracking labels is equivalent to
one packet crossing a fixed spatial cut. Within this two-packet sector an
odd exchange sign is therefore indistinguishable from a spatial π twist.
Labels and a signed transport rule are comparison tools, not extra marks
discovered inside the packet.

There is one useful control. Compare a full single-seam lap to a monotone
two-seam exchange. Across these sizes, the very same centers fire, with the
same multiset of occupied edges before and after on each center's star and
its four neighbor shells. Any common scalar phase assigned to those local
events cancels in the exchange-to-lap ratio; a sign supplied only in the
two-packet sector does not. A phase depending on a distant spectator or on
the number of packets can mimic it. Without an independently supported
common phase rule and a phase-sensitive reference this remains a proposed
distinguishing comparison, not a measurement. For even n, merely watching
the gap between packets does not even distinguish this exchange from
repeatedly advancing and undoing one step.

For context, [Girardeau's one-dimensional mapping](https://doi.org/10.1063/1.1703687)
starts with a quantum many-particle model and impenetrability; it does not
assign phases to raw IDT configurations. The existing [photonic phase
reference](probe_photonic_exchange_reference.py) uses measured interferometer
phases, not an observed fermionic sign for these patterns. Neither a particle
spectrum nor the Pauli principle is derived by this finite topology.

Replay [three-mark transitions](probe_three_mark_tracks.py) and
[exchange/cut controls](probe_seam_exchange_flux.py) with
`python3 scripts/replay_primitive_probe_campaign.py --bundle bench_seam_tracks_and_exchange`.
