# A reader built out of the same bits and bonds

Can an apparatus made of the [pair-rule substrate](WHEN_A_RELATION_CAN_DELIVER_FOUR_CHANGED_BITS.md)
tell that a quartet changed without disturbing its final output? Yes, on a
prepared star, with a supplied program. It need not start with a copy of the
bit it will observe. The same pair program also reproduces two earlier packet
instruments. Neither result gives spontaneous measurements or Born weights.

### Why attaching a reader can break the operation

The rule compares endpoint degree **parities**. Attaching a passive link to
just one place can change the program even if that link is never offered.
Of the 16 possible masks of static exterior parity offsets, only all-zero
and all-one preserve the complete 16-input quartet truth table. In increasing
order of the number of correct inputs (2, 4, 6, 16), the numbers of offset
masks are 4, 4, 6, 2. An unmodified output in one calibration does not
establish non-disturbance.

One way to preserve all four offsets equally is to attach every leaf to a
common hub. Use an even number of leaves. At a clean gate boundary a leaf
has odd degree and the hub even, so offering their existing bond swaps the
two diagonal bits without changing any bond. Three such offers swap two
selected leaves and restore the hub. During a quartet program on leaves,
its four core members all see the same exterior parity offset.

Let the four leaves c,k,p,q contain a data bit, a reference, and opposite
pointer bits p,q. Apply the 15-offer quartet and then the three hub offers
that exchange c and k. The result leaves c,k intact and swaps p,q precisely
when c and k differ. This comparison costs 18 offers. To detect a *change*,
run the comparison before and after the source quartet, using the same
reference. The pointer swap then depends only on the difference between
the two readings; neither the initial data bit nor the hub bit need be known.

On eight leaves plus the hub, the 51-offer history (18+15+18) preserved the
source output and restored all bonds on 256 allowed initial assignments.
The pointer changed on all 96 assigned half-filled cases and on none of the
other 160. Disconnecting the spare leaf, so the hub has odd degree, breaks
216 of the 256 tests. A simpler copy control with two witness leaves can
read the change, but swaps the measured bit back: all six positive reads
disturb the source output. This compares two actual interaction histories,
not two descriptions of the same measurement.

The substrate is also programmable enough to imitate logic. A quartet
on (a,b,0,0) writes their conjunction to its two blank leaves. Read one
with the comparator, then undo the first quartet. In 48 offers this swaps
a dual-rail pointer only if both control bits were one, with the controls
and workspace restored (8 positives among 32 tested preparations). It is a
classical controlled operation on a specified code, not the copying of
unknown quantum states. A positive result from an externally programmed
test is weaker physical evidence than a prediction without that program.

### Transfer to independently specified packet instruments

On the [three-context carrier](WHEN_PACKET_ORDER_GENERATES_A_QUARTER_TURN.md),
replace each cell of each chosen matching by 15 pair offers. Every one
of the 48 color/address starts was replayed step by step: eight cells per
layer, 5,760 offers in total. The reconstructed action gives the same
`W=ABC` and `W²=(AB)²` as the raw quartet gate. The signed-contrast
identity is still a property of a selected readout of a permutation.

For the [two-packet reader](WHEN_TWO_PACKETS_CAN_MAKE_ONE_RECORD.md) the
256 cells **overlap**, so a scan offers one complete cell program after
another. The upper specification has one legal forward change and then
only its inverse. Each tested order therefore fires once during the
outgoing sweep and once during the following return sweep. The program
does not test which cell to call. A net-idle cell with one incoming bit
can make several internal moves; its clean boundary was verified, not
assumed to mean microscopic inactivity.

For every one of 256 inputs in each of the two modes, both scan orders
and both sweeps were checked by lifting the exact local 16-row table at
clean boundaries. This represents 7,864,320 individual offers. In addition,
122,880 actual global two-source offers on selected inputs were compared
**after every step** to that construction. These counts describe different
checks. A crossing-bond control breaks the clean compilation assumption.
Simultaneous scheduling of overlapping cells, autonomous detection, and
unchanged probabilities in a physical interferometer are not conclusions.

Replay the [reader and back-action controls](probe_embedded_relation_reader.py)
and [instrument transfer](probe_pair_compiled_packet_instruments.py) with
`python3 scripts/replay_primitive_probe_campaign.py --bundle bench_embedded_relation_measurement`.
