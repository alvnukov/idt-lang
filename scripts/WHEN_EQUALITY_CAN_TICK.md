# When equality can tick

A clock site can be identifiable even when its absolute phase is not. The finite example uses one rule: an offered triple flips all three bits when they are equal; a mixed triple does nothing. A **jam** is a state in which no offer changes anything.

## A site that flips on every change

The [raw search](probe_unanimous_fano_clock.py) asks which sets of at most seven unordered triples on at most seven sites have no jam. Exactly 30 labelled families survive, all relabellings of the seven lines of the Fano plane. No coordinates enter the search. There is a direct two-colour count: each pair lies on exactly one line. A unanimous line contributes three same-colour pairs; a mixed line contributes one. Even the most balanced split, three sites to four, has nine same-colour pairs. Seven mixed lines could account for only seven.

Among the 128 raw states are seven six-cycles. On each, the two enabled lines meet at the same site throughout the cycle. Every changing event flips that site's bit, in either direction around the cycle. This covers 42 states, not all 128. The rule does not force the next offer to change anything, forbid undoing the previous change, or specify elapsed time.

## Keep differences, discard absolute shades

The [relational probe](probe_relational_unanimous_clock.py) stores only whether each pair differs. A triple is ready when its three internal differences vanish; firing toggles exactly those links crossing its boundary. If all differences come from vertex bits, the 128 assignments give 64 diagrams: a colouring and its global complement give the same one. Each clock six-cycle folds to a triangle. The common site remains identifiable and the set of ready lines changes at each firing. But no binary label of the current diagram can alternate on every edge of a triangle. Equality locates the tick; it does not orient its absolute two-phase readout.

Keeping only local consistency gives a different model. Two colours permit four diagrams on a single triple: all equal, or any one site different. The seven Fano lines share no pairs, so their local choices give 4⁷ = 16,384 link diagrams. Exactly 3⁷ = 2,187 are jammed: every line is mixed. The moves preserve the XOR of differences around each closed path. The diagrams split into 256 sectors of 64 by these cycle values; only the sector with zero XOR on **every** cycle is jam-free. Thus no-jam survives forgetting the absolute shades, but not discarding their global consistency. This is a property of the supplied incidence and states, not a physical clock, detector or spatial reconstruction.

Reproduce from the repository root:

```sh
python3 -m scripts.probe_unanimous_fano_clock --json
python3 -m scripts.probe_relational_unanimous_clock --json
```
