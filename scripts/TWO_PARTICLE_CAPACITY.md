# When does a reversible two-port candidate have room to bunch?

Run `python3 -O scripts/probe_two_particle_capacity.py`. This complements
the [existing Pauli benchmark](../PAULI_CHECKER_RESULT.md), which checks a
supplied amplitude tensor. Here the input is a finite port alphabet and
an actual reversible routing table T. Count *both* output occupations,
in order (2,0), (1,1), (0,2); a single click is not a number measurement.
Identical preparation means two independent draws from the same hidden
one-particle distribution, not merely equal marginal distributions.

For the bare table assume T² is the port swap on the entire raw state
and T preserves the total number. A diagonal input stays diagonal by
commutation with swap. Define an edge ij between distinct single labels
if that pair bunches. The reverse ordering bunches at the other port.
Each such edge consumes a distinct unordered vacuum/double-label pair,
so there are at most (number of vacuum labels) × (number of double
labels) edges. For identical iid weights p, the coincidence probability
is C=1−2Σ_edges pᵢpⱼ. Its minimum over p is 1/ω, where ω is the largest
number of mutually connected single labels. To see why, transfer the
combined mass of two non-neighbours onto the one with larger neighbour
mass; this cannot decrease bunching. On a clique, C=Σpᵢ² is minimized
by uniform mass. The [replay](probe_two_particle_capacity.py) checks graph
examples and explicit full gates; the argument, not a finite grid, gives
the general formula.

| Actual mechanism | Observation on supplied inputs | What it distinguishes |
| --- | --- | --- |
| 4 cell labels; 16 ordered inputs | iid: (1,2,1)/4; anticorrelated: (1,0,1)/2 | Same marginal distributions and splitter, different two-source preparation |
| 105 labels; 11,025 ordered inputs | same marker: (28,8,28)/64; different markers in either order: (16,32,16)/64 | Strong coincidence suppression, iid sources, balanced singles, exact number and marker conservation, with no quantum amplitudes |
| 4 extra directed memory phases; 144 full inputs | UU: (2,0,2)/4; UM and MU: (1,2,1)/4; MM: (0,4,0)/4 | One matched preparation mimics a perfect dip, but the other matched marker does not. The square is **swap plus a memory shift**, not the bare swap |

With one empty and one double label, at most one graph edge can bunch,
so C≥1/2, regardless of the number of one-particle labels. With no double
labels there is nowhere for both particles to go in two exhaustive modes.
Neither exclusion is Pauli antisymmetry. Conversely a nonzero dip does
not establish bosonic exchange; the 105-label example yields C=1/8
without changing the bare swap-square law. A measured finite residual
would need independent bounds on the size of the hidden state space,
on preparation correlations, on completeness of the ports and on losses
to turn these statements into an exclusion of a physical model. No
laboratory count or universal spin–statistics relation is inferred here.
