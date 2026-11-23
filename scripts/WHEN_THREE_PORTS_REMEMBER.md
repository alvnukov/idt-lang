# When a two-port switch is used on three ports

Send one tagged token through three ports A, B, C. A two-port device that looks balanced on the bench need not behave like two fresh balanced devices in sequence. In particular, a rail that is empty of the token can retain ordinary physical records.

## What changes, and what is supplied?

The original [four-label switch](WHEN_A_BLANK_RECORD_CAN_TRAVEL.md) has two operating cells D,E per port. On two vacant arms it flips both D shades, leaving E unchanged. An independent, identically distributed vacuum stock is invariant only when each D is fair and independent of its E. For this stock, replacing the source D by the token and reusing that arm's E gives crossing probability at most 3/8. A different source stock escapes this particular bound. On the original fixed-D preparation the literal cascade AB,BC also differs from two independently balanced couplers: for input A the counts are (4,3,1)/8 instead of (4,2,2)/8.

The [compensated switch](probe_vacuum_compensated_network.py) adds scheduled contacts on the same four-label law, with one restored scratch cell per arm. The old device is retained. The new device fixes all 16 two-arm vacant states individually. On the prepared one-token code, it swaps the token exactly when the two E shades differ and leaves those shades intact. It is **not** a global involution: its square fixes 63 of 81 tested positive-label operating states. It recovers all 32 two-arm shutter/plate rows using its own specified plate and refill, not by editing old scores.

One fair independent shade bit per vertex makes these switches independently balanced on any **forest of once-used edges**: one root bit per component and the edge XORs determine every vertex bit. A loop or repeated edge shares stock. In the table, rows label sources A,B,C; each triple counts arrivals A,B,C out of eight.

| Order of two-port operations | Native rows on the three ports | What distinguishes it? |
| --- | --- | --- |
| AB, BC | (4,2,2); (4,2,2); (0,4,4) | Matches fresh independent switches. |
| AB, BC, CA | (2,2,4); (4,2,2); (2,4,2) | Differs from fresh switches but matches an explicit fixed coherent comparator. |
| AB, BC, AB | (6,0,2); (0,6,2); (2,2,4) | Cannot be the probabilities of one fixed unitary on three complete, single-mode ports and orthogonal pure source ports. |

The last claim needs no phase reconstruction. The first two input rows have only **one** common occupied output, C. In the complex inner product of those rows just one nonzero term remains. This is a special case of the known unistochastic triangle condition ([Bengtsson et al.](https://arxiv.org/abs/math/0402325)); it is not evidence against quantum mechanics. Unresolved modes at C, distinguishable internal states, classical mixtures and channels change the comparison.

## How accurate must the four readings be?

Write pXY for the probability of exit Y given input X. If pAC and pBC are each at least 1/4, at least **one** of pAB and pBA must be at least (3−2√2)/8, about 2.14%, for a fixed unitary under that scope. The bound is sharp. More generally, if both bright readings are at least c and both leakages at most z, row orthogonality requires c² ≤ 4z(1−c−z) for 0 ≤ z ≤ (1−c)/2. For the exact values above, dropping **any one** of the four readings permits an explicit real orthogonal completion of the other three. There is no claim that four measurements are always necessary for every device or every exclusion.

The [interval and counting checker](probe_three_port_dark_bounds.py) tests a necessary condition using unequal exact bounds; it is not a complete decision procedure for arbitrary interval tables. Input labels and the same detector labels in both rows must be verified independently. It returns *inconclusive* when the scope is unverified, modes are unresolved or raw counts are incomplete. Zero observed counts do not imply a zero rate. For example, with previously fixed thresholds c=1/5, z=1/100, and 512 independent launches per input, the **hypothetical** rows (384,0,128) and (0,384,128) pass four exact one-sided binomial tests at a joint error level at most 5%. The same proportions at eight launches do not pass. This sampling calculation is separate from exhausting eight shade states: no resampling of simulated states creates experimental evidence.

## Which alternatives survive the echo?

Call the one-block table for AB,BC,AB above T. Apply that entire block again without reading or refilling the apparatus. All 24 complete twelve-cell launches (three source ports, eight shade stocks) return to their initial state. The final port table is the identity. Redrawing shades independently *per block* gives T² instead. Choosing once between two balanced active pairs (AC or BC) and fully dephasing after each stage gives T. Retaining a fixed permutation, or retaining the same coherent balanced Hadamard on the chosen pair, also gives the identity. Thus the echo distinguishes memory assumptions, not classical from quantum dynamics.

Now intervene **between** the two blocks, on port A alone. For input B, none of the eight stocks puts the token in A at this cut. The final A/B/C counts are (0,8,0) without a plate, (2,4,2) after flipping A's local shade, and (0,4,4) after flipping C's shade instead. This is an empty *forward* token port, not an output selected for being dark after the fact. A classical controller remains at A. In a single-particle comparison, an ideal local phase plate acting only on an exactly empty subspace cannot do this. The [intermediate-port probe](probe_dark_intermediate_port.py) checks the tolerance explicitly: let q bound the weight of the entire active subspace, r the final event probability without a plate, and s that probability with it. Then √s ≤ √r + 2√q if the plate acts unitarily, is the identity elsewhere, and downstream evolution is common. Thus q,r ≤ 1/64 imply s ≤ 9/64, below the observed **simulated** 1/4 at A. Unknown modes, tails of the plate action, controller memory, or unverified downstream isolation invalidate this comparison.

A different intervention cyclically reroutes the three **data** cells, leaving shades in place. None of the three source ports then has a return in the native fixture. On the named fixed coherent balanced pair mixture the return probabilities are (1/8,1/8,1/4). The fixed-permutation alternative still reproduces the native response; rerouting does not establish that one surviving implementation is unique.

In a physical three-port experiment the measurement contract matters as much as the table. For example, [Spagnolo et al., three-photon tritter](https://doi.org/10.1038/ncomms2616) used single-input count rates and two-photon interference to reconstruct a different device. Their fitted transfer matrix is not a raw all-launch count sample for the four-cell test above; no IDT device or setting was tested there.
