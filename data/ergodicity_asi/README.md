# Two deposited 250 K frames: Apamea artificial spin ice

These are unmodified coordinate/moment tables from Michael Saccone, Francesco
Caravelli, Kevin Hofhuis, Scott Dhuey, Andreas Scholl, Cristiano Nisoli and
Alan Farhan, *Real-space observation of ergodicity transitions in artificial
spin ice* (2023). [Version-specific data record, 15 August 2023](https://doi.org/10.5281/zenodo.8250892);
[article, especially Fig. 1 and Methods](https://www.nature.com/articles/s41467-023-41235-4).
The data are redistributed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
The parity calculation below is a new reanalysis, not a claim made by the
depositors. No raw microscopy images or other frames are included.

| Member in the deposited `apameaData.zip` | Bytes | CRC-32 (decimal) | SHA-256 of original CRLF bytes |
| --- | ---: | ---: | --- |
| `250K/coordinates_000.dat` | 39617 | 1688648756 | `38ff466252d49e7c1c6ae61c28c407f2af5bc6447b63336dfc5cc1021ccf4df1` |
| `250K/coordinates_001.dat` | 39650 | 576837988 | `4af3edaa975909ba2189d5623a30e94504d995651039ca535dbec24f2966dfb8` |

The local filenames omit the `250K/` prefix. To verify against the source,
use the version-specific [archive content endpoint](https://zenodo.org/api/records/8250892/files/apameaData.zip/content).
The 6,450,591-byte ZIP has a central directory at bytes 6,402,619–6,450,568.
The two complete local records occupy inclusive ranges 0–9,585 and
9,586–19,242. Both were retrieved with HTTP Range; status 206, Content-Range,
payload length, member names, decompressed sizes, CRC-32s and the two SHA-256s
were checked. No checksum of the *entire* archive is claimed here.

## From table rows to an observable

Run `python3 scripts/probe_measured_asi_loop_parity.py` from the repository
root. It checks the hashes before parsing and prints deterministic JSON. The
sampling rule is the first two consecutively numbered tables at 250 K; no
face is selected for having changed. Each output row reference is a 1-based
line number in its **own** original table. The two files use different row
orders.

1. Treat columns 1–2 as center coordinates, 3–4 as classified moment
   components and column 5 (±45) as the undirected diagonal axis in the
   deposited coordinate convention. Check that the sign of the slope agrees
   with the component pair. Use the sign of column 3, not its magnitude, for
   the within-axis binary classification. The magnitudes differ between the
   two frames; they are not a calibrated probability or error bar.
2. Match same-axis centers across frames within Euclidean distance 4 in
   native table coordinates. Accept only one-to-one candidates; stop on
   ambiguity. Use averaged positions for matched islands and retain unmatched
   islands in the graph with an unknown change bit. All 1061 first-table
   rows match; second-table rows 54 and 670 do not. Of the matched rows, 42
   change classified sign.
3. Use *virtual* incidence endpoints at offsets `(d, d × sign(column 5))`
   for `d = ±11.75` (half a coordinate step of 23.5 along each axis). These
   are graph-construction parameters, not magnetic moment magnitudes, literal
   island ends, SI lengths, physical contacts or uncertainty estimates.
   Cluster endpoints by single linkage at Euclidean distance ≤4; locate
   each vertex at its cluster centroid. One island is one edge.
4. Reject collapsed/parallel edges or a crossing in the primary straight-edge
   drawing. Follow each directed edge with the predecessor of its reverse
   in counterclockwise neighbor order. Count every positive-area face walk
   without a repeated vertex. If either sign of a boundary edge is missing,
   count the face as incomplete, not even. On a complete face, an odd number
   of changed signs means that the product of binary signs changed.

The primary graph is connected: 1063 islands, 832 vertices, and 232 bounded
simple faces (also `1063 − 832 + 1 = 232`). All 232 have eight island edges,
not necessarily eight geometric corners. There are 45 faces with one changed
classification, 13 with two, 174 with none, and zero incomplete faces. Thus
45 are odd and 187 even. For example, tracing frame-000 rows
`8,9,14,10,36,61,59,35` gives frame-001 rows `9,11,14,10,33,63,58,32`;
only the pair `61 → 63` changes sign.

## Geometry sensitivity and limits

### How many sign comparisons would have to change?

On this fixed graph, **28** of the 1,061 known binary transition labels would have to change to make the two frames compatible with *unrestricted* full-star flips. This is a deterministic distance to a model, not an estimate of how many measurements are wrong. The [certificate checker](../../scripts/probe_asi_cut_distance.py) gives both bounds. Its lower certificate contains 24 individual odd faces and two triples of odd faces, with no shared edges between groups. One edge cannot hit all three faces of either triple. The upper certificate lists 28 toggles and verifies a binary vertex assignment whose endpoint differences give every corrected known edge. The two unmatched islands are bridges; neither requires an invented observation. Additional firing guards can only make the model more restrictive.

A synthetic counterexample also matters: if some edges are read before a full-star flip and others after it, a recorded loop can be odd even though every instantaneous loop was even. The deposited signs have no per-island error bars that would exclude such a readout. This is an alternative to an instantaneous direct-edge interpretation, not an assertion about what happened during the authors' exposures.

### Alternative reconstructions

Before reading other temperatures' sign outcomes, the [transfer protocol](transfer_protocol.json) fixes the other six temperature settings, the two frames at each, the numerical geometry parameters, and the conditions for reporting an inconclusive result. This distinguishes transfer of a data-analysis method from confirmation by an independent experiment.

At endpoint cutoff 5 the census is unchanged. At cutoff 3 the inferred graph
splits into two components and has a nonincident crossing (row pairs
`990 → 992` and `1011 → 1012`). Its rotation-order enumeration gives 213
positive simple walks, 43 odd, and nine additional positive walks with repeated
vertices. These are **not** a valid planar-face census for that embedding.
Reversing only the slopes at fixed centers is another distinct construction,
not a reflection of the entire coordinate system. It has no degree-four
vertices and yields 50 four-edge and 133 twelve-edge walks, 34 odd overall.
The primary convention reproduces the two-, three-, and four-island junctions
described in Fig. 1 and agrees with the tabulated component slopes. The
odd count is not the justification for this convention.

Flipping every edge incident to a vertex changes zero or two edges of any
simple cycle. A sequence of such complete-star flips therefore preserves its
sign product. The odd faces are incompatible with **only that direct
edge-bit model**, conditional on faithful classification, matching and
incidence. They do not distinguish a swap rule from other non-star changes,
or identify which microscopic updates occurred. The islands interact
dipolarly; their reconstructed vertices are not physical contacts. Each XMCD
frame composites measurements at opposite polarizations over roughly 10 s.
Neither per-island classification confidence nor within-frame event order
is provided by these tables. Faces share edges, so 45 is a census, not 45
independent events or a statistical confidence level. This replay tests no
fundamental physical theory.
