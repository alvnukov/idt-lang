# Apamea: fixed transfer to six further settings

The reconstruction selected at 250 K yielded a usable pair at four of the six
preregistered settings. At each of those four, some complete faces changed
sign product. The other two pairs were **inconclusive**: their deposited
files fail the original parser's moment/axis guard, before graph construction.
No temperatures, frames, rows, faces or numerical cutoffs were substituted.

The [published protocol](https://github.com/alvnukov/idt-lang/blob/e1b7b29fab0d29ae1e5f0f59ffabcf88da27e825/data/ergodicity_asi/transfer_protocol.json)
fixes the six pairs and reconstruction independently of their results. Run
`python3 scripts/probe_apamea_fixed_transfer.py` from the repository root for
an offline JSON replay. It checks SHA-256 of the protocol, the published
[250 K reader and graph code](../../scripts/probe_measured_asi_loop_parity.py),
and each present original frame. A missing source is inconclusive; a changed
hash is an integrity error, **not** an inconclusive scientific outcome.

| K | Source rows 000 / 001 | Matched | Only 000 / 001 | Reversed | Complete odd / even | Incomplete | Result |
|---:|---:|---:|---:|---:|---:|---:|---|
| 260 | 1037 / 1036 | 1036 | 1 / 0 | 57 | 59 / 166 | 0 | Usable |
| 270 | 1041 / 1040 | — | — | — | — | — | Inconclusive: frame 000, row 6, axis 135° |
| 280 | 1026 / 1031 | 1026 | 0 / 5 | 57 | 58 / 162 | 3 | Usable; 3 components |
| 290 | 1028 / 1031 | — | — | — | — | — | Inconclusive: axis 0° in frame 000 row 69 and frame 001 row 777 |
| 300 | 1017 / 1015 | 1015 | 2 / 0 | 52 | 57 / 164 | 1 | Usable |
| 310 | 1013 / 1012 | 1011 | 2 / 1 | 48 | 47 / 175 | 0 | Usable |

Rejected row references are the **first** parser failures within each frame,
not an exhaustive census of nonstandard axes. The frozen reader requires
±45° and matching component slopes. No reinterpretation of 135° or 0°, row
deletion or rotation was attempted. A dash means not computed, not zero.

| K | Components | Vertices | Degrees 1 / 2 / 3 / 4 | Bounded simple faces (all 8 edges) | Complete faces by changed classifications: 0 / 1 / 2 / 3 / 4 |
|---:|---:|---:|---|---:|---|
| 260 | 1 | 813 | 47 / 321 / 395 / 50 | 225 | 151 / 55 / 15 / 4 / 0 |
| 280 | 3 | 811 | 44 / 330 / 390 / 47 | 223 | 147 / 55 / 14 / 3 / 1 |
| 300 | 1 | 796 | 44 / 316 / 386 / 50 | 222 | 149 / 54 / 14 / 3 / 1 |
| 310 | 1 | 793 | 33 / 330 / 385 / 45 | 222 | 160 / 45 / 14 / 2 / 1 |

All four usable embeddings had zero intersecting edge pairs and zero
excluded positive-area nonsimple walks. Component count is reported, not
used to reject the 280 K pair: connectedness is not a protocol requirement.
Unmatched islands are retained with unknown transition labels; the size
histogram includes incomplete faces, the parity histogram does not.

### Comparison and limits

The [250 K pilot](../ergodicity_asi/README.md) found 45 odd / 187 even complete
faces. The *qualitative* outcome (at least one odd face) transfers to the
four usable settings, not to six established measurements. If incidence,
matching and signs faithfully describe two instantaneous edge-bit states,
then a complete-star-only update cannot produce an odd complete face on
that graph. This reanalysis does not recover within-frame event order or
classify updates. The composite exposures and lack of per-island confidence
leave readout alternatives open. Shared edges, the same author archive and
instrument, and only one selected frame pair per setting do not justify
independent trials, temperature-dependent event rates, classification-error
probabilities or independent replication. No fundamental theory is tested.
The 250 K cut-distance certificate is not applied to these different graphs.

### Source and exact bytes

Unmodified coordinate/moment tables: Michael Saccone, Francesco Caravelli,
Kevin Hofhuis, Scott Dhuey, Andreas Scholl, Cristiano Nisoli and Alan Farhan,
*Real-space observation of ergodicity transitions in artificial spin ice*,
[Zenodo data version, 15 August 2023](https://doi.org/10.5281/zenodo.8250892),
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
See also the [authors' article](https://doi.org/10.1038/s41467-023-41235-4).
The six-pair analysis and guard outcomes are ours, not the authors' claims.
Only these coordinate tables are included; no raw microscopy images.

The [versioned content endpoint](https://zenodo.org/api/records/8250892/files/apameaData.zip/content)
served a 6,450,591-byte ZIP. We retrieved the central directory plus end record
(inclusive bytes 6,402,619–6,450,590), then six ranges, each covering exactly
the two contiguous local records selected at that temperature. For each
request we checked HTTP 206, exact Content-Range and length. For each member
we verified local-header name, compression method, sizes and CRC against
the directory, checked the consumed deflate payload and recomputed length
and CRC-32 on in-memory original bytes before exclusive local writes. The
SHA-256 values below hash those bytes including the original line endings.
The local paths retain the original archive names. No full-archive checksum
verification is claimed.

| Member (relative to this directory and ZIP root) | Inclusive local-record bytes | Uncompressed bytes | CRC-32 decimal | SHA-256 |
|---|---:|---:|---:|---|
| `260K/coordinates_000.dat` | 965197–974616 | 38685 | 2432815397 | `542027a22ebe9e1eb49572de69538b23884f98b97c4dd940b105d1c56d82fff9` |
| `260K/coordinates_001.dat` | 974617–984037 | 38658 | 1348604433 | `435e0c64c3e076eccfca5f159c1aba1513844ea14c193e5c1f916d771905f411` |
| `270K/coordinates_000.dat` | 1908919–1918466 | 39385 | 1353135697 | `da226c88644daaca00309da3ff43c38a73439a8efbb19eb0d9de00e1950f3187` |
| `270K/coordinates_001.dat` | 1918467–1927949 | 38857 | 1122740457 | `061cb39aad0142fc81cd384b6942326a7a0749a92761b8eff530152346a95894` |
| `280K/coordinates_000.dat` | 2861753–2871015 | 38257 | 2354048909 | `f53cd90369c6c3935866e6f16bd6d90d4e1c52af99b153345135de447fa4ecba` |
| `280K/coordinates_001.dat` | 2871016–2880361 | 38473 | 3203278045 | `2c781eaeaa4c4451690b394a50814feecd9c6a8f12433fced0dc6d29f093f53d` |
| `290K/coordinates_000.dat` | 3704817–3714153 | 38296 | 2235789579 | `0cf8dbcca907acd6b0b768cc47fefcc5a28ddaa626456ac19d70c95cd4f98c8e` |
| `290K/coordinates_001.dat` | 3714154–3723508 | 38414 | 3143915503 | `9f27e22a71f5e3b493c6a75431cd5295b03d901fb1f5d921e038ae90965ff970` |
| `300K/coordinates_000.dat` | 4552786–4562091 | 37911 | 687103075 | `9cb81c35a40dccf61ac212b021340f955a0c5b8f1d0681a5a681efea8fcfe56b` |
| `300K/coordinates_001.dat` | 4562092–4571342 | 37844 | 27293017 | `0d5045f7bd25ef1a55947bf50272e80bfda09e692b6dc5c1216bd206ab530957` |
| `310K/coordinates_000.dat` | 5481935–5491130 | 37799 | 1503626619 | `1760299e0d05d632f7f7d8dfd745429c775b07a24c04de7ff4d0e9961856ae59` |
| `310K/coordinates_001.dat` | 5491131–5500366 | 37759 | 2161354816 | `935f80ec5c310b9c3d47ad1bf409bac92786f9c612651f689e9b3a93d36d2a1c` |
