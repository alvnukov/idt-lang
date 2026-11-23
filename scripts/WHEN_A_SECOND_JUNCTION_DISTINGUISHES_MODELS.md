# A single junction can look coherent. Connect two.

The [conserved two-bond packet](WHEN_A_SHAPE_DIRECTS_ITS_NEXT_MOVE.md) moves without further address choices on its prepared sector. But how much geometry did its port guard already require? At every vertex exactly two incident edges have two common neighbors per endpoint pair (“short”), and two have one (“long”). Among the four neighbors, the induced graph consequently has degree sequence 2,2,1,1: it is a four-vertex path. The two long directions are its nonadjacent ends. No triangle contains two long edges. Every long edge has a triangle, so it connects a pair already two short steps apart.

On a nonempty finite connected carrier the short edges must therefore form a **single cycle**, and both distance-two neighbors at each vertex are already required. The accepted graphs are exactly squares of cycles of length at least seven. Disconnected unions can pass the original local guard. The replay reconstructs short cycles without coordinates and exhausts labeled four-regular graphs on five, six and seven vertices (0/1, 0/15 and 360/465 admitted). **The original guard selected a rail; the moving packet did not derive spatial dimensionality.** This is a structural argument and finite cross-check, not a Lean proof.

### Crossing and branching are different laws

At a crossing, define neighboring directions on one rail by the connected components of the neighbor graph. A line-preserving extension recovers 15 rails on a 7×8 product and 147 on a 7×7×7 product, without using the input axis labels to route the packet. But the same law also works on two rings joined at just one site. A packet cannot reach a transverse output; crossing two lines does not make them interact.

Alternatively allow any permitted replacement bond of the right type at the pivot. Both laws agree on an isolated ring. At one common site between an 11- and a 13-site ring, however, the same preparation has 33 reachable states under the line-preserving law and 172 under the alternative. Four events can transfer the whole pair to the other ring. Straight travel and jams are also possible. **Possibility is not a branching probability.**

### First-passage rates, including stops

Now choose uniformly among allowed raw moves. The preparation and four output arms are explicit; a pulse is recorded at its first outward clean reading, and a jam or a trapped recurrent component counts as a separate outcome. There is no division by the number that exit. On two held-fixed fixture sizes, the line-preserving law goes straight. For the alternative, shifting the injected phase-A seed by one site changes what comes out:

| Distance of seed anchor from the junction | Same arm (back) | Straight | Each transverse arm | Jam |
| --- | ---: | ---: | ---: | ---: |
| 6 sites | 0 | 1/3 | 1/3 | 0 |
| 7 sites | 0 | 1/3 | 0 | 2/3 |

Connect **two** junctions using the same physical bonds and let the packet continue without reading and re-preparing its microscopic state. With corridor length 14 and even-offset preparation, the second output in the original corridor has probability 1/3 and each other corridor 2/9. This happens to equal the square of the one-stage probability matrix P (zero diagonal, all other entries 1/3), but the equality was checked on the joined graph. With odd offset the jam probability is 8/9. At length 15 and even offset it is 2/3, even though the first crossing did not jam. Copying a measured one-stage matrix blindly would miss this dependence.

### What the two-stage table excludes, and what it doesn't

A lossless complex four-port with one amplitude per arm can match P exactly. Take a real zero-diagonal conference matrix C, with off-diagonal entries ±1, satisfying C²=−3I and CCᵀ=3I. The amplitudes C/√3 give P; two such devices with no intermediate phases give an echo with probability one. This is a supplied mathematical comparator, not an implementation of amplitudes by the graph.

Could another pair of fixed phase choices match the joined length-14 table? Orthogonality forces *every* one-mode unitary with these one-stage magnitudes to be equivalent to C/√3 up to input and output phases. For aligned connections, let z be the four unit phases between stages. An off-diagonal two-stage probability equals |zₖ−zₗ|²/9 for the complementary pair of arms. Getting 2/9 in all three off-diagonals of even one input would require three mutually orthogonal unit vectors in the real plane. That is impossible. The analysis gives a sharp minimum worst-cell discrepancy over the aligned full table of **(1+√5)/18 ≈ 0.180**. The probe checks the achieving configuration in exact arithmetic. Even varying the fixed one-to-one port alignment cannot give exact equality; the quoted sharp error is for the specified alignment.

Two equally likely phase configurations, however, match the whole baseline **exactly**: (1,i,1,i) and (1,i,−1,−i). This is not evidence the graph or a laboratory instrument randomly uses these phases. In particular, it does not exclude multichannel quantum devices, phase drift or unobserved records.

One additional *calibrated* setting would distinguish these alternatives. Multiply arm j's phase by wʲ, where w=(3+4i)/5. The baseline measures the real parts of the six pairwise phase correlations. The second setting rotates each by a known angle with nonzero sine, making its imaginary part accessible. In the two-setting mixture a previously 2/9 cell becomes 2/5; for complete phase dephasing it stays 2/9. Given the full baseline, one flat additional input column already excludes two discrete phase contexts within this model. Three additional input columns suffice to recover all six complex correlations; two can miss a three-context counterexample. A flat reconstructed identity correlation matrix needs at least four discrete phase contexts, attainable with four sign patterns. This is an experimental *design* requiring controlled phases and an unchanged ensemble, not a phase knob already provided by the binary packet.

Replay the [carrier and junction census](probe_bond_carrier_geometry.py), [literal two-junction rates](probe_raw_bond_junction_rates.py), [fixed-phase comparison](probe_fixed_phase_four_port.py), and [extra measurement design](probe_phase_gradient_tomography.py) with `python3 scripts/replay_primitive_probe_campaign.py --bundle bench_two_junction_comparison`.
