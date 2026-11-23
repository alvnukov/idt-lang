# The bonds are conserved. Are two particles still present?

For the [moving two-bond candidate](WHEN_A_SHAPE_DIRECTS_ITS_NEXT_MOVE.md), call one short and one long marked bond a *free packet* only when their isolated state can execute the known gait. Given two marks of each type, try both complete pairings. Keep every compatible one; do not assign hidden particle labels to resolve a tie. This definition concerns an observable decomposition, not the existence or disappearance of fundamental particles.

| Raw states on the square of a 16-site cycle | Number |
| --- | ---: |
| No decomposition into two free packets | 10,640 |
| Exactly one decomposition | 3,440 |
| Two decompositions | 320 |

The counts exhaust all 14,400 states; they are not a probability distribution unless a preparation is specified. The short bond compatible with a given long one can start at six consecutive positions. Counting four-cycles in this compatibility graph independently gives 20n double readings and n(18n−73) unique readings for n ≥ 11. In 928 of the uniquely pairable 16-site states there is a raw allowed move that is not explained by independently advancing the two identified packets.

From three actual two-packet inputs on the ring, the shortest words losing **all** full pairings take seven, six or two events. From every first such endpoint a unique reading can be recovered (minimum nine, two or four more events, respectively). Recovery is possible, not inevitable: there are indefinitely continuing histories without a full pairing. Short and long bond counts remain unchanged throughout. A detector should therefore not silently discard configurations that no longer look like its two incoming packets.

### Same singles, different coincidences

For concreteness, Sᵢ joins i to i+1 and Lᵢ joins i to i+2, with indices modulo 16. On each trial randomly rotate a four-bond input. Evolve by a supplied uniform distribution over enabled moves. Translation symmetry and count conservation keep every individual bond's occupancy probability at 1/8.

A two-edge detector counts N on {S₀,S₁}; its mean is 1/4. For the near preparation {S₀,S₁,L₋₃,L₃} the normalized factorial coincidence E[N(N−1)]/E[N]² is 2 initially. For the far preparation {S₀,S₈,L₋₃,L₅} it is zero. At the second event every near coincidence has *two* possible packet readings; insisting on a unique reading loses them all. The far input first gives a coincidence on the tenth event, with probability 1/41472 in this fixed bin, exclusively on states with **no** full two-packet reading.

The baseline matters. For two uniform distinct short slots the same statistic is 4/15; for precisely two independent draws allowing repetition it is 1/2. Neither is the Poisson reference of one. On a single Boolean bond a factorial coincidence is zero by definition. None of these facts supplies a fermionic exchange sign or a bosonic enhancement.

[Jeltes et al.](https://doi.org/10.1038/nature05513) measured bunching of metastable ⁴He and antibunching of metastable ³He in the same apparatus. Their atom-pair separations after free expansion were normalized using single-detection distributions; finite detector resolution matters. The [authors' supplementary fits](https://arxiv.org/pdf/cond-mat/0612278) give vertical correlation lengths of 0.56 ± 0.08 mm and 0.75 ± 0.07 mm, respectively. The [⁴⁰K lattice experiment of Rom et al.](https://doi.org/10.1038/nature05319) provides a distinct fermionic noise-correlation measurement. None measures our ring bin, or calibrates a bond as an atom. These are targets for constructing a source and detector, not fits or confirmations.

### Even complete pair tables can hide the next response

Prepare a uniform rotation **and reflection** of either {S₀,S₄,L₁,L₉} or {S₀,S₄,L₅,L₁₃}. Direct enumeration gives identical 32 singleton probabilities and all 496 unordered two-bond probabilities. The first shape has no full packet pairing and the second has one. After one uniformly selected event the probability of occupying both S₀ and S₃ is **0 versus 1/32**; on S₀ and S₅ it is reversed. Some initial three-bond correlations already differ. Another pair of initial shapes has the same static ambiguity and only one enabled move on each, so no random choice of event is necessary for that control.

For the 484 distinct uniform symmetry-orbit preparations on the 16-site carrier, the full initial pair table gives 480 different signatures. Two one-event readings, (S₀,S₃) and (S₀,L₂), suffice to resolve the remaining collisions; no single pair does. This identification does **not** extend to arbitrary mixtures. Two different mixtures of idle shapes agree on every pair at every repeated snapshot, yet the triple S₀,L₃,L₄ has probability 1/64 in one and zero in the other. The idle states have no next event.

The [finite sufficiency checker](probe_pair_response_span.py) makes that distinction executable for other submitted menus. Include normalization in a matrix whose columns are preparations and whose rows are known measurement expectations. A proposed response is either a linear combination of the rows, with coefficients checked on each preparation, or there is a rational null vector. Splitting that vector into normalized positive and negative parts gives two **ordinary nonnegative mixtures**: identical measured data, different response. This excludes a proposed closure of the measurements, not the primitive. It applies to every mixture on the specified finite menu, not to unsubmitted physics.

**Do triples suffice if idle states are removed?** No. Fix two short starts at 0 and 4. Prepare an equal mixture of long-start pairs (1,13) or (5,9), or instead (1,5) or (6,10). Uniformly rotate and reflect each shape. All are in the active recurrent sectors of the symmetry-randomized source. All 5,488 labelled one-, two- and three-bond inclusion probabilities agree. Half the mass in either preparation has one enabled move and half has three. Yet after one uniform enabled move P(S₀ and S₃ both occupied) is **1/32 versus 1/96**. No state was discarded. For arbitrary mixtures in this particular four-mark family, order four is necessary and sufficient if the question is the least *full equal-time inclusion hierarchy* predicting that response: the order-four entries are already the probabilities of the complete raw states. This is not a four-body physical force. [Replay the compact witness](probe_active_triple_witness.py) in bundle `bench_active_triple_witness`.

By contrast, restrict the initial menu to its 94 symmetry orbits (3,008 raw states) with **one enabled next move**. For every mixture of these orbits the same target equals p(S₀,S₃) + 2[p(S₀,S₄,L₅)+p(S₀,S₄,L₄)−p(S₀,S₃,L₄)−p(S₀,S₃,L₃)], using initial lab-frame inclusions. The [one-offer regression](../tests/test_active_triple_witness.py) compares this decoder against all 94 orbits individually. Orders three and four are therefore not rival universal laws: the required order changes with the specified preparations, even for the same next detector.

Replay the [matching and recovery census](probe_two_packet_matchings.py), [raw coincidences](probe_matched_singles_bond_counts.py), [ambiguous pair histograms](probe_hidden_pair_correlations.py) and the finite sufficiency checker with `python3 scripts/replay_primitive_probe_campaign.py --bundle bench_packet_identity_and_readout`.
