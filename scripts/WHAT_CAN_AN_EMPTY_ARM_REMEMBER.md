# What can an empty arm remember?

Two different tests ask where a later detector response can come from. The models below use different local laws; the second is **not** an extension derived from the first.

### The two-bond packet has a narrow entrance

Keep a fixed single input to the [free-pivot junction](WHEN_A_SECOND_JUNCTION_DISTINGUISHES_MODELS.md), with an unchanged, empty, homogeneous stretch before it. Only the two moving bonds may enter; there is no independent clock or persistent device memory. At first forward touch of a section six short steps from the junction, the isolated gait can present two shapes. For a right-moving packet and section coordinate q, both have short bond (q−1,q); their long bonds are (q−3,q−1) in A and (q−4,q−2) in B. These are actual bond configurations, not phase tags assigned on entry.

Count enabled moves from that touch, including unsuccessful histories, and choose uniformly among distinct enabled moves. On each of four inputs of two wedge fixtures and the far crossing with unequal corridor lengths:

- A jams at move 11 with probability 2/3; otherwise it exits straight at move 21.
- B never jams. For each of three non-return exits, the probability of first reaching it on move 20+k is (1/9)(2/3)ᵏ for k ≥ 0. Exact first-hit propagation and the finite transition-matrix recurrence certify the tail.
- Under the alternative line-preserving law, both go straight, A at move 21 and B at move 20.

Thus an upstream change can be invisible to an arm-and-arrival-time monitor and still change the output by changing the shape. **But if both settings must pass the free junction with certainty**, neither may deliver A. Both must deliver the same B on that input. With the same arrival-time distribution and a state-complete, time-independent move law, the detector then receives identical output histories in distribution. This rules out a lossless phase switch *across this separating interface*. An extra incoming mark, a change to the junction, or persistent environmental memory invalidates the premise. Active-move counts are not laboratory time.

### Write a relation before there is a packet

In a separate experiment prepare four independent empty cells A, B, A′, B′, each with equiprobable raw labels 0 and 1. Apply one identical binary contact on each of two disjoint pairs, either AB and A′B′, or AB′ and A′B. Retire A′ and B′ without looking at them. **Only then** inject a token at C. Read both preparations with the very same contacts AC and AB, in that order. Every trial ends with one occupied output. The complete single-cell histograms of A and B **before the reader** are identical between the two preparations.

| Contact | Outputs (A, B, C), originally paired | Outputs (A, B, C), crossed pairing |
| --- | --- | --- |
| [Eight labels](probe_eight_label_interferometer.py), original rule | (1/2, 0, 1/2) | (5/16, 3/16, 1/2) |
| Same mixed contact, vacuum-XOR variant | (1/4, 1/4, 1/2) | (1/4, 1/4, 1/2) |
| Four labels, uncolored token | (0, 1/4, 3/4) | (3/16, 1/16, 3/4) |
| Four labels, same mixed contact but identity on blank pairs | (1/4, 1/4, 1/2) | (1/4, 1/4, 1/2) |

The four-label rule swaps just three pairs of ordered configurations: 01↔02, 10↔20, and •1↔1•. Everything else stays put. After the first contact, the equally likely paired blank states are 00, 02, 20, 11. To get to B, the token must meet a 1 in both cells; that happens in 1/4 of paired trials versus (1/4)² in the crossed trials. A full uniform stock over all empty labels offers no such resource: a reversible map preserves the uniform product. Also, failure of this particular reader to tell two stocks apart need not mean their joint raw states are identical.

With only **two** empty labels, every reversible blank contact commuting with wire exchange permutes the two diagonal inputs among themselves and the two off-diagonal inputs among themselves. One such contact on independent identical Bernoulli blanks leaves a product distribution: it either preserves both biases or complements both. The three empty labels above therefore attain the minimum for *this single-contact correlation preparation*, not a fundamental number of states in nature. The four-label contact squares to identity, unlike the eight-label contact which squares to exchanging the wires. These checks do not generate a physical vacuum, an interferometer fringe, a preparation probability, or a detector from first principles.

Replay the [entrance](probe_two_bond_entrance_collar.py) and [packet-free preparation](probe_packet_free_pair_record.py) together with `python3 scripts/replay_primitive_probe_campaign.py --bundle bench_empty_arm_record`.
