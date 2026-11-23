# How much can three operations tell us about a contact law?

**Within one finite class they select a single law up to renaming. They do not select a unique primitive for nature.** The three operations were chosen after a working ternary example was known. They express a design target for the bench, not three independently measured laws of physics.

## Filtering all ternary pair contacts

Start with three local values a,b,T. Ask for a deterministic involution on an ordered pair, unchanged when the ends are exchanged, that preserves the number of T marks. The [complete census](probe_ternary_operational_selection.py) filters all 9! permutations and finds 24 such laws. Each capability may use different hardware. Within one capability hold the wiring, contact word and ordinary ancillary stocks fixed when varying its input.

| Additional capability | Remaining raw tables | Why the filter works |
| --- | ---: | --- |
| Varying an ordinary shade can change where one initially fixed T emerges. | 8 | If T always crosses, or always stays, its path through a fixed word cannot depend on the shades. |
| A source shade can affect a different physical site when there is **no T anywhere**. | 4 | Identity or sitewise complement on ordinary pairs cannot carry a difference away from its original site. |
| The device can restore its private input and write an ordinary flag iff that input was T, with the same no-hit response to a and b. | 2 | A passive dye can be routed but is invisible to ordinary occupancy; the active law has an explicit clean meter. |

The survivors are `aa ↔ bb; Ta ↔ aT` and its a↔b renaming; every other pair is fixed. Omitting any one test admits a different law satisfying the other two, with an actual witness. The exclusions concern whole fixed-word classes by local identities, not a timeout in a circuit search. Allow an extra token on the transmission test, adaptive addressing, irreversible contact, more local values, or an external nonlinear detector, and this uniqueness does not follow.

## Change the number of sites in a contact

The [binary pair control](WHEN_THREE_MARKS_CAN_WRITE_A_CLICK.md) rules out a clean vacuum-sensitive switch in its fixed-word reversible two-bit class. But a **three-site** binary contact has another option. With no distinguished end, four reversible laws commute with every permutation of the three sites: leave everything alone; complement every triple; complement only the homogeneous triples; or complement only the mixed triples. The last two are nonlinear. Compare them on one physical encoding: a logical site is a pair of rails; a or b has one filled rail and T has neither. The fourth pair state is not part of that code.

| Binary contact | Exact compiled ternary contact, tested on all 9 input pairs | What distinguishes the raw law? |
| --- | --- | --- |
| E: exchange 000 and 111 only | [Six scheduled offers](probe_binary_unanimous_triples.py) on four data sites and one restored high bit; nine with a low bit | Total filled bits modulo 3 is conserved. A homogeneous raw state can change. |
| M: complement the three bits only if they are mixed | [Thirteen offers on four data sites](probe_mixed_binary_triples.py), **no helper**; eight with a restored high bit, eleven with a low bit | A homogeneous vacuum is quiescent; filled count modulo 3 is not conserved. |

These lengths are exact minima on the indicated hardware and prepared code. For E with four bits, no common injective two-bit encoding of three symbols works: the required switch of aa and bb forces a and b to have the same weight modulo 3. They must then be the two distinct weight-one pairs, and the four-site configurations aa and bb are both jammed. A helper changes that conclusion. In the M case homogeneity, not a conserved tag number, characterizes jams on each connected component whose sites are covered by contacts.

Both compiled circuits reproduce the two-arm prepared observations, including 512 token launches, 1,024 all-ordinary controls and the 72 three-port launches. For E the two-arm apparatus uses 51 binary sites and at most 1,740 offers; the helper-free M compiler removes one site but uses 13 offers per ternary contact instead of six. The labels now describe a **code at observation cuts**: the raw state can temporarily leave that code. The initial pairing of rails, their stock, the addressed triples, ordering, and final record boundaries are supplied. Thus fewer value types need not mean less apparatus, and neither binary law is selected by these observations.
