# When a blank record can travel

Failing a particular apparatus does not invalidate a primitive. The previous [four-label switch](WHEN_A_COLORLESS_TOKEN_READS_TWO_ARMS.md) records a setting in an empty arm but cannot send a change of its 1/2 shade down a vacant road. We varied the contact, kept the original apparatus frozen for calibration, and then tried a new apparatus for a promising failure.

### Census before redesign

Keep three empty labels 0,1,2 and one occupied label •. Require the same reversible contact in both directions, its square to be identity, conservation of the number of tokens, and identical-input pairs fixed. In the homogeneous vacancy off-diagonal sector there are three unordered pairs, each with two wire orders; in the mixed sector there are three more. Independently enumerating the permitted permutations in each sector gives 20 × 20 = **400 labeled laws**. The [census](probe_four_label_law_census.py) retains the full family, including off-target and unread outcomes. Run it with `--enumerate` for stable rule IDs and complete finite records.

| Frozen observation | Laws matching it |
| --- | ---: |
| No plates, both arms open, reciprocal echo on either input | 400 |
| All eight open-arm input/plate rows of the old switch | 2 |
| All 32 rows including both shutters | 2 |
| Both original matched/crossed blank-preparation count vectors, on their own | 16 |
| All 32 switch rows **and** both blank-preparation vectors | 1 |

The two switch survivors give the same entire raw traces on the 512 launches. They differ only on a token beside 0, a contact never offered there; an isolated token/0 encounter separates them directly. Just seeing *some* response to the blank-pair preparation does not separate them: the measured **rates** do. The surviving original moves three unordered input types; its alternative moves four. These are counts within this specified alphabet and symmetry class, not a lower bound on the complexity of the universe.

Now write 1 versus 2 at a sender, offer a contact to a fresh 1 at the next site, and pass on the receiver's actual resulting label. Among all 400 rules, 240 distinguish the messages after one link; 220 never merge the two on this road. Eight of the 16 matched/crossed survivors retain this transport distinction indefinitely. Neither survivor of the old 32-row *circuit* does.

### A rule the frozen switch would have missed

Add just the exchange 12↔21 to the original rule, with all other raw pairs unchanged. Call the new candidate B. It gives the original four-label matched/crossed blank-reader counts, but only **2 of 32** old switch rows. Unlike the original, every operating label 1,2,• moves into a fresh 1 in one contact, leaving a 1 behind. Thus a travelling signal can be a shade of an unoccupied cell; transporting it need not add a detected token.

We searched for a new symmetric circuit using B, judging its source and analyzer on the **open-arm binary-setting** target. The circuit was designed, not discovered as spontaneous motion. Separation distances, sealed replacement rows, and fixed-replacement interventions are separate finite checks on the selected word, not independent laboratory data. Each arm has D and E. Let A offer D:E, Y offer zero:E, X offer zero:D, and C offer the two E cells. With local operations applied symmetrically when appropriate, Q=A Y A and the splitter **and** analyzer are both C Q C Q C Q C. This palindrome of involutive operations undoes itself. The late switch on one arm is X A X A X.

Start the token at either chosen D, the other D at 1 and both E cells independently fair over 1,2. The splitter yields four equiprobable states on each input. The occupied arm encodes a bit as (•,1) or (1,•); the vacant arm as (2,1) or (2,2). The XOR of arm index and the two bits is the input port. The local switch flips its bit for either type of arm, so the analyzer sends the token to input XOR left switch XOR right switch. This is a computation on raw labels, not a measurement of an intermediate route.

To close an arm, forward its D and E into separate fresh-1 dumps; refill the cleared cells with 2 and an independently prepared fair 1-or-2 label. The dumps stay sealed. This **replaces** the previous operating state, not merely its distribution. For each launch, changing a closed-arm plate at a fixed replacement leaves the final detector/loss record unchanged, although the sealed dump may remember the change. A native contact with a fresh 1 is not an unconditional exchange of every arbitrary pair of symbols.

The [mobile-label replay](probe_mobile_blank_interferometer.py) checks all 512 endpoint inputs and four independently specified relay lengths (one per arm before the plates and after the shutters), each 0, 1, 2 or 5 hops: **131,072** associated launches. It reuses exact local traces and checks their composition. The return port is deterministic with both arms open, (left, right, loss) is (1/4,1/4,1/2) with one open, and both closed gives loss one. The zero references, fresh blank stocks, ordered contacts, and token-selective readout remain externally supplied. A two-setting response with native empty-arm transport is a stronger candidate mechanism, **not** a derivation of physical phase or the Born rule.

Replay both probes with `python3 scripts/replay_primitive_probe_campaign.py --bundle bench_mobile_blank_selection`.
