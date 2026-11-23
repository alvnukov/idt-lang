# When pair contacts can identify four participants

There are three different requests hiding in “make a four-place event from
pairs”: reach the right bits, recognize that they are right, and leave the
result available for the next event. The first two are possible in the
following finite models. The last does **not** follow from either certificate.

## A certificate on four supplied places

Give each place a symbol with a binary occupation. Use one reversible pair
table on all six opportunities; it must commute with swapping the two ends
and preserve the number of occupied places. Fix a fresh symbol in each charge
sector. From every fresh two-of-four mask the goal is the *sitewise* opposite
mask. The reader may see the current unordered histogram of symbols, not the
initial mask, port names or history. A sound positive signal must be reachable
from every valid preparation. **Global** soundness applies at every visit;
**first-hit** soundness requires an observer armed at preparation and applies
only to its first positive read. Neither requires every schedule to signal.

| Number of symbols per charge | Pair tables | Some path reaches complement | Sound first-hit table | Globally sound table |
|---|---:|---:|---:|---:|
| 1 + 1 | 2 | 1 | 0 | 0 |
| 2 + 1 | 32 | 22 | 0 | 0 |
| 2 + 2 | 6,144 | 5,448 | 12 | 8 |

The tables in the final columns are counted once even if they admit multiple
readers. All the positive four-symbol tables allow a test for a pair of
identical spent symbols at the corresponding soundness level. None admits a
sound test for the occurrence of a single symbol, even at first hit. For
example, let 0/2 be fresh empty/occupied and 1/3 their spent versions. Use
`02 ↔ 31` and its port reflection, leaving other pairs alone. Two disjoint
unlike transactions reach the complement. Two spent empty places certify it
on four half-filled places; they cannot have appeared in the first transaction
alone. A supplied four-offer word works for all six inputs, but offering each
pair twice in succession forever is pair-fair and avoids completion.

A fifth empty-charge marker `r` allows `11 ↔ rr`: seeing even one marker now
certifies the current complement. The emitted markers come in two copies.
All seven states reachable from each valid preparation were checked,
including after erasure and refiring. On six places this very reader fails:
`222000 → 122300 → 112330 → rr2330`. It identifies neither the intended cell
nor the completion of the whole six-place input.

Why the small-alphabet obstruction makes sense: if one charge has just one
symbol, one of its two initial places can keep its original charge through
any proposed sequence of histograms. Use the other carrier for mixed-charge
contacts; contacts between the two singleton-charge carriers cannot change
their charges or the histogram. Thus the histogram alone cannot force
sitewise complementation. Before the **first** appearance of a proposed
fourth-symbol flag, at most three symbols have been used, so a similar
spectator survives up to and including its production. This argument is for
anonymous pair opportunities and a positive current-symbol test, not for
arbitrary circuits, prepared ancillas, or sensors attached to particular sites.

## A quartet selected by bonds instead of a four-place box

Start with binary sites, no bonds and a supplied graph of possible encounters.
An offered pair can do either of two things, with the inverse also allowed:

1. Two isolated unlike bits swap and bind into a dimer.
2. Two current zeros, each already the end of a distinct isolated dimer,
   acquire a bridge without changing their bits. In the zero-only rule it
   suffices to test degree one at both unlinked ends on reachable states.

The connected pieces are single sites, unlike dimers and paths `1–0–0–1`.
A central bond in a path identifies *which four* are currently flipped
relative to their initially free bits; the rest of a larger system need not
be unchanged. The third encounter creates the record; both swaps have
already happened. An immediate reversal removes the record.

| Complete opportunity graph; one balanced preparation | States | States with ≥1 record | States with 2 records | Shortest ordered histories to first record |
|---|---:|---:|---:|---:|
| 4 sites | 9 | 2 | 0 | 4 |
| 6 sites | 70 | 36 | 0 | 36 |
| 8 sites | 785 | 576 | 72 | 144 |

On a fixed opportunity graph a first record is possible exactly when a simple
path with fresh values `0–1–1–0` exists; extra chords are harmless. Its two
end edges allow the swaps and its middle edge allows the bridge. Conversely,
the two dimers and bridge of any record supply just such a path. Exhaustive
graph/preparation replays agree in 1,024 four-site and 32,768 five-site cases.
A bare path without this preparation, for example `0–1–0–1`, does not suffice.

The preferred zero is a real input. Allowing either sign to bridge while
testing only endpoint degrees creates a four-cycle on four sites and a
six-site chain on six. Sign symmetry can be restored by checking also that
each endpoint's outside neighbor has degree one before making or removing a
bridge. That is additional access to the neighborhood. No detector clock,
force, dimension, probability distribution or irreversible event follows.

Most importantly, **current bit XOR “has any bond” equals that site's fresh
bit** throughout this construction. If all bonds disappear, the original
bits return. Keeping the record is not the same as delivering four changed
free bits. This is a concrete obstacle to composing this particular candidate.

Replay both the [pair-table census](probe_pair_contact_completion.py) and the
[dynamical bond probe](probe_relational_quartet_records.py) with
`python3 scripts/replay_primitive_probe_campaign.py --bundle bench_pairwise_quartet_records`.
These are reproducible finite findings and scoped arguments, not new Lean
proofs or evidence that nature uses these symbols or bonds.
