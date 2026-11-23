# A reusable four-place change from reversible pair offers

The earlier [dimer-and-bridge record](WHEN_TWO_CONTACTS_CAN_NAME_FOUR_SITES.md)
could identify four flipped sites, but releasing all its bonds restored the
input. Here **the sites can emerge free with the changed bits**. Three distinct
microscopic rules have the same programmed truth table. Their unprogrammed
motions, input requirements and cost are not the same.

The target is the identity on zero, one, three or four occupied places; on
exactly two, complement all four bits. A clean input or output has **no
internal bonds**. An offer names a pair, whether or not that pair changes.
An input-blind word is one fixed sequence, with no conditional branches or
tests performed by the programmer. A word is still supplied structure.

### A bridge that can release the result

In the guarded sign-symmetric dimer model, add a single possibility:
on an unlike bonded pair of degrees one and two, exchange its bits without
breaking the bond. An isolated four-site path can now rotate either of its
two dimer arms. Its bridge may dissolve only when the middle bits agree.
Both arms must therefore have been swapped an even number of times or both
an odd number of times. From binding the dimers to releasing them, the
clean operation is identity or complementation of all four, not just one
arm. The contact where the bridge is formed is not a simultaneous four-bit
flip.

Number the places 0–3. This single word finishes clean on **all 16 inputs**:

    01 02 03 23 13 03 01 02 23 13 03 01 13 02 23

Eight offers actually change state on each balanced input, four on a
singleton or its complement, and none on either uniform input. For this
guarded rule 15 serial offers are minimal for the entire truth table:
the depth-seven forward and backward balls in the synchronized input
product do not meet. For one known balanced input, eight changing offers
suffice. On the bare path 01–12–23 an allowed input has such a realization,
yet no word can serve all inputs. In particular, complementing 0110 on that
path requires an odd number of 01 offers while cleaning the singleton 1000
requires an even number of them.

In the complete scan of all labeled opportunity graphs and fresh inputs
through five sites (33,867 cases including the empty case), the set of clean
outputs equals the reachability closure of the simple-path moves: flip the
four sites on a path initially reading 0110 or 1001. This is about reachable
endpoints, not matching every microscopic trace or duration. Address
isolation matters: on five sites two extraneous offers touching the quartet
can cancel its intended result while leaving the exterior and all bonds
restored at the end.

### One symmetric Boolean relation

Write a site's mark on the diagonal of a symmetric 0/1 matrix, and a bond
between distinct sites in its off-diagonal entries. This represents a
variable mark and variable mutual bonds in one type of relation; **the
diagonal still carries independent information**. The representation alone
does not explain the existence of sites, marks or encounters.

Here is a much smaller reversible rule for an offered pair:

1. If the marks agree, do nothing.
2. Otherwise, if the parities of their off-diagonal degrees agree, toggle
   their mutual bond.
3. Otherwise, if they are bonded, exchange their two marks.

Toggling a bond changes both degree parities together; an exchange keeps
the marks unlike. Thus the same offer can undo itself. The same 15-letter
word above works for this rule, with the same clean outputs and activity
counts. **No minimum-length claim for this rule follows from the guarded
rule's search.** On four complete sites from one balanced clean input, its
unrestricted orbit has 32 states, only two clean: the input and its
complement. On five sites with two marks, degree parity and exact degree
equality give 5,110 and 400 states respectively. Both can reach all ten
clean two-mark states; the six sharing one original mark first occur after
10 versus 14 changing offers. None of those numbers is a physical time.

There is also a degree-free rule, reading only the **three bits** of its
pair (the two diagonals and their link): if the marks agree, toggle the
link; if they differ, exchange them only if unlinked. The following word
also implements the clean gate:

    repeat 16 times: 01 02 01 23 03 02 03 23 02

This construction needs 144 offers, not a proof that 144 are necessary.
On either uniform input **every** offer toggles a link. The endpoint agrees
with the silent parity rule, but the event histories differ immediately.
Among the twelve reversible pair tables in the specified color-symmetric,
mark-conserving, degree-free class, the other eleven preserve the marks or
act on them from a clean start as a fixed site permutation. Such a permutation
cannot fix every singleton and complement the balanced inputs.

### Ways to distinguish the candidates

- A capped comparison that sees outside-degree types 00, 01 or 11 admits
  12³ pair tables under the stated symmetries; larger outside degrees idle.
  Keeping the 15-letter word fixed, six tables pass the full clean test.
  Failure on that word is **not** failure on every possible program.
- A chain or ring with no possible extra edges cannot distinguish parity
  from exact degree equality: excluding the offered edge leaves at most one
  neighbor per end. On the branching tree with edges 02, 04, 12 and 23,
  the word `04 12 02 12 23 12 23 02 04 23` *does* distinguish them. From
  marks {0,1}, parity finishes with clean {0,3}; exact equality keeps {0,1}
  and leaves bond 12. Offer five compares 2 with 0.
- A fair periodic program need not perform the gate. For the parity rule
  and the single target clean {0,1} → {2,3}, only 240 of the 720 repeated
  orders offering each pair exactly once per round ever hit, even when we
  look after every offer. For the degree-free rule, a **different** check
  asks for all 16 rows to be correct together at a round boundary; none of
  the 720 repeated orders does so at any such boundary.

The outcome is a pair of candidate mechanisms and tests that separate them,
not a selection of the law of nature. The parity test may read many
incident bonds, the program and address convention are external, and the
microscopic inverses give no preferred arrow of time. Compiling operations
also does not supply quantum amplitudes, measurement probabilities, or any
Standard Model species.

Replay the [clean compiler](probe_clean_quartet_compiler.py) and
[single-relation census](probe_single_relation_quartet.py) with
`python3 scripts/replay_primitive_probe_campaign.py --bundle bench_clean_quartet_compilers`.
