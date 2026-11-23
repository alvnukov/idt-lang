# No marks on sites: a quartet operation using links alone

The [diagonal-bit candidate](WHEN_A_RELATION_CAN_DELIVER_FOUR_CHANGED_BITS.md)
stores an independent mark on every site. The following candidate removes
those marks entirely. Its state is a simple undirected graph. For an offered
pair of distinct vertices, compute p and q, the parities of their numbers
of incident edges **other than** the offered edge. Toggle that one edge if
**p OR q** is true. Nothing else is updated. The two control bits are
unchanged by this toggle, so repeating the offer undoes it.

This local involution can implement the four-bit truth table. It need not
conserve the number of edges at every intermediate step. A site's derived
degree parity should not be silently identified with a conserved particle.
For example, requiring conservation of the number of odd vertices on *every*
offer leaves just two of the eight symmetric two-parity predicates: idle
or toggle on unlike parities. The latter acts as a fixed site permutation
on the parity bits for a fixed word. Its edge update is linear over GF(2).

### Four vertices, one changing work edge

Number the edges of K₄ as 0=01, 1=02, 2=03, 3=12, 4=13, 5=23. Store four
data bits on edges 0–3, with the others initially absent. This word of edge
indices has length 30:

    403412431201240120124034214304

It complements every half-filled data word, fixes all ten other words,
and leaves the work edges blank again. Edge 5 is never offered. NAND
(toggle unless both outside parities are odd) also works, with an explicit
74-offer word changing only one work edge. At least one changing work edge
is needed in this encoding: with all other edges fixed, each generator
flips a data edge according to a degree-at-most-two Boolean polynomial
of the other three data bits. Such a polynomial has an even number of
true rows, so every word is an even permutation of the sixteen data states.
The desired gate is *three* transpositions, hence odd. These are work-space
bounds, not optimal lengths for OR or NAND.

Separate input-dependent paths and a common word are distinct tests. Over
the 60 choices of four data edges and constant values of the two others,
OR and NAND can reach each of the six balanced targets separately on all
60 layouts; for AND and NOR no layout reaches all six. Even the OR/NAND
programs do not select their own ports. In each layout some permutation
of the four vertices fixes a balanced input graph but not its intended
output. For the displayed encoding, mask 5 is fixed by exchanging vertices
1 and 3, but target 10 is sent to 34. No deterministic terminal map of that
bare graph respecting vertex relabeling can give the specified output.

**Existing-contact control.** Require a bypass between the offered
endpoints using only existing edges and excluding the offered edge.
This guard preserves connected components. With bypass length at most two
(a common neighbor), OR fails on at least one balanced target on every K₄
layout. With length three an OR word succeeds on a layout with two occupied
work edges. NAND already succeeds at length two with these work bits.
The bypass and the work preparation are substantive inputs. The empty graph
is silent for OR, active under unrestricted NAND, and silent again under
this bypass guard.

### Passing a gate in isolation did not make it a module

Glue two of the 4-vertex layouts by identifying one data edge, changing
nothing in the old programs. The outside degrees at its endpoints can now
depend on the other inputs. Over all 32 role/orientation choices and every
seven-bit input, **not one** gluing reproduces the two specified operations
on all inputs. Of 128 outputs, 18–57 are correct for the short OR word and
23–80 for the NAND word. Even a correct final state can conceal an incorrect
intermediate one. This fails two particular compiled interfaces, not every
way of connecting graphs.

There is a more expensive interface that does compose. Store each logical
bit on a physical edge with endpoints disjoint from those of the other
logical bits (a matching). A seven-offer OR word gives controlled XOR on
two such bits, cleaning all temporary links. For a three-bit controlled
operation, temporarily join one end of each disjoint control x and y. This
stores j=x OR y; the outside degree parity of the first end is then x XOR j.
Three offers copy that parity into a blank disjoint edge. Controlled XOR
to the target, reversal of the temporary operations, and a final controlled
XOR from y toggle the target by x XOR j XOR y = x AND y. The resulting
Toffoli takes **22 offers**, restores both controls and cleans its workspace.

Four data edges, two blank logical work edges and one reusable scratch
edge now suffice. The indicator of weight two is the XOR of all six
pairwise products and all four triple products. Compute it into a blank
flag, toggle the four data bits by it, then uncompute: the indicator itself
is unchanged by the target operation. This 820-offer construction restores
the whole graph on the clean boundary apart from the intended data. Two
quartets sharing a matching-encoded logical edge compose in *either*
specified order on all 128 inputs, also with an independent occupied or
empty spectator edge. The two orders are not interchangeable: their
logical outputs differ on 54 of the 128 inputs.

This is evidence for a simple **computational substrate**, not for nature
selecting it. The logical port layout, initial workspace and sequence of
offers have been supplied. Indeed the ability to implement a Toffoli gate
makes agreement with freely programmed Boolean fixtures less discriminating.
Local encounter restrictions, silent backgrounds, independent readout,
and schedule-free predictions demand separate tests.

Replay the [atomic rule and locality controls](probe_loopless_link_quartet.py)
and [composition/cross-talk controls](probe_loopless_matching_ports.py) with
`python3 scripts/replay_primitive_probe_campaign.py --bundle bench_loopless_matching_logic`.
