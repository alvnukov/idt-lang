# Is counting witnesses necessary to update one link?

The state is a simple undirected graph. Offer an unordered pair of distinct vertices. If **any** other occupied link meets either end, flip the offered edge exactly once. Two witnesses still cause one flip. This is different from applying one controlled flip per witness: two such flips cancel, and a fixed sequence of individual controlled XORs remains linear. No independent site marks or parities enter the new candidate. The event and its site are still offered; the rule does not select an encounter.

The zero graph is silent. For a connected family of potential links (their line graph is connected), *all nonempty states communicate*: keep adding neighboring links until all are present, then reverse the other state's path. Thus being able to find a different path for each desired input/output pair is **not a discriminating success**. Ask for a single word that acts correctly on every input.

On the six edges of K₄ in lexicographic order, four data edges (01, 02, 03, 12) and two absent worker edges suffice. The [previous parity rule's word](WHEN_LINKS_ALONE_CAN_CHANGE_FOUR_BITS.md) still works on only six of sixteen inputs. This new fixed word, read left to right, uses no worker edge and gives the exact half-filled complement, fixing the other ten words:

    3130301020301012013020101201302010120130230201030313

This distinguishes two kinds of simplicity. The rule is short, but **any permutation** of the 15 nonempty data states is programmable in that layout. A quarter-turn, a coincidence, or a Boolean table obtained just by choosing instructions provides little evidence that the rule itself selects the operation. Three four-cycle layouts, in contrast to the twelve triangle-with-tail layouts, yield only even permutations and cannot implement this odd quartet without a writable work edge. Repeating a sweep that offers each of the four data edges once never exceeds 10/16 correct, even over all orderings and all powers. With sweeps over all six edges the best is 11/16.

All six K₄ offers generate the even permutations of 63 nonempty masks. Two complete certificates test different requirements on the initially nonblank work bits. An 88-offer word implements the quartet on the clean sector and disturbs only two other masks, the minimum possible because the clean quartet is odd. A 264-offer word implements the quartet on **all four** initial work assignments and restores those two bits on all 64 inputs. Neither can insulate the gadget from an arbitrary environment: three fixed occupied exterior leaves touching three different K₄ vertices make all internal offers unconditional. No internal word then matches more than ten clean inputs.

### How cheaply can a checker distinguish the rules themselves?

Compare two local summaries: each endpoint's **parity** of its other links, or whether it has **any**. Allow all eight symmetric Boolean tables on the two summaries. Optionally require an existing bypass of length at most two or three around the offered edge. This gives 48 named rules. Relabel the tested offer to 01 and suppress its own bit, since every predicate ignores it. A trial asks a single binary question on a fresh prepared graph: did the offered edge change?

Three-, four-, five- and six-vertex carriers separate 8, 25, 27 and **28** classes respectively. Six vertices already realize all twelve possible combinations of parity row, occupancy row and bypass category: if an endpoint has no other link there is no bypass; if both have one, each of the three parity rows and each of the three bypass categories are possible. A larger graph cannot split another alias **for these 48 laws**. The checker returns every original label in each class; an unmodeled mechanism can still mimic its whole transcript.

| Cost in binary reads (fresh preparations) | Fixed panel | Adaptive next read |
| --- | ---: | ---: |
| No erroneous answers | 9 | 5 |
| At most one erroneous answer in total | 27 | 11 |

The robust adaptive tree replays all 28 truthful and 223 single-error histories, with no loss of the true class. For a short independent lower bound, follow the all-zero response class. Five actual rivals differ from it on disjoint sets of queries. Each set must be queried at least twice or a rival can mimic zero using one lie. If the worst case were ten, exactly two hits per set would be possible on this branch; flipping the final answer would then leave a rival able to match all ten answers with one earlier error. Eleven is therefore necessary, and the tree attains it. Costs count reads, not laboratory apparatus or preparation time. Unknown and externally calibrated physics are not rejected.

Run `python3 -m scripts.probe_link_rule_separation --answers ''` to get a first robust query; give the answer prefix to request the next one. Replay the [program, topology and ambient controls](probe_available_link_logic.py) and [minimum-cost panels](probe_link_rule_separation.py) with `python3 scripts/replay_primitive_probe_campaign.py --bundle bench_existential_link_comparison`.
