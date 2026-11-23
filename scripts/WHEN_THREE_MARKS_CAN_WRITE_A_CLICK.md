# Three marks can route a signal and write an ordinary record

The same reversible contact on two unnamed ends suffices for both jobs in a programmed finite apparatus. Its entire rule is

    aa ↔ bb       Ta ↔ aT       all other ordered pairs fixed.

Here a and b are ordinary shades. The single T at launch is conserved; no contact asks whether a detector should fire. This removes a fourth local state from these tests. It neither makes the initial T from vacuum nor selects a schedule, a source distribution, or a permanently sealed detector.

## First try: a dye which moves but cannot write

On the [three-label vacancy switch](probe_ternary_vacancy_switch.py), exchange any mark with an empty site V; on two occupied sites do nothing. With occupied data ends A,B and a third site C, the fixed contacts AC, AB, BC exchange the data marks **if C is vacant**, restoring C. Using a control from each arm gives an exchange when just one is vacant. A plate exchanges the two cells of a complementary V/N stock. Shutters physically dump and refill; losses count as outcomes.

This passes all 32 two-arm settings in 512 reversible launches. On the three programmed networks it agrees with the [four-label compensated switch](WHEN_THREE_PORTS_REMEMBER.md) on the prepared operating code at all 192 intermediate hubs. But a meter reading only vacancy versus occupation sees **identical histories** when the source dye is exchanged for an ordinary mark in the same position. Project any contact to its two occupancy bits: they just swap, regardless of the dye. Appending clean sites and composing any fixed word cannot change that. Reading the dye itself is an extra ability; passing a port-count table hid this missing detector.

## An active three-label alternative

The [active contact above](probe_ternary_active_readout.py) has a different ordinary sector. On a triangle with a reusable prepared a, nine physical contacts implement the vacancy exchange for **all nine** data pairs while restoring the helper. A meter with data x, two ordinary records b,b and helper a takes five contacts:

| Input x | Final data | Final ordinary records | Final helper |
| --- | --- | --- | --- |
| a or b | original x | b,b | a |
| T | T | a,a | a |

The T temporarily enters the helper but never visits either record. This is a concrete way to read the tag using ordinary shades. All 512 two-arm launches, 1,024 full-apparatus controls without a token and 72 three-port launches are checked. The two-arm apparatus uses 25 sites and at most 290 physical contacts; the three-port apparatus uses 16 and at most 177. Among the 24 anonymous, token-number-preserving ternary pair involutions, eight make token movement depend on which shade it meets. This is a search class, not a uniqueness result for the displayed law. The component word lengths are minimal only for their stated hardware, stocks and endpoint contracts.

The [four-label detector](probe_native_mobile_detector.py) remains in the history. With a fixed-zero reference, six contacts transfer the input to a holding cell and set an ordinary flag iff the input was the token. The flags match all 512 original switch runs, including dumps; every trace reverses. Reusing an exposed holding token in fresh meters can write **several** flags. Dirty record or holding stock produces false positives and misses. One conserved token therefore does not imply exactly one irreversible click: record isolation or an event grouping is still needed in either construction.

Is an odd cycle in the hardware doing essential work? The [tree implementation](probe_ternary_tree_hardware.py) replaces the triangle: two data leaves, a central a and a third leaf b implement the same clean vacancy contact in 15 scheduled steps. A four-site path writes the two protected records in ten. Combining them on one shared hub leaves the *entire* installed apparatus a tree: 26 sites and up to 490 contacts for the shutter test, 17 and up to 300 for the three-port test. That tree installs 16 edges but offers only 13 in these runs; three stock-partner leaves remain idle. All 192 intermediate hub states still match. A four-site line can perform the individual clean exchange in 19 contacts for two stated stocks; that does **not** place the full apparatus on a line.

There is a cost hidden by simply counting labels. On any bipartite carrier the number of b sites on one side minus the number on the other is conserved by every active contact. Two b→a records with the rest restored must therefore sit on opposite sides. A clean exchange of a and b across opposite sides with all helpers restored is impossible; the logical data homes in the tree construction lie on the same side. The supplied tree and clock do real work.

## Would two marks suffice?

It depends on the arity and the readout. The [binary pair control](probe_binary_pair_switch_wall.py) enumerates all 24 reversible maps on two bits; even with oriented inputs, each is affine over binary arithmetic. In any fixed circuit, independently varying a source block and a control block gives even parity across the four corners at every raw output bit. A clean switch must put a signal at the cross output precisely when the source is present **and** the gate is open: that has odd parity. If the raw output retains distinct clean codewords for the two answers, at least one output coordinate witnesses the discrepancy. Arbitrary shared, setting-independent mixtures of affine truth tables have worst-cell error at least 1/4, attainable on that bit; for a fixed profile with just a random common offset the bound is 1/2.

This test needs the vacuum. Two oriented controlled flips reproduce the switch for either one-token input but produce both output flags from vacuum when the gate is open. The four endpoint-symmetric reversible binary pair laws also preserve Hamming distance; with the raw input retained, they cannot additionally write distinguishing bits on disjoint fresh records. Consuming the input or supplying a nonlinear external reader changes the problem. Three *addressed three-site* operations of the form “flip the target if either neighbor is set,” using a zero reference, can implement a reversible controlled-controlled flip. Hence the exclusion concerns reversible **pair** operations and a particular clean readout, not binary primitives in general. No equivalence to an autonomous Rule 54 lattice follows.
