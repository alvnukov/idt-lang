# When a colorless token reads two arms

Can a single token respond to settings in both arms without carrying a phase label of its own? **In a programmed finite circuit, yes.** The same [four-label contact](WHAT_CAN_AN_EMPTY_ARM_REMEMBER.md) that writes correlations before a particle is present gives a reciprocal splitter and reader. The role of the apparently empty arm becomes visible when one changes the closure or the distance to the reader.

### One rule, two cells per arm

Write • for the only occupied label. The contact exchanges 01↔02, 10↔20 and •1↔1•; all other ordered pairs are fixed. Each arm has two cells D,E and a zero reference. Two configurations of the occupied arm, (•,2) and (1,•), represent bits 0 and 1. On the vacant arm they are (1,1) and (1,2). No bit value is consulted to decide which contact fires.

Let A contact D with E, Z contact the zero with E, and C contact the two arms' E cells. Inside one arm, P=A Z A toggles either bit without changing which arm is occupied. In a symmetric layer both independent arm contacts can fire. The analyzer applies C, then P on both arms, then C, then A on both arms, in chronological order. A central C flips the occupied arm precisely for occupied bit 1 and vacant bit 0. Between the two C contacts both bits complement, so their net routing change is their XOR; final A puts the token at the D detector. The splitter is the exact inverse of this same word. It starts with a token at the chosen D, the other D at 1, and two independent fair E shades, 1 or 2. This produces balanced arm occupancy without a separate path coin. With no late intervention, the analyzer restores the entire source state.

| Late operation | Raw outcome over independent source and shutter stock |
| --- | --- |
| Both arms open | Exactly one hit at input port XOR left plate XOR right plate |
| Only one arm open | Left 1/4, right 1/4, dedicated dump 1/2 |
| Both closed | Dedicated dumps 1 |

To close an arm, first apply A locally, then contact D with a fresh 1 dump and E with a fresh fair 0-or-2 mask. Neither auxiliary is brought back into the analyzer. The [raw replay](probe_colorless_packet_arms.py) checks the conserved token throughout all 512 launches, for both input ports, all plate and shutter settings. After one fixed exchange of detector names, all 32 averaged rows agree with the [eight-label comparator](probe_eight_label_interferometer.py).

**What distinguishes them:** freeze the mask of the closed arm and toggle its late plate. In the four-label circuit the surviving half of the original launches switches ports: (1/2,0,1/2) becomes (0,1/2,1/2), or vice versa. The mask randomizes the old bit in the averaged table; it does not replace the old state. The eight-label shutter actually exchanges the whole incoming label for a prepared vacant label and isolates the former. Its output is insensitive to that closed-arm setting at fixed replacement stock.

One uncolored occupied label therefore need not forbid a two-setting response: two local cells can encode a bit in a *position*. This does not select the rule in nature. The topology, time order of the offers, source and shutter stocks, definitions of arms, and occupation meter are supplied. Two binary settings do not derive a continuously variable optical phase, the Born rule, or statistics of identical particles.

### Put a real gap after the setting

The two interacting E cells originally touch. Now put each D and E on its own lane. A hop contacts the cell with a fresh 1 at the next site. A token moves forward with certainty; two blank shades 1 and 2 leave a fresh destination at 1. At the far end of each nonempty group of hops, a contact with zero at E restores *both occupied encodings exactly*; both vacant encodings arrive as (1,2). No absorber or missing click explains the loss of the vacant-arm distinction. For the eight-label comparison, two contacts per hop transport the actual raw cell by exchanging it with its neighbor. These are explicitly different transfer operations on the two candidate laws.

Use h hops before the plate and g hops between the plate/shutter and the analyzer. For h,g independently 0, 1 or 2, count every launch on either input. For the four-label device, any nonzero total gap produces 1/2:1/2 with both arms open. **That average alone cannot locate the failure.** In a simulator one can replay the same initial raw stock, toggling only the plate on the arm found to have been vacant. When g=0 this changes the click in all 128 directed open-arm comparisons at each h, even when a positive upstream gap has washed out the ensemble fringe. When g>0 it changes none. The old shade can still be present in the retired writer cell: it was not transported. The eight-label device retains its zero-gap response seed by seed. With either one shutter closed, both devices still give (1/4,1/4,1/2). An actual experiment with unavailable microscopic seeds cannot just perform these paired simulated readings.

This limitation is not peculiar to a one-edge transfer. In a token-free region the zero positions are fixed. Every other cell flips its own shade once per offered contact with a zero. Therefore two trials that initially differ only in a written 1/2 shade, with the same zero pattern and the same subsequent sequence of contacts, cannot move that difference to a different blank site. Moving the detector token itself to the remote setting and back does work in a separate control. An adaptive address schedule, extra moving signals, or a changed zero pattern is outside this restriction. [Unconditioned separated-arm replay, matched controls and active return bus](probe_separated_empty_arm_transport.py).

### What happens if the final sequence is not programmed?

Keep the open-arm preparation and plates, but replace only the analyzer by random contacts on its five undirected edges. Count a launch as correct if its token is anywhere on the target arm; also record each of the four physical sites separately. The prepared ensembles occupy part of a 12-state orbit. Exact transition probabilities give:

| Final contact selection | Highest correct-arm probability | When attained |
| --- | --- | --- |
| Independent uniform attempted edge; idle attempts count | 11/20 | After 1 or 2 attempts |
| Uniform among currently enabled edges | 7/12 | After 1 active event |
| Independent uniform permutation of all five edges per sweep | 1297/2304 | After 2 complete sweeps |

The peak bounds cover **all whole ticks of the stated clock**: check the early ticks exactly, then bound every later tick by total-variation distance from a symmetric stationary law. For sweeps these are complete-sweep boundaries; intermediate individual contacts can exceed the tabulated value. Stationarity alone does not imply monotone relaxation. Grouping D and E is significant: after one random attempt for a left target the four site masses (left D, left E, right D, right E) are (3/10,1/4,3/10,3/20). The original D detectors tie; 2/5 remains on E. This is a small, clock-dependent transient on a prepared circuit, not an autonomous optical measurement. [Exact clock comparison](probe_undriven_colorless_analyzer.py).

Replay all three source probes with `python3 scripts/replay_primitive_probe_campaign.py --bundle bench_colorless_arm_comparison`.
