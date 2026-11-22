# What happens after the first click?

An apparatus can give the right probability of one click and still make
the wrong prediction for the next click. Here the first bit stays in a
physical register and every outcome is counted. The comparison is to a
**specified** repeatable, rank-one projective instrument at six coplanar
settings, not to every physical detector with these one-click rates.
All figures below are exact finite model results, not measured frequencies.

## One contact rule can write a record and prepare an output

Start with five tags and three addressed wires. Two wires interact; a
third is an unchanged spectator. If its tag equals the midpoint of the
other two in arithmetic modulo five, use the old binary affine pulse;
otherwise use its inverse. Applying the new rule twice exchanges the
targets. It conserves their sum, and renaming all tags by the same
invertible affine change does not change the rule.

The [literal instrument](probe_midpoint_spectator_instrument.py) uses
this one rule for the signal, memory and actuator. A sequence of five
spectators recovers the old unconditional binary pulse. Two contacts can
exchange a pair of complementary tags conditional on a reference match.
Two such comparisons, with separate unused tokens, implement an OR:
a second hit does not erase the first. Its bit controls which of two
opposite preparations goes forward. Nothing reads a bit in order to
choose the external address sequence.

| Resource or control | Checked result |
| --- | --- |
| Initial stock | One defect and 47 blank wires prepare a 17-wire kit in 40 contacts; the unselected wires are not reset. A second complete kit can also be prepared starting with one defect, using 98 blanks and 84 contacts total. |
| Reading and changing the signal | 52 contacts write the original two-visit bit and restore the input triple. Preparing the opposite seed takes 60, conditional switching takes 6. The new signal leaves on **different wires**. Two independent fair skip/step choices supply its spread. |
| Every input and frame | On 125 triples and all 20 distinct background/defect choices the exact bit and all four conditional output tickets agree. All 11,520 two-record histories give the prescribed joint table; neither click was inferred from the first. |
| Two separated copies | With fresh independent settings, shared classical stock and **no inter-device message**, the absolute CHSH score is at most 2. The supplied singlet prediction at the selected six-direction settings is 5/2. A sequential wire between detectors is not a Bell experiment. |

The [rule census](probe_midpoint_rule_origins.py) shows just how much was
assumed. Keep the spectator and equal targets fixed, require affine tag
covariance and a square equal to target swap: there are 16 rules. Sum
conservation leaves four; two ignore the spectator and the other two are
the midpoint rule and its inverse. Replacing affine structure with complete
interchangeability of five tags leaves **no** such rule. The original
assumptions, including five tags with affine structure, are not inferred
from the measured world. The same primitive implements an ordinary
reversible controlled swap on two bits in six contacts with restored
helpers. Programming a good detector is not explaining why this detector,
its clock, or the independent fair sources would form.

## Why a correct one-click row or an unread sequence is too weak

In the [old five-tag model](PHASE_REALIZATION.md), copying the bit without
changing the signal gives an unread second-click probability of 1 in one
return experiment instead of 5/8. A fair choice of doing nothing or
reflecting the six states is much more convincing: it is repeatable and
matches **all 36 unread rates**. Keeping both records exposes 1/8 instead
of 1/16 for one joint event.

The [six-state check](probe_affine_unread_instruments.py) gives sharp
minimax discrepancies for a common positive channel whose rows and columns
all sum to one: **1/16 for joint rates and 1/12 for conditional rates**.
These are two different optimizations; they are not uncertainty intervals.
To reproduce the entire sequential table *on this six-state code*, the
postchannel must reset within each outcome sector to a 1:2:1 distribution.
A reversible swap with a fresh three-valued stock does this but consumes
that resource. It is not an old binary-contact program.

If poststates may occupy any of the **125** triples, six dial settings
cannot simply be assumed to identify their distribution. A stronger
[operational test](probe_affine_projective_reset.py) compares the desired
outgoing preparations using all 480 native analyzer maps. These give 240
distinct effects; with normalization their rank is 30 on 32 scale classes,
**not** full tomography. Positivity nevertheless pins these particular
bright and dark stocks. Of 1,953,125 affine maps on the input plane only
24 preserve both required supports. Every independent mixture gives a
sum of middle-bright probabilities of 1 where the reset requires 3/2.
This excludes a prescribed observer-independent mixture of affine color
maps for the **extended** comparison, not for arbitrary smaller sets of
analyzers. Correlated ancillas, feedback, or different primitives are not
covered.

## Other candidates kept, including failures

* [Separate memory](probe_affine_contact_record.py): five colors with four
  memory labels support an actual bit. A [full-space test](probe_full_affine_record.py)
  finds the original 17-contact record differs from the intended detector
  on 32 of 125 raw triples, though they agree on the six calibration
  states. Two actual programs of 33 and 36 contacts record the intended
  bit on all inputs and in every background frame; scratch is not reset.
  In this candidate the memory does not drive the subsequent colors.
* [Mixtures](probe_affine_preparation_mixtures.py): three equal mixtures
  of nominally opposite preparations all read 1/2 on the six dials.
  A single right contact splits them into 4, 3, 5 out of eight. A separate
  wire-swap difference of 1/8 persists under every nonnegative common
  stock on the full carrier preserving the exact solo fringe. This is
  a failure of an operational equivalence, not a contextuality violation.
* [Which controls are accessible?](probe_affine_operational_library.py)
  Only five subgroups containing the clock keep the three mixtures equal.
  Requiring the common rate to stay 1/2 leaves two, of orders 6 and 12.
  The latter has noncommuting operations but adds no new detector row
  on the original preparations. Allowing elementary contact prefixes
  changes the apparatus.
* [Fourth axis](probe_affine_fourth_axis.py): given three named old axes,
  one old stock and a single ordinary rotation per pole, the best
  deterministic fourth axis misses the supplied 32-cell ideal by 1/4.
  An independently randomized analyzer reduces this to 7/71 (1/12 with
  component-wise outcome flips). A different common four-ticket stock or
  a mixture for just one pole gives the whole **ideal** table exactly.
  A failure at the first interface is not grounds to discard the substrate.
* [Clock control](probe_alternating_catalyst_clock.py): the earlier
  [restored-reference program](PHASE_REALIZATION.md) does not supply
  its own scheduler. For the frozen 216 lifts, two reference wires, six
  placements and either starting edge, strict alternation at a common
  stopping time yields zero complete +1 operations. The exact period
  calculation covers arbitrary waiting time, not all clocks.

Replay all ten probes:

```sh
python3 -B scripts/replay_primitive_probe_campaign.py --bundle instrument_realization
```
