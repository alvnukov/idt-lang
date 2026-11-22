# When the phase plate is a program, not an instruction

Two finite mechanisms now produce an actual operation. In an apparatus with
one occupation on two arms, the same local collision can be programmed to
shift an unknown tag whether its cell is empty or occupied. In a smaller
model without an occupation bit, four collisions on three cells produce a
six-beat process. Neither derives a probability law, a clock or an observer.

## One reversible apparatus, many ways to carry the hidden tag

The earlier [packet](OPPOSITION_PROCESS_RESULTS.md) sends one occupation to
one of two detectors. Independent phase settings on **both** arms give its
six-position row. Keep its preparation, shutter and raw completion outside
the active mixed sector, but vary the update of the occupied and vacant tags
at a collision. Retaining common-origin covariance of this update, a relative
half-turn and two applications equal to wire swap gives [216
rules](probe_vacuum_phase_lifts.py). All reproduce the original counted
fringes and shutters with the stated stocks. They do **not** agree at every
preparation: a shutter supplied with one fixed reference instead of a uniform
one gives (left, right, lost) = (4, 0, 4) versus (0, 4, 4) for two rules,
without a plate or discarded emission. Seven fixed-reference settings
distinguish all 216 when both documented source preparations are available.

| What must implement the step +1? | Result |
| --- | --- |
| Any finite stock of exactly restored helper cells; a different program for each **known input** | [Integer tag-count changes](probe_catalytic_tag_invariants.py) classify all twelve inputs for each rule. For 192 rules every input is reachable; for 24 only four are. All 2,400 reachable rule/input pairs have replays restoring the original helper wires and tags. |
| One occupied and one vacant helper, with one fixed program for an **unknown input** | [Three-cell search](probe_catalytic_six_phase_words.py): for 160 rules a stock and a common program work on all twelve inputs. For each of the other 56, even the best stock makes only four of the twelve inputs individually reachable. This does not exclude more helpers. |

For example, free increments (1, 1, 5) and raw helper labels (8, 0) admit
a program of 740,471 elementary pulses. Both a compressed verification and
literal pulse-by-pulse execution restore the helpers. The same program works
on zero of twelve inputs for the specified wrong-stock and old-rule controls.
This is an existence witness, **not** a shortest program. It removes the
separate plate instruction on the logical code but supplies stocks,
addresses, timing, preparation and the occupation detector.

## What five tags can do instead

The [five-tag rule](probe_affine_contact_fringe.py) respects every common
affine relabeling of its tags and squares to wire swap. Denote the two
neighbor contacts on three cells by A and B. ABAB has period six on **all
120 nonuniform triples** and fixes the five uniform ones. No shorter
positive word on those contacts has a six-cycle.

Put one defect in the middle of uniform stock, keep a background reference,
and allow two fair skip-or-step choices. A fixed reader asks whether the
first cell equals the reference now or after one reverse step. The resulting
six-setting bright counts are (4, 3, 1, 0, 1, 3) out of four. All 20 unequal
background/defect choices agree. The earlier end-defect/last-cell reader
fails and is retained. After three steps the isolated triple is merely a
global reflection of its starting frame: without a reference, a
relabeling-invariant reader cannot see the antipodes. Nor can the affine
rule alone write a nonconstant binary answer on any output wire on this
orbit. The comparison event, its record and fair choices remain supplied.

The [paired-pulse census](probe_affine_pulse_holdouts.py) tries all 20
native order-six maps on the same preparation and reader. Only the first
pulse and its inverse retain the full solo calibration. Two noncommuting
maps look successful on a calibration and first mixed test if their failed
single-pulse rows are ignored. No independently calibrated second axis
was obtained.

The [frame test](probe_phase_frame_covariance.py) asks a different question:
an *individual* tag must have an actual six-cycle, not a pattern across
three tags. A homogeneous gate on two cells that squares to swap and respects
this raw frame needs at least twelve tags; two six-cycles suffice. If in
addition every tag is related to every other by a symmetry, [thirteen
suffice and are minimal](probe_transitive_phase_tags.py). The selected clock
then has a fixed tag although the collision does not prefer it. If **every**
tag must have period six, transitivity instead requires at least 48; both
abelian and nonabelian examples attain it. The general bounds are written
algebraic arguments with checked finite examples, not registered universal
proofs. They concern a homogeneous gate, not a physical minimum.

Follow-up: [what happens to the signal after its first click?](INSTRUMENT_REALIZATION.md)

## Independent controls

* [Point contacts](probe_native_phase_contacts.py): on the separate 216-site
  relay, three calibrated contacts work on one orbit but give six zeros on
  each of the other seventeen, even when the move preserves phase. With a
  programmed marker, an equality comparison and a latch, 54 comparisons
  are necessary and sufficient on all 108 candidate positions under that
  access contract, not for arbitrary detectors.
* [Serial trial witness](probe_serial_trial_witness.py): count all heralds,
  including losses and double events. A shared seed carrying the sum can
  fake the score even when the observed setting words are uniformly
  distributed. The test requires settings fresh against the apparatus or a
  justified conditional bound on their errors. Design examples are
  hypothetical; none is a measured exclusion.
* [Scalar channels](probe_finite_scalar_channels.py): on one parity-even
  occupation carrier, there are four color-singlet weak-doublet operator
  copies. Requiring the scalar to be one of these operators, with the
  stated chiral charges, selects a neutral neutron under the specified
  charge assumptions. A Lorentz-scalar pair of two left-handed fields on
  the same representations admits the scalar charge without that
  restriction. Neutrality does not identify the scalar carrier.

Run the quick comparison from the repository root:

```sh
python3 -B scripts/replay_primitive_probe_campaign.py --bundle phase_realization
```

Quick mode checks one literal common program and all single-input orbits.
To reconstruct and replay a common program for **each of the 160** positives:

```sh
python3 -B -O -m scripts.probe_catalytic_six_phase_words --joint-census
```
