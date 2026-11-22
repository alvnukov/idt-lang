# Contacts, composite stocks and a detector that returns one register

This cluster asks which assumptions can be removed from the [unsigned-graph
and stock candidates](TRANSFER_AND_STOCK.md). It does not add an axiom to IDT,
derive the physical Born rule, or report new experimental data. A *stock* is
a nonnegative number assigned to a packet before normalization; a *rail* is
a distinguishable channel, not a direction assumed to exist in space.

Replay all eight finite checks:

```sh
python3 -B -m scripts.replay_primitive_probe_campaign --bundle contacts_and_local_readout
```

The scripts separate the conditional arguments on an integer lattice from the
finite examples the computer actually evaluates. None is a Lean proof.

## Can repeatable contacts and stock constrain one another?

On neutral integer triples, suppose two nonzero additive outputs annihilate
one another on repetition in opposite order, neither repeated same output
vanishes identically, and each raw dark line is invariant under the chosen
rail swap. The two outputs must be integer multiples of the sum and the
difference of the input and its swapped copy. A blind detector can hide a
nonzero cross output: empirical repeatability alone does not give these
hypotheses. [Contact probe](probe_repeatable_triangle_contact.py).

Now require one common nonnegative, reversal-invariant stock, zero on zero,
and a positive input-independent total gain at each of the three contacts,
on **all** integer inputs. One bright median (a permutation or nonzero
multiple of the current triple `(2,-1,-1)`) selects a squared norm and equal
absolute output multipliers within each setting. A uniform duplication of
both outputs is invisible after normalization: absolute gain four would
need its own measurement. Without the bright median there is a genuine
modulo-three competitor, not a failed numerical approximation.

A fourth initially empty rail changes the result. An additional exchange
can connect the dark candidate's median to an edge it must count as bright.
For canonical contacts on four or more neutral rails, merging two entries is
enough to fix the nonzero stock to a constant times the sum of squares.
For even stock, connected available swaps suffice; conjugating the equation
does not physically install extra devices. [Idle-rail probe](probe_fourth_rail_stock.py).
A variant allows an unknown additive plus map that kills the exchanged edge
and a scaled canonical minus map: consistency of three-entry merges still
constrains even stock under the stated hypotheses, but a spectator
permutation can preserve the gain and stock with different output currents.
[Associative-merge probe](probe_associative_stock_merge.py).

## What changes when two systems meet?

Start with integer arrays with three rows and three columns and all row and
column sums zero. Supply paired addresses and local contacts that can exchange
two rows or two columns. **Do not assume the stock factors on products.**
Every first local split has product children. If the same gain equation
applies to *all* parents, including nonproducts and scaled inputs, the
one-system restrictions fix the stock on products and then on every parent.
There are two nonzero possibilities: a squared norm or a modulo-three
indicator. Summing both remote branches gives the solo population fractions;
this does not assign a local outcome to any individual ticket.

Why test more than first-contact statistics? A rival squared norm plus a
squared minor agrees on every product and every normalized first local table.
A matched unmeasured bypass on the native antisymmetric input yields
`7/31` instead of `1/5`. A matrix representation, coherent pooling, the
gain law and the bypass are supplied. This does not derive tensor
composition. [Composite probe](probe_local_composite_stock.py).

## A counted event, a named register and an original vertex are different

- A three-register routing instrument sends each supplied ticket to exactly
  one register. On neutral packets its register fractions are the three
  squared currents divided by their sum of squares, conditional on the
  quadratic stock and uniform ticket sampling. An input-label shortcut
  mimics the histogram; tracing the routed tickets distinguishes it. Neither
  the sampling rule nor absorption of a physical photon follows.
  [Exclusive register](probe_exclusive_triangle_detector.py).
- In a generated unlabelled packet, even preserving its earlier port history
  leaves a symmetry exchanging two possible original vertices for a single
  survivor. Its *count* is fixed; a deterministic choice of its original
  address is not. Recording extra path identities changes which events cancel.
  [Original-address obstruction](probe_anonymous_click_addresses.py).
- The six square faces of a twelve-vertex local signal shell determine three
  opposite-face pairs without a chart. Transport in two examples exchanges
  the same pair of roles despite opposite spatial orientation; a coupled
  triangle reference can notice one such exchange but not a simultaneous one
  on both arms. Coupling roles to reference rails is an **input**; no spatial
  spin or physical phase follows. [Role transport](probe_angular_phase_reference.py).

## A prospective test with unequal detectors

Two candidate stocks predict branch weights proportional to `(14,12,16)`
and `(7,12,16)` on an off-ray bypass. Three cyclic assignments to three
stable detectors can cancel unknown per-detector efficiencies and per-wiring
flux at the level of expected counts. The script also supplies an exact
small-count conditional comparison under independent Poisson counts (or
fixed row totals and multinomial counts) rather than treating observed
products as noiseless. A branch-specific upstream loss of one half can still
make the competing laws identical. All example counts or margins are
synthetic. [Port calibration and loss control](probe_bypass_port_calibration.py).

The [seven source proposals](../data/primitive_contacts_readout_inventory.json)
retain the assumptions and countercontrols. Source retention does not bind
any proposal to a QM or Standard Model prediction adapter.
