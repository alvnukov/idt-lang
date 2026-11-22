# What can one pulse and one detector explain?

Several different finite machines give an exclusive click with the same
six-setting probability row: **1, 3/4, 1/4, 0, 1/4, 3/4**. Matching the
row is a useful construction, not an identification of the underlying
machine. These tests change the preparation, combine controls, or count
resources while keeping the detector fixed. None supplies an experimental
confirmation of IDT, a universal proof or a new accepted primitive.

## From a local update to a relative phase

Follow-up: [which finite models can build the phase plate itself?](PHASE_REALIZATION.md)

The [local shuttle](probe_shuttle_local_reunions.py) has one bit visiting
four addressed cells. Reversal of three different visits is required to
give the same **entire** configuration, not merely the same position.
In the noncommuting branch the bit alternates, and a visit applies a cell
permutation or its inverse. A good starting point need not stay good
after moving the marker. The [Boolean cost test](probe_boolean_shuttle_origin.py)
asks what it takes to introduce a period divisible by three: affine
wiring alone forces the fourth power of the permutation to be the identity;
one scalar AND still forces the eighth power to be the identity. Two
Toffolis per addressed update suffice. This counts nonlinear gates with
separate fixed encodings of bit and cell, and no extra persistent memory.
It is not an encoding-independent minimum cost for Nature.

The [joint relay](probe_joint_relay_phase.py) realizes the nominated
short-path echoes and an actual pulse of order six on 216 sites. Its size
bound requires two different roles and a finite abelian endpoint quotient
with all four port labels permutable. The analyzer reads a **difference**
between cells; a predicate on one absolute cell label that distinguishes
antipodes is not even well-defined on that quotient. Both relay controls
pass the two individual pulse calibrations. A held-out commutator then
gives 1 for the base relay, 3/4 with an extra transported bit, and 29/32
for independently specified orthogonal 60-degree rotations. Those are
three calculated values, not observations. Adding the bit preserves the
endpoint tests, not the full-state reversal assumption.

## One click, a wave-like row, and the operation still supplied

In the [six-mark model](probe_six_mark_phase_origin.py), a three-mark
incidence window, a cyclic pulse and two fair skip-or-step choices give
the row by counting four histories. For this pulse and detector the full
row fixes their relative stock to 1:2:1; it does **not** fix the microscopic
sampling history. A two-site construction can realize the row without
switching the elementary scattering law. The choice and timing of the
program remain inputs.

The [exclusive-packet model](probe_six_phase_exclusive_packet.py) puts
one occupation on two arms, but gives **both occupied and empty cells**
a tag. The same reversible interaction splits and recombines the packet;
applying it twice swaps cells and serves as a shutter against a prepared
vacancy. The check enumerates 995,328 ordinary histories over settings,
preparations, shutters and independent dump tags. Both arms open give
the six-setting row. With either arm closed the (left, right, lost) shares
per emission are (1/4, 1/4, 1/2); closing both loses every emission.
Randomizing the empty arm's tag by an independent antipodal shift destroys
the fringe. The phase plates themselves are **supplied**. For this
particular full interaction, a conserved tag count forbids a clean
one-step plate with exactly restored auxiliary cells. This does not rule
out other reversible interactions or consumable phase references.

This mechanism has a relevant precedent: [Catani, Leifer, Schmid and
Spekkens](https://quantum-journal.org/papers/q-2023-09-25-1119/) gave a toy
field theory with a discrete occupation and phase on each mode, including
an empty mode. Its treatment of interference is a reason **not** to count
the mere coexistence of a wave-like row and one click as a uniquely
quantum signature. Their model is not the gate table enumerated here.

| Question asked of the same visible row | Finite result | What the comparison assumes |
| --- | --- | --- |
| Can two separated readers reproduce the static probability table? | [Three forward symbols suffice, two do not](probe_local_phase_comparator.py); six are needed to read the exact microscopic comparison. | Independent inputs, input-independent shared randomness, one directed message, every trial counted. |
| Can a bounded classical register carry a sequence of settings? | [Five independent six-position dials exclude at most four symbols at the ideal score](probe_serial_phase_memory.py); [eight exclude at most five](probe_six_mark_phase_origin.py). | No setting-dependent memory bypasses the cut; null and double events count as zero in the signed score. These are thresholds, not measured violations. |
| Do two individually calibrated pulses represent different axes? | In the [paired-pulse test](probe_phase_pair_holdout.py) all 192 retained station pairs act as the same pulse or its inverse on all twelve joint states. | Specific transparent station library and unchanged preparation/readout. Failure to reach an independent calibration is not a failed prediction of its subsequent holdout. |

For a historical comparator, [Trojek et al.](https://arxiv.org/abs/quant-ph/0502066)
used sequential single-qubit communication in a different five-party task.
Its continuous correlated setting distribution and one-bit comparison are
not experimental tests of the discrete four- or five-symbol bounds above.

## What five occupied-or-vacant slots do **not** determine

* [Exchange signs](probe_occupation_square_signs.py): hard-core occupancy
  already forbids double filling. It does not choose the relative sign of
  two orders of toggling. Even requiring odd signs on all ten empty-start
  squares leaves 32 inequivalent extensions with three-plus-two slot
  symmetry. A bit that records a loop sign is not a coherent exchange
  experiment. Compare the explicit *assumption* of odd dashing in the
  mathematical [cubical construction of Doran, Iga and Landweber](https://doi.org/10.4171/AIHPD/43).
* [Chiral charge conditions](probe_packet_charge_pairings.py): given the
  usual six one-family multiplets, including a singlet neutrino, the local
  anomaly equations do not pick the observed hypercharges. All four
  conventional Yukawa links still leave a universal extra charge
  direction; a bare neutral Majorana pairing would be a further input.
  This reproduces a known ambiguity; see [Babu and Mohapatra](https://doi.org/10.1103/PhysRevD.41.271).
* [Direct neutron-charge anchor](probe_neutron_charge_anchor.py): on the
  specified integer charge plane the proton and electron cancel even on
  nonstandard branches. With an independently fixed scalar character
  of three, the alternatives have a neutron charge magnitude of at least
  3/4 of the electron charge magnitude, far from the [free-neutron
  measurement](https://doi.org/10.1103/PhysRevD.37.3107). With only the
  global quotient fixed, explicit alternatives approach zero arbitrarily
  closely. A finite experimental uncertainty cannot choose the exact
  character in that larger family.
* [Flavor connectivity](probe_flavor_charge_connectivity.py): the observed
  muon-to-electron and muon-to-tau appearance channels
  ([T2K](https://doi.org/10.1103/PhysRevLett.112.061802),
  [OPERA](https://doi.org/10.1103/PhysRevLett.115.121802)) connect all
  three active flavors. If these flavors have definite charges and the
  propagation environment cannot exchange that charge, the three charges
  coincide. An explicit globally conserving environment can evade the
  implication by taking up the difference. The two measurements concern
  different transitions; neither selects a universal charge shift.

Replay from the repository root:

```sh
python3 -B scripts/replay_primitive_probe_campaign.py --bundle local_shuttles
python3 -B scripts/replay_primitive_probe_campaign.py --bundle phase_memory
python3 -B scripts/replay_primitive_probe_campaign.py --bundle chiral_observations
```
