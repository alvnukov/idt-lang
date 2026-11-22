# What can an empty arm carry?

Replay: `python3 -m unittest tests.test_shutter_candidate_probes`. These
are two deterministic, finite candidates with supplied preparations. The
rates below are per emission, including the runs lost to a shutter. The
earlier [separate-shutter controls](SHUTTER_CANDIDATE_PROBES.md) are unchanged.

| Open arms | Four labels: normal / reversed source | Eight labels: zero / one local plate |
| --- | --- | --- |
| Both | (0,1) / (1,0) | (0,1) / (1,0) for a left input |
| Either alone | (1/4,1/4) for either source | (1/4,1/4) for every plate setting |
| Neither | (0,0) | (0,0) |

### Source control is not a local phase plate

The [four-label certificates](probe_hidden_arm_certificates.py) use the
previous gate family, with eight distinct tables for the fixed weight
assignment. They change the visible object: now it is an extreme-weight
label L or H; the two middle labels X and Y are invisible at readout.
Exactly one extreme is supplied on the two arms at input. Its position,
its species and the otherwise invisible label follow an explicit four-case
source distribution. A closed arm swaps with a separate X dump. The same
recombiner word is used for **all** masks and both sources for its table.
On six tables the listed words return the third cell to X, keep a vacuum
silent and produce the indicated detector counts. The shortest *listed*
word has length 40; the search did not certify a minimum.

On the other two tables, a checked bijection relates the two 15-state
weight sectors and commutes with both allowed adjacent moves. Four distinct
required inputs would have to fit into three allowed outputs of a
permutation. Thus no word of any length solves this **specified clean
three-cell problem** there. Neither these tables nor the four-label
family are rejected as physical primitives.

A clean local operation conserving this weight and returning all its
auxiliaries cannot change L or H: each is the sole label at its weight.
Thus acting on one arm leaves at least half the fair trials unchanged.
Switching the source's correlation reverses the fringe, but is not an
operation inserted independently in one arm.

### A native local plate with eight labels

The [eight-label candidate](probe_eight_label_interferometer.py) gives
each cell an occupation (0 or 1) and one of four colors. One reversible
two-cell table T conserves total occupation, fixes equal pairs and squares
to the swap. A six-use word of that very table, with two ready vacuum
references, toggles a phase bit for both occupied and empty logical cells
and restores both references. This is checked on the operating labels
0,1,4,5; it is not a universal bit flip on the eight labels.

Apply T to split, insert the same plate on neither, either or both arms,
swap each closed arm into its own dump with T², then apply T to recombine.
The detector just reads occupation. With both arms open, two plates restore
the zero-plate **output port**; the two cases are not claimed to be the
same raw operation. With one arm open half the emissions are absorbed,
with the survivor split evenly. The input particle phase may be fixed.
Fair input-vacancy phases, appropriate dump phases, ready references,
and the occupation readout are supplied resources. Copying the closed
arm's old phase into its replacement in the control breaks the single-arm
balance. The fixture uses independent fresh dump phases, not a proof that
mutual independence of the two dumps is necessary.

Eight is minimal only in this class: binary additive occupation, T² equal
to the raw swap, at least two distinct labels in **each** occupation
class. The swap on each total-occupation sector must be an even
permutation. Its transposition counts are C(d₀,2), d₀d₁, C(d₁,2), where
dᵢ counts labels of occupation i. A different valid eight-label table
with the same mixed-occupation rule conserves the XOR of vacant phases.
That invariant forbids a clean vacuum phase flip with all other cells
restored: the raw square and occupation rules do not force the plate.

This is a two-setting, one-particle comparison. Neither a phase continuum,
a measurement instrument, entanglement nor exchange statistics follows.
There is prior work on the broad idea of definite occupation plus a phase
of empty modes; see [Catani et al.](https://arxiv.org/abs/2111.13727).
The finite gate certificates here are not experimental evidence for that
model or for IDT.
