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

### One localized carrier versus two information-carrying arms

Give Alice and Bob independent uniform bits `x,y` after the direction of
a single classical transmission has been fixed. Each must guess the other
input by the same deadline. Even arbitrary shared randomness independent of
the current inputs cannot raise the joint success chance above 1/2: the
upstream party has no information about the downstream bit. The downstream
party may know *both* bits. Enumerating those deterministic extreme cases,
in both directions, gives the following counts of wins on four input pairs:

```pycon
>>> from collections import Counter
>>> from itertools import product
>>> from scripts.probe_eight_label_interferometer import trial
>>> bit = range(2)
>>> inputs = tuple(product(bit, repeat=2))
>>> scores = Counter()
>>> for reverse, upstream, downstream in product(bit, product(bit, repeat=2), product(bit, repeat=4)):
...     wins = 0
...     for x, y in inputs:
...         a, b = (y, x) if reverse else (x, y)
...         wins += (upstream[a] == b and downstream[2*a+b] == a)
...     scores[wins] += 1
>>> sorted(scores.items())
[(0, 32), (1, 64), (2, 32)]

```

Now give the **existing positive eight-label** machine two independently
switchable plates, including its phase-carrying empty arm. Alice decodes only
from her input and left click, Bob only from his input and right click.
Both also need a common deadline, detector convention, and one counted
emission per trial; a no-click is not assumed to distinguish a loss in a
real apparatus. Below, the ideal closed accounting explicitly checks for
loss. An independent random bit flip on one plate is a dephasing *analogue*,
not a microscopic model of optical temporal mismatch.

```pycon
>>> def bilateral(noise):
...     wins = total = 0
...     for x, y, particle, vacant, n in product(bit, bit, bit, bit, noise):
...         left, right, lost = trial(0, particle, vacant, (0, 0),
...                                  (bool(x ^ n), bool(y)), (True, True))
...         if lost or left + right != 1:
...             raise ValueError("missing emission or ambiguous local output")
...         wins += ((x ^ left) == y and (y ^ right ^ 1) == x)
...         total += 1
...     return wins, total
>>> bilateral([0]), bilateral([0, 1])
((16, 16), (16, 32))

```

The test separates the direction-limited channel from an additional
information-carrying arm. It does **not** separate complex amplitudes
from this prepared positive model. In the optical protocol of
[Massa et al.](https://doi.org/10.1002/qute.201900050)
([author manuscript, Fig. 3 and Appendix C](https://arxiv.org/pdf/1802.05102)),
the reported fraction in the correct registered output was 0.961 ± 0.006
with high visibility and 0.498 ± 0.006 without temporal overlap. Errors
are standard errors across settings. The paper averages counts over 100
setting pairs, with multiple photon events per pair; this is not a
fresh-choice, per-emission test of the unconditional task above. Their
separate source-correlation check is not an independent replication.

Replay the examples: `python3 -B -m doctest scripts/HIDDEN_MODE_CANDIDATES.md`.
