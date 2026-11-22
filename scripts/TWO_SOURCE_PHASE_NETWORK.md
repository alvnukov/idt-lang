# A test of how separately prepared systems share a phase convention

Integer coordinates by themselves say nothing about this question. A
two-integer phase register with quarter turn J can be treated either as a
real plane or as a single complex line. The rule for composing **two**
registers is additional physical information. Three probes separate that
choice, a finite network it permits, and what actual trial records would
be needed to test it.

## A finite native network, not a fit

Supply two independent encoded Bell pairs, the usual complex tensor rule,
addressed paired-rail gates, and a normalized squared-amplitude readout.
Alice uses three settings, Bob measures one complete Bell basis, Charlie
has six settings. For Charlie an initially blank **third logical path**
completes the normalized column (3+2i,1+i,1)/4. One output counts as plus;
both remaining outputs count as minus. There is no acceptance filter.
All source preparations, local analyzers and the middle measurement have
finite native words. This is conditional circuit synthesis, not an origin
of product structure, locality, preparation or Born probabilities.

With all 18 pairs of settings and all 288 output cells retained, the
[compiled example](probe_two_source_phase_network.py) has **T=63/8=7.875**
on the precise 12-term, four-Bell-outcome functional of
[Renou et al.](https://arxiv.org/abs/2101.10873). The authors report a real
independent-source upper bound of 7.6605; our code imports that number, not
their SDP certificate. Merely deleting all imaginary components gives
T=43/8. Among single-output axes with denominator (1+i)^k and one spare
path, the first sufficient k in this restricted exhaustive search is 4.
With no spare the corresponding face score stays six. A simultaneous
per-active-setting total-variation error below 143/16000 is sufficient
to keep the example above the reported bound; this is not measured noise.

The complete distribution is invariant under simultaneous conjugation
of the two ends, because the sources and Bob's measurement are real in
the specified basis. Conjugating just one end gives **T=23/8**. For a
settings-independent probability h that the two phase orientations disagree,
T=63/8−5h; the same comparison needs h<0.0429. This sign is a physical
misalignment in the example, not an arbitrary change of notation and not
a bound on orientation errors in any existing experiment.

## Ordinary tensor product versus a balanced phase rule

Write A=J⊗I, B=I⊗J. In the ordinary real product, K=AB is a symmetric
involution. Both K=+1 and K=−1 sectors exist. Requiring that a phase turn on
either factor mean the same thing imposes A=B, hence K=−1. This is a
quotient rule, not the result of measuring K and silently discarding half
the records. In fact a normalized real product puts exactly half its weight
in each sector.

The [composition check](probe_balanced_phase_composition.py) also operates
before any real scalars are introduced. In the two-register integer basis
the balanced quotient map is (a,b,c,d)↦(a−d,b+c), with image all of ℤ².
The minus-sector **sublattice** instead maps to 2ℤ², of index four.
Oriented edges in a network can identify neighboring quarter turns up to a
sign. A product of minus signs around an inconsistent loop leaves no real
sector, while the corresponding integral quotient can have two-torsion.
These are distinct statements, not just coordinate conventions.

An ordinary real-separable reference, even a classical mixture of products,
has zero expectation of K. A supplied real *entangled* reference (I−K)/4
has expectation −1. Two independent sources of such real reference pairs
do not furnish one global reference for free: the two middle measurement
branches leave opposite outer sectors, and retaining both gives I/4.
The real-model comparison in the cited paper allows shared classical
information but not a freely shared entangled source between source factors.

## What can actually be checked

[Chen et al.](https://arxiv.org/abs/2103.08123) report 8.09(1) for the
three-axis/six-axis functional on a four-qubit superconducting processor.
They report a 12×16 probability table on the **active** settings, different
analyzers from our finite word, and discuss readout correction. The six
inactive setting pairs contribute zero to the aggregate T. A published
aggregate is not a chronological file of raw trials. The author archive
inspected did not supply trial order, original per-setting counts or a
verified independent setting schedule. We do **not** claim to have
replayed this score, its reported significance, or a new test of the
integer model. Our result is a compatibility example with supplied
complex composition, not an experimental success of IDT.

The [prospective raw-trial checker](probe_phase_network_game.py) uses a
different data contract: fresh uniform independent x and z on **all** 18
pairs, every output retained, no post-setting herald, and applicability
of the real source model conditional on **each past history**. In 12 settings
the signed score is ±1; in the other six it is zero, with the trial still
recorded. Under a supplied valid upper bound B, the conditional chance of
a win on an active trial is at most p₀=(1+B/12)/2. The predeclared comparator
p₁=53/64 comes from the synthetic finite example. Multiply the running
factor by p₁/p₀ on a win, (1−p₁)/(1−p₀) on a loss, and one otherwise.
With p₁>p₀ its conditional expectation is at most one, so crossing a
predeclared level K>1 at any time has null probability at most 1/K. This
argument needs conditional sources and settings, not iid outcome records.
The statistic is **not** a likelihood for the whole theory.

For a history-wise, settings-independent compromised fraction bounded by h,
the conservative comparator becomes (1−h)B+12h. When it reaches the
predeclared target, the checker does not bet. A run with missing protocol
information is ineligible, not a rejection; an asserted bound, chronology
or independent source is not independently verified by command-line flags.
Use `python3 -m scripts.probe_phase_network_game --help` for the strict
ordered JSONL format. Default execution uses only synthetic controls.
