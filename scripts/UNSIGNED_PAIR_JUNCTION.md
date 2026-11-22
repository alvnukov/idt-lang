# Two unsigned marks: when do they mix like amplitudes?

**Candidate:** a packet occupies two different legs of a four-leg junction.
A single tick rewrites it as another such packet. This is discrete and
unsigned. It needs no *stored* complex number, norm, or detector rule.
It does assume packet locality, stable leg labels, a clock and a way of
feeding packets into each junction. Below, the assumptions that produce
the mixer and the assumptions that produce a click are tested separately.

## Learn the table, rather than put the mixer in

There are six unordered two-leg packets and **46,656** deterministic tables.
Group the four legs as two ports with two internal rails each. Require two
ticks on a **single packet** to exchange those ports while preserving rail
identity. The induced swap on six packet labels fixes two labels and exchanges
the other four in two disjoint transpositions. Its square root must be a
permutation. On the moving labels there are two possible four-cycles, and
on the two fixed labels one may either swap or fix them. Requiring the two
equal-input packets to be individually transparent leaves **two tables**.
The [exhaustive replay](probe_unsigned_collision_search.py) recovers them
without checking amplitudes or conservation of quadratic stock during
selection. The pair differs only by orientation.

| Criterion in the six-species class | Tables |
| --- | ---: |
| Output histogram determined by input histogram, independently of packetization | 318 |
| Bijective on the six packet species | 720 |
| Both of the above; equivalently, preserves the squared population for every packet cloud | 48 |
| Two-tick raw port exchange | 4 |
| Two-tick raw exchange plus equal-input transparency | 2 |
| Only the corresponding **coarse port-count** comparisons | 8 |

For the histogram test it suffices to compare the three ways to pair one
mark of each leg. An integer change in edge multiplicities that leaves
every vertex count unchanged must be constant on each of the three opposite-edge
pairs, with the three constants summing to zero. These two independent
differences therefore generate the entire ambiguity. For a bijection to
factor through vertex counts it must permute the three opposite-edge pairs,
possibly swapping either endpoint in each. The resulting 48 operations are
leg permutations and their compositions with edge complementation. The
coincidence of these two classes is not an assumption about physics.

**Try a new candidate.** Supply its six output indices in input order
01,02,03,12,13,23 (same order for output indices 0–5), plus which
readout is available. The [four example rows](../data/unsigned_pair_packet_controls.json)
can be evaluated together:

    python3 scripts/screen_hypotheses.py --batch-file data/unsigned_pair_packet_controls.json --no-cache

This example intentionally includes a resolved counterexample, so its
nonzero batch exit is expected. Like other candidate batches it records
the submission in history; `--no-cache` only disables the disposable
cache. Supply a temporary `--history-dir` for a scratch replay.
The same reset table survives under
`port_totals` but fails under `resolved_packets`. Both contracts permit
all six input packets to be separately prepared; they differ only in the
output measurement. A limited budget that exhausts no counterexample and
does not finish the checks gives an inconclusive result. The individual
candidate costs at most six echo cases and two transparency cases, not
the 46,656-table census. These are requirements of the microscopic model,
not measured particle data.

With **only two pure-port preparations**, a different test is needed.
Let F be the unknown tick, S an independently implementable port exchange,
and V a trusted internal swap in the first port, with only final port totals
reported. The [observability search](probe_packet_echo_observability.py)
finds four short experiments totaling 15 operations: one FF, one FSF
and FVFVF on both pure inputs. Together, with the outputs specified in the
probe, they isolate the two intended orientations among all 46,656 tables.
Without the independent controls, repeated F alone cannot distinguish
either genuine rule from the hidden resets on those preparations. Gauge-
conjugate orientations still need not be distinguishable. This is a
proposed device test, not an assumption that a laboratory has V or S.

## From complementary edges to the mixer

First replace each unordered pair {i,j} by the two *unused* labels. Of
all deterministic, fully permutation-equivariant maps from distinct
two-mark inputs to distinct two-mark outputs, a nonidentity possibility
of this kind exists **only at valency four**: the stabilizer of the
input pair leaves its two-element complement invariant only then. This
class deliberately excludes repeated-input species, ordered outputs,
extra marks and internal memory. The complementary rewrite is already
present in the [four-label chain controls](REFERENCE_CHAIN_PROBES.md);
the new question is how a complete layer acts on an ensemble.

If nᵢ marks are on leg i and P=Σnᵢ/2 packets fill the junction, exactly
P−nᵢ output packets contain i. This is the real reflection
G=½**1** **1**ᵀ−I. A cyclic rewiring R gives RG, with negative entries on
one four-cycle. The two raw transparent roots above are RG and R⁻¹G.
Writing z=n₀+i n₁ and w=n₂+i n₃, one orientation has outputs
((1+i)z+(1−i)w, (1−i)z+(1+i)w)/2. Complex notation describes the table,
not its microscopic instructions. RG squares to the port exchange and
fixes equal inputs. Leg permutation symmetry does not give a preferred
handedness. [Explicit unsigned packet replay](probe_complement_collision_mixer.py).

A packetization exists exactly when the total is even and no leg contains
more than half. Sorting marks by leg and matching opposite halves is one
existence proof, **not** a fundamental sorter. Uniformly random matching
of physical marks with equal-label collisions left unchanged gives a
different result. If mᵢ equal pairs formed at i, the unturned output
is P−nᵢ+4mᵢ−Σmⱼ. At n=(B±1,B∓1,B,B), the odd first-leg response in the
random model is −1/(4B−1), instead of −1 for complete unlike pairs.
There is no need to fit a rate to tell the two candidates apart.

## Can the pairs form without a controller?

Yes in an abstract encounter model. The [two-rule resolver](probe_asynchronous_pair_resolver.py)
first binds **any** two free marks, allowing a temporary equal pair aa.
It repairs aa next to bc with a absent from bc by producing ab and ac;
b=c is allowed. Each rule strictly decreases the number of free marks
plus the number of equal pairs. On even inputs, if an equal pair aa
remains at termination, every other pair contains a. The number of
equal pairs is then exactly (2nₐ−Σnᵢ)/2. Hence a balanced admissible
histogram resolves completely for *every maximal schedule*. The
pairing itself is not unique; its output leg counts are. Free and
bound marks are different internal states. One can test incomplete
encounters, odd inputs and starting a second layer too early without
misclassifying these as successes of the two-rule model.

The resolver assumes needed pairs can encounter one another and that
the next computation waits for resolution. Its potential bounds rewrite
counts, **not** wall-clock time or spatial communication. Nor is it
injective on all microscopic pairing records. For 2m labeled marks,
m each of two colors, a fraction 2ᵐ/binom(2m,m) of all initial perfect
matchings are already unlike. If every original pairing carries physical
information, a completely reversible repair needs at least the reciprocal
number of distinguishable history labels, rounded up. There is no such
inference about a source that supplies only free marks or an already
valid pairing.

## Which square is being counted?

For two ordered packet addresses e,f, count one ticket per shared leg.
Complementing both packets leaves |e∩f| unchanged. The named leg of a
ticket maps to the unique unused leg if that intersection has size one;
for size two a consistent tie convention gives a bijection. Thus every
ticket exits, without new random seeds or postselection. Uniformly
sampling an initial ticket gives raw weights nᵢ². The tie convention can
change individual trajectories. A single-mark detector on the same
collision gives linear counts instead. [Whole-ticket replay](probe_unsigned_pair_tickets.py).

There are two different obstacles to a physical interpretation:

1. **Unshifted counts.** A nonempty injection through only the first port,
   with the other port empty, is admissible only as (m,m,0,0). It splits
   to (0,m,m,0). Sending either resulting port to a fresh blank splitter
   leaves only one populated leg; no unlike pair exists. Merely adding
   more input marks or choosing a common initial complex phase does not
   remove this two-gate obstruction.
2. **Positive background.** One can encode real and imaginary amplitudes as
   deviations from a uniform stock B. Then every specified finite native
   word admits an unsigned implementation at sufficient signal scale.
   The two overlapping mixers T₀₁,T₁₂ repeated t times on a single named
   input require an initial integer scale divisible by **2ᵗ**, with our
   constructions using B=2ᵗ. After each gate the active two components
   with unequal least (1+i)-denominator levels get a new level one greater
   than the larger one; the two-step endpoint has levels (2t−1,2t,2t) for
   t≥1. Clearing these denominators with a real integer requires and
   suffices to use 2ᵗ. A uniform shift cannot clear fractions. This is a
   cost of *this common unit of occupancy*, not a lower bound on every
   computer, every possible encoding or nature.

Raw-ticket weights on a positive background are not squared **deviations**.
The [background detector check](probe_unsigned_background_readout.py) makes
that gap quantitative. Compare dark (B,B,B,B) with (B+a,B−a,B,B), using
the same randomized click policy on k uniformly sampled colors. For k≤B
without replacement every possible word can already occur in darkness;
zero dark probability implies zero bright probability. The sharp
likelihood-ratio bound is (B+a)ₖ/(B)ₖ, attained on the all-plus word.
For B=8,a=2,k=3 a bright rate of 1/4 requires a dark rate at least
**103/620** from the exact receiver tradeoff. Ordered hidden bonds, mark
identities, many more samples or an active subtraction device change the
contract. With k=B+1 an all-plus detector can be exactly dark, but this
does not generally give a quadratic law. No empirical false-click rate,
absolute physical mark scale, or unclonable single-particle detector is
inferred from this finite candidate.
