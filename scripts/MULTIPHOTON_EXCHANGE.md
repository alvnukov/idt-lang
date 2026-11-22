# What single- and two-source checks can miss

Three independent photons can have the same pairwise distinguishability
and nevertheless give different three-detector coincidence rates. This
is experimental physics, not a prediction of the packet model.
[Menssen et al.](https://arxiv.org/abs/1609.09804) varied the collective
phase in a fiber tritter. Their Eq. 4 gives the ideal one-per-output
probability; Fig. 4 adjusts temporal overlaps as one polarization rotates
and reports 330–515 triple counts per plotted point. The smooth curve is
their apparatus model. We do not use these counts as a raw trial sequence.

The [native tritter comparison](probe_packet_triad_phase.py) prepares three
normalized internal states on successive edges of a triangle. Every pair has
squared overlap 1/4 and the same balanced two-detector coincidence probability
3/8. The phase of the product of all three overlaps changes. Two fixed native
mixers give one-per-port probabilities **5/32, 1/8, 3/32, 1/8** for four
internal phase choices. Three mixers can also resolve the two orientations
that the first coincidence statistic conflates. An independently dephased
source has the same pair tests but lacks the three-state term. Two different
population calculations agree on all ten output occupations. These are
predictions for the finite candidate apparatus **with** bosonic composition
and number-resolving squared-amplitude readout, not a fit to the published
tritter or an independent derivation of those laws.

Four-source experiments can probe effects missed by three. In their distinct
interferometer [Jones et al.](https://arxiv.org/abs/2001.08125) report, in
Fig. 4, a fitted total fourfold visibility of **5.9 ± 1.0%** and **18.9 ± 3.7%**
after subtracting separately measured double-emission backgrounds.
The corrected value is not a raw detection frequency and neither is a
universal visibility for every circuit.

The [ring probe](probe_packet_exchange_cycles.py) supplies a short native
alternative, not a reconstruction of that apparatus. Each source occupies
two adjacent internal labels. Changing a phase around the entire ring leaves
every proper subset equivalent under independently rephasing the input rays;
there is no phase reference in a path of overlaps with no closed loop. For
four inputs, the native circuit puts one count at each station with probability
1/8 for either orientation tested. Within those records a signed output
parity changes from **+1/16 to −1/16**. All other records receive zero score;
the unconditional expectation therefore changes from +1/128 to −1/128.
A second fixed analyzer reads the other phase quadrature. Sparse long cycles
are not free experiments: the predicted contrast and the retained fraction
both decrease with length.

### Cheap check for proposed pure source states

Run `python3 scripts/compare_exchange_phases.py FILE.json` on
two **exact, labeled** normalized Gram matrices, under keys `left` and
`right`. Entries can be integers, rational strings, or `[real,imaginary]`
pairs. The tool validates positivity including singular states. It first
checks pair magnitudes, then transports relative phases along a spanning
forest. If a chord disagrees, it returns an actual closed cycle; otherwise
it returns rephasings witnessing equivalence. No division by zero is needed
between disconnected sets. Nonphysical input is invalid, not a rejection
of a theory. The positivity check costs O(n³) rational operations and the
graph comparison O(n²), versus enumerating n! particle permutations for
each alternative circuit. Fractions can still grow in bit length.

This shortcut certifies equality of **internal-blind passive predictions**
for independent pure sources under the stated bosonic model. It does not
certify the source from noisy clicks, work in place of a mixed or correlated
source model, or say that each cycle is observable by a particular fixed
detector. The program never upgrades a public scientific claim.

### A prospective discriminator that also works against real mixed sources

The [conjugate-analyzer probe](probe_triad_reality_swap.py) compares a
calibrated three-mixer network U with its complex conjugate on the *same*
independent preparations. For occupation (2,1,0), the probability difference
is exactly one quarter of Im Tr(ρ₁ρ₂ρ₃); one native preparation gives −1/32.
Every three-state **preparation triple**, in any common-real internal
dimension and even allowing mixtures, has zero imaginary trace under the
specified internal-blind bosonic law. Conversely a real mixed third state
can mimic the even cosine fringe alone with the same pair overlaps. With
two calibrated pure real reference states at the specified overlaps, zero
triple trace bounds the third purity by 13/18. No quoted experiment is
retrospectively tested by this new contrast. Settings-dependent losses,
correlated emissions, or a shared auxiliary phase require different nulls.
