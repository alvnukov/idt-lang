# What do signed transfers and five binary slots actually determine?

Replay: `python3 -m unittest tests.test_slot_sign_and_charge`. The
existing [Pauli gate](../PAULI_CHECKER_RESULT.md) asks whether a supplied
amplitude tensor obeys the declared exchange law. Here we ask a different
question: what can be recovered from rules for moving occupations?

### Transfer within a sector is not creation between sectors

Take N binary slots, fix k occupied, and permit a transfer Eᵢⱼ from j to
i when j is full and i empty. Supply reciprocal edge signs on the
linear span of configurations, with integer coefficients; require
[Eᵢⱼ,Eⱼₗ]=Eᵢₗ for distinct labels. The two orders cannot both be used
on the same input. If the intermediate slot is empty, the forward route
contributes; if it is full, the other order contributes with the minus
in the **supplied commutator**. Thus the two types of triangle have
products +1 and −1 respectively.

The [sign probe](probe_signed_slot_transfers.py) verifies these constraints
on every triangle of five finite fixed-occupation graphs. Their binary
constraint ranks equal their cycle ranks (1,1,7,21,6), so the solutions
in each checked graph differ only by rephasing each vertex. The sign
obtained by sorting an exterior product is a solution. With four slots
and two occupations the same three directed moves can close triangles of
both signs in their respective legal orders; fixed signs assigned to the
three controls cancel in the ratio. An actual observation of the ratio
would require coherent routes and a phase-sensitive recombiner. Reading
only the occupied slots cannot see it.

Unsigned moves on the same bitstrings satisfy a different law (an
anticommutator). In characteristic two the signs cannot be distinguished
at all. Neither generic closure of an algebra nor the occupation
restriction selects fermionic physics.

Even agreeing on **every** Eᵢⱼ does not fix particle creation. Change the
sign of every creation leaving one selected lower configuration, and
make the reciprocal change to annihilation. A transfer via that lower
configuration picks up the extra sign twice. In the four-slot check all
256 labeled transfer entries are identical, yet the anticommutator of
two distinct creations on the empty state changes from zero to twice a
nonzero basis vector. Thus this test gives neither the full canonical
anticommutation relations nor the relativistic spin–statistics connection.

### One known representation, and its null tests

Supply five slots, even parity, a three-slot color block, a two-slot weak
block and the exterior action of their continuous determinant-one block
group. An additive integer charge, constant on each block, traceless and
in least integer units, gives weights (−2,−2,−2,3,3) up to a common
sign. The [spectrum probe](probe_five_slot_charge.py) enumerates one
familiar left-handed matter assignment. The labels in the first column
are **identifications supplied for comparison**, not emergent particles.

| Left-Weyl comparison | (color, weak) occupied slots | Multiplicity | 6Y |
| --- | --- | ---: | ---: |
| Q | (1,1) | 6 | 1 |
| uᶜ | (2,0) | 3 | −4 |
| dᶜ | (2,2) | 3 | 2 |
| L | (3,1) | 2 | −3 |
| eᶜ | (0,2) | 1 | 6 |
| neutral singlet label | (0,0) | 1 | 0 |

This is the known exterior-algebra packaging, not a new empirical
prediction. For the representation and its history see
[Baez and Huerta](https://arxiv.org/abs/0904.1556) and the original
[Georgi–Glashow SU(5) proposal](https://doi.org/10.1103/PhysRevLett.32.438).
The additional neutral basis label is not evidence for a sterile particle.

The unsigned action has the same classical configurations but character
4 rather than 0 for a simultaneous transposition in each block. The
4+1 split gives a different charge spectrum but also passes its anomaly
checks. On 3+2 the affine alternative D=3−2k_color, identified with
3(B−L) *including* a sterile singlet, and linear combinations with 6Y
pass the tested local anomaly constraints too. Strict additivity with no
constant offset is what makes the empty subset neutral. The SU(2) global
parity check counts four doublets; it is separate from local cubic
cancellation. The order-six kernel is that of the supplied action and
does not identify the global gauge group of nature.

There is a useful independent-label test specification. For ten pair
charges cᵢⱼ let S=Σᵢ<ⱼ cᵢⱼ/4 and xᵢ=(Σⱼ≠ᵢ cᵢⱼ−S)/3. Test all ten equations
cᵢⱼ=xᵢ+xⱼ, then predict the five four-slot charges S−xᵢ. All ten individual
pair mutations are rejected, and a cross-block relabel still fits the
pairs but misses two of five fixed-label targets. The checked inputs
are **synthetic**, not a blinded particle-data analysis. The slot labels
and correspondence would have to be obtained without using the test
charges for an empirical application.

No underlying rule selects the 3+2 split here. Neither the particle
identifications, three generations, gauge dynamics, bosons, masses,
mixing, couplings, nor spacetime have been reconstructed.
