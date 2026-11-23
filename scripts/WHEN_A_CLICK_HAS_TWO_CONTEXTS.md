# Does the same click mean the same event in two experiments?

Use one token, three ports and five possible yes/no tests. Test i occurs in two neighboring contexts: once alongside test i−1 and once alongside test i+1. If both occurrences mean the same event on every prepared state, and neighbors never click together, at most two of the five tests can click. This is the five-cycle exclusivity question in [Klyachko et al.](https://arxiv.org/abs/0706.0126). Here the tests are built from actual programmed contacts rather than assigned directly to five output columns.

## Five different native effects

The [contact probe](probe_native_pentagon_contexts.py) uses the ternary switch and its protected ordinary meter. To query a port, route, write to fresh records, then undo the route: the original data and shades are restored on all 24 source/stock preparations. Every neighboring pair of tests can be read on **one** preparation in either order; nonneighbors really can both click. Sixteen preparations give two clicks across the five alternatives, the other eight give one. Uniform weight on all 24 gives 1/3 per test and S=5/3. An explicitly supplied uniform choice among five different two-click preparations gives 2/5 at every test and S=2. That is the classical bound, not a five-way experimental coincidence.

The implementation of the measurement matters. The three frozen routing hubs generate 108 distinct transformations and 81 distinct yes/no effects on the tested preparation set. Of 648 unordered disjoint effect pairs, only 324 admit one routing word that displays them on different output ports. There is no faithful pentagon of that more restrictive kind within this library. Reversible route/read/undo does realize one with at most two hubs in each test's route. Failure in the first adapter is not a reason to discard the primitive.

## The cost of changing what is being read

For a fixed stock write L_i and R_i for the two potential readings of test i. Put S = Σ(L_i+R_i)/2, D = Σ[L_i ≠ R_i] and J = Σ R_i L_(i+1). On **every one** of the 1,024 ten-bit assignments,

    S ≤ 2 + D/2 + J.

The inequality also holds after averaging. J counts neighboring double clicks. D counts mismatches for the *same stock across contexts*; comparing separate observed marginals is not a measurement of D. The native restored tests have D=J=0. Context-dependent addressing can instead give exactly the same individual probabilities from the left and the right, J=0, and S=5/2, at the cost of a hidden mismatch.

As an external comparator only, five orthogonal-neighbor rank-one qutrit projectors give S=√5 for the axial state. At J=0 any common deterministic coupling that imitates these edge probabilities needs mean D ≥ 2√5−4. The probe gives a mixture attaining the bound and another with five times as many mismatches and **identical full pair tables**. The earlier [rational pentagon](probe_native_rational_pentagon.py) uses supplied amplitudes and projective readout; it is not a violation by the ternary contact.

[Lapkiewicz et al.](https://doi.org/10.1038/nature10119) performed a photonic experiment on single three-state systems. Neither the hidden mismatch D nor the displayed native circuit is measured by that publication. Sequential compatibility and disturbance require operational checks ([Gühne et al.](https://doi.org/10.1103/PhysRevA.81.022121)); perfect agreement of simulated marginal histograms cannot provide them. This fixture is not a Bell test or an exclusion of all contextual models.
