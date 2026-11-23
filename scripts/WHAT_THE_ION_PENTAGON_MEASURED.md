# A measured five-context table from one trapped ion

On a preselected slice of the [ETH trapped-ion archive](https://tiqi.ethz.ch/publications-and-awards/public-datasets.html), **44,690 of 50,000 ordered outcome pairs were unlike**. This is a result from the authors' apparatus, not from an IDT simulation. We compare the observed pair statistics to the explicit common-stock, context-independent event contract in the [native pentagon probe](WHEN_A_CLICK_HAS_TWO_CONTEXTS.md). We do not fit the contact law or infer the ion's hidden state.

## A selector independent of the observed score

Use the five-observable, full modular sequence (`005_gen`), normal order, with every shot in the selected blocks. Choose the lower median of the distinct pulse times before inspecting the numeric outcome rows: the six keys are 10.4 through 10.9, giving **10.6**. There are 100 blocks of 100 pairs for each ordered edge. This is not the publication's separately selected point nearest the compatibility angle. Every *archived pair* in these blocks is kept; this is not an audit of unrecorded attempts or of all apparatus errors.

| Ordered pair | dark,dark | dark,bright | bright,dark | bright,bright |
| --- | ---: | ---: | ---: | ---: |
| 1,2 | 1,028 | 4,413 | 4,555 | 4 |
| 2,3 | 1,084 | 4,352 | 4,554 | 10 |
| 3,4 | 1,070 | 4,348 | 4,560 | 22 |
| 4,5 | 1,001 | 4,383 | 4,609 | 7 |
| 5,1 | 1,077 | 4,389 | 4,527 | 7 |

Assign +1 to bright and −1 to dark. The sum C of the five measured product means is −3.938. With S the sum of mean bright probabilities (averaging the two appearances of each event) and J the sum of neighboring double-bright probabilities, X = S−J = (5−C)/4 = **2.2345**. Defining the comparison using X avoids silently assuming that double-bright events never occur.

For a common setting-independent coupling of **these empirical tables**, X ≤ 2+E[D]/2, where D counts how many of the five candidate event bits would change for the same stock between contexts. Such a coupling needs E[D] ≥ **0.469**. The sum of observed same-event marginal differences is only 0.092. Neither value measures D directly; the former is a conditional lower bound for matching the table, and the latter uses two different groups of observed pairs. This is not an assumption-free exclusion of stochastic, contextual or disturbance-sensitive candidates.

How weakly is this latent quantity determined? The [exact coupling certificates](probe_ion_coupling_certificates.py) exhibit two nonnegative, 16-atom distributions that both reproduce **all 20 normal-order cells**. One has E[D]=0.469, the other E[D]=4.479. The event inequalities exclude values outside that range and mixtures attain every value inside it. For reverse order the exact range is [0.4735,4.4837]. These are sharp identification intervals for the stated empirical coupling problem, not sampling intervals or physical disturbance measurements. Verifying the stored integer certificates requires no optimizer.

The plug-in standard error of X is about 0.00344 *if shots and edges are independent*. It is not a confidence guarantee against drift or systematic error. Reversing the order at the same pulse time and threshold gives 44,735 unlike pairs in 50,000, X=2.23675. That is a control on the same apparatus, not a second experiment. Compare the method and the authors' compatibility analysis in [Malinowski et al., Appendix E and Tables I–II](https://arxiv.org/html/1712.06494). The [independent superconducting-qutrit experiment of Jerger et al., Table 1](https://www.nature.com/articles/ncomms12930/tables/1), reports C=−3.489(1) for its own sequence and preparation; it does not reproduce the selected ion counts.

## How far are these tables from a single assignment?

A global assignment fixes one bright/dark bit per vertex, the same in both contexts. An *exclusive* assignment also forbids adjacent bright vertices. The [edit probe](probe_ion_edit_robustness.py) answers three distinct questions about the fixed tables:

| Minimum | Normal order | Reverse order |
| --- | ---: | ---: |
| Coupled stocks with at least one disagreement, keeping every cell unchanged | 4,690 / 10,000 stocks | 4,735 / 10,000 stocks |
| Ordered pair records to relabel to obtain a mixture of global assignments | 4,690 / 50,000 pairs | 4,735 / 50,000 pairs |
| Bright/dark bits to flip to obtain a mixture of exclusive global assignments | 4,790 / 100,000 bits | 4,837 / 100,000 bits |

A global assignment has at most four unlike edges; an exclusive assignment has at most four bright endpoints counted across the five edges. One mismatched stock or one pair relabel can account for at most one excess unlike edge, and one bit flip can remove at most one bright endpoint. For each order, a 16-row integer transport attains all three lower bounds, using separate targets for the two editing questions. Its verifier reconstructs all 20 original cells and preserves every setting's shot total. Stocks are hypothetical couplings, not matches between observed shots. The edits are counterfactual distances, not estimates of detector error, population bounds or p-values.

## What is reproducible offline?

The [small fixture](../data/ion_pentagon_2018_summary.json) contains the two aggregate tables, their provenance and SHA-256 pins, not a redistributed shot archive. By default the [replay](probe_measured_ion_pentagon.py) computes the above numbers from the fixture. Optionally supply the [authors' original ZIP](https://ethz.ch/content/dam/ethz/special-interest/phys/quantum-electronics/tiqi-dam/documents/Datasets/Dataset_Public%20repository.zip):

    python3 -m scripts.probe_measured_ion_pentagon --json
    python3 -m scripts.probe_ion_edit_robustness --json
    python3 -m scripts.probe_measured_ion_pentagon --zip /path/to/original.zip --json

Each raw row contains alternating first and second photon counts for 100 shots. A count of at least seven is bright: this cutoff reproduces the authors' four cell counts inferred from the three archived block means in **all 3,000 normal-order blocks**, and the same cutoff agrees in all 3,000 reverse-order blocks. It was not selected for maximizing X. A source-hash or decoding mismatch is a provenance failure, not evidence for or against a candidate.
