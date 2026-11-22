# Detector order and event-reservoir controls

These probes separate three questions: whether two detector settings can share
an accessible history, whether deterministic address transport supplies fresh
seeds, and what one released Bell record can say about serial order. The first
two checks use exact finite arithmetic. The third has a raw-free exact control
and a separate optional empirical replay. None establishes physical iid,
derives a stochastic event origin, or closes QM.

From the repository root, no raw data are needed for these commands:

```sh
python3 -B -O -m scripts.probe_alternative_setting_gaps
python3 -B -O -m scripts.probe_adic_event_reservoir
python3 -B -O -m scripts.probe_hensen_order_controls --json
python3 -B -O -m unittest discover -s tests -p test_detector_order_controls.py
```

## Alternative setting histories

The routed fixture yields `S = 14/5` in both standalone analyzer orders. The
probe then follows hidden tags through `A0, B_y, A1`, retaining the full routed
cloud and all 40 tag histories for each `y`. The two pair reductions match the
standalone tables. The hidden history has `Pr(A0 = A1 | y = 0) = 7/10` and
`Pr(A0 = A1 | y = 1) = 3/10`, saturating the two-triple CHSH bound with zero
pair gaps. The journal is an internal diagnostic, **not an accessible Alice
record or a nondisturbing measurement**. Single-bit no-signalling in the
fixture does not authorize access to the joint hidden history. The result
does not predict physical remote signalling.

The two-triple comparison assumes the first pair is retained as a causal
prefix. The bound is `|S| <= 2 + 2(d0 + d1 + r0 - r1)`, where `d0,d1`
are total-variation gaps for the second pairs and `r0,r1` are the two
history equality rates. Opposite causal order needs its own comparison, and
history-dependent postselection can break the prefix premise. As a separate
control, a common local joint matches the first pairs and pays `1/5` on each
second pair, the sharp minimum total pair-TV gap `2/5` for this target.
The mixed-setting control also shows why single-setting iid and common
stationarity do not imply invariance under unread insertions in arbitrary
mixed setting words. The extension to a common mixture is conditional on that
stronger premise and is not a Lean proof.

## Gaussian-adic event reservoir

At depth `N`, dividing out `1+i` bijects a Gaussian quotient address with a
first bit and a depth-`N-1` remainder. Uniform initial addresses supply all
`N`-bit words equally; the compatible uniform cylinder laws describe a Haar
address as an implicit reservoir. The initial law and the digit-consuming
update are separate inputs. The same uniform address law can be preserved by
translation by `1` or rotation by `i`, which emit alternating or constant first
bits, respectively. Approximate invariance under the two generating translations
does not give a depth-uniform Haar guarantee. A fixed-port readout also needs
its own reference contract.

A predictable schedule uses only consumed bits to select the next seed size;
each untouched finite suffix is uniform conditional on its consumed prefix.
Peeking to choose which bit to expose can produce `Pr(0) = 3/4` instead. Finite
stock reports exhaustion rather than recycling. Tail freshness is not a proof of
conditional uniformity for incoming tags after adaptive cloud selection, and
encoding an iid reservoir is not a derivation of its preparation law or of
physical event actualization.

## Hensen accepted-record order control

The default command reports `not_tested_without_optional_pinned_raw_file`.
It checks the exact fixed-margin runs counts against exhaustive short words and
synthetic controls. To reproduce the optional empirical result, supply a
locally available checksum-pinned `bell_open_data.txt`:

```sh
python3 -B -O -m scripts.probe_hensen_order_controls --raw-file /path/to/bell_open_data.txt --json
```

The source is the [Hensen et al. 2015 dataset](https://doi.org/10.4121/uuid:6e19e9b2-4a2d-40b5-8dd3-a660bf3c0a31).
The [repository source record](../data/raw_observations/hensen2015.json)
pins the archive and extracted text digests and records the released selection
recipe. The reviewed replay used a pinned mirror matching the published archive
size and MD5 and the repository SHA-256 pins; the official download timed out,
so official bytes were not independently retrieved. The dataset metadata lists
the 4TU General Terms of Use; raw redistribution permission was not verified.
The probe does not download or bundle the raw record.

The fixed analysis reuses the released cuts and readouts. For each party it
counts changes of outcome sign between neighbors **in the same accepted**
`(author day, run, Alice setting, Bob setting)` **subsequence**. Those neighbors
need not be consecutive accepted trials overall and are not raw-trigger
neighbors. Conditional on each stratum's sign counts, the null gives equal
weight to all within-stratum assignments independently across strata. The
analysis convolves exact runs counts, doubles the smaller inclusive tail
(capped at one), and applies a two-party Bonferroni adjustment at family
threshold `1/20`. The adjustment does not assume independence between parties.

The optional replay used 245 **accepted trials** across 169 author day/run
groups and 221 strata (200 singletons, 19 pairs, one triple, one quadruple).
There were just 24 same-stratum neighbor pairs and two informative strata per
party:

| Party | Observed changes | Null mean | Null support | Raw p | Adjusted p | Smallest attainable adjusted p |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Alice | 13 | 83/6 | 13–15 | 2/3 | 1 | 2/3 |
| Bob | 11 | 71/6 | 11–13 | 2/3 | 1 | 2/3 |

Rejection was impossible at `1/20` with these conditioned margins. Failure to
reject is **not evidence of iid**, a rotor, or IDT-specific physics. This
retrospective control covers neither full trigger acquisition nor serial
effects outside the chosen subsequences, and it does not optimize cuts or
change points.
