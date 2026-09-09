# Candidate history: preserve hypotheses, detect checker drift

This directory is durable, Git-tracked research input and evidence, not a
disposable cache. A rejected candidate remains in the inventory and is rechecked
on exactly the same footing as a surviving candidate. Historical observations
are not ground-truth labels. In particular, an anomaly-free spectrum can fail a
minimal-SM-content target without being excluded as every possible extension.

## Use

```sh
python3 scripts/screen_hypotheses.py --batch-file candidates.json --no-cache
python3 scripts/check_candidate_history.py
python3 scripts/check_candidate_history.py --record
python3 -m unittest tests.test_candidate_history
```

Normal batch screens automatically archive here. `--history-dir` selects another
durable archive; `--no-cache` does not disable history. For programmatic research,
use `theory_experiments.candidate_history.record_batch`. The lower-level
`candidate_pipeline.run_batch` remains a computation API without archival side
effects, for internal evaluation and tests. The legacy primitive-only CLI and
same-version cache `--replay` are not new-candidate archival entry points.

`--show-candidates` only prints input templates and creates no observation.
Malformed JSON and batches outside input/resource limits are not accepted
submissions. Within those limits, raw candidate specifications are saved before
adapter validation, including unknown families. An adapter error is retained as
an execution error, never as a physical counterexample. An interrupted run can
leave an input without an observation; replay reports it rather than dropping it.

## What is retained

- `submissions/<sha256>.json`: exact submitted batch, including ordering,
  duplicates and original rational spelling, plus all evaluation bounds.
- `observations/<sha256>.json.gz`: losslessly compressed complete reports,
  including normalized inputs, check requirements/assumptions, coverage,
  witnesses, certificates, original checker hashes/runtime and scientific scope.
  `capture_provenance` identifies the archiver's version separately from the
  original report's checker version. Errors also retain capture provenance.
- `baselines/<submission-sha256>.json`: the selected computational observation
  and a reason for that selection. The first completed observation initializes
  an absent pin automatically; this is a comparison point, not scientific approval.

Content digests refer to canonical uncompressed JSON; gzip metadata is not an
identity. Publication uses atomic no-overwrite links and file/directory fsync.
Readers reject corrupt, oversized, non-regular or symlinked entries. All old
observations are integrity-checked, not just the selected baselines. Digests are
not authentication; the archive filesystem and Git review are trusted. Commit
new records to retain them in repository history and back up the repository.

## Cross-version regression contract

The history check recomputes **every** submitted candidate at its original
bounds with the current implementation and without the persistent cache.
An adapter failure is reported per candidate; neighbors are still evaluated.
It compares aggregate and per-check statuses, additions/removals, requirements,
assumptions, checked/planned counts, witnesses, normalized inputs, certificates,
scope and proof/empirical boundaries. Only request protocol-version/provenance
metadata and check ordering are excluded from semantic comparison. Original
metadata is never rewritten.

Both survival-to-counterexample and counterexample-to-survival require review.
Changed prerequisites with an unchanged aggregate result require review too.
Missing baselines and operational failures cannot become a green regression
result. Exit codes: 0 = unchanged; 4 = review required; 2 = archive/tool error.
The screening CLI also returns 4 when the new observation differs from its pin.
Ordinary candidate counterexamples retain screening exit 1 when unchanged.

Default rechecking is read-only. `--record` appends current observations for
inspection but **never** changes a baseline. To accept an intentional checker
change: inspect the complete old/new evidence and assumptions, reproduce the
relevant witness or independent positive control, explain why the change is
valid, and explicitly edit the affected baseline pin and its nonempty reason
in a reviewed change. Keep the old observation. There is no blanket snapshot
refresh command. A new interpretation should normally be a new specification
or adapter, not a retroactive rewrite of the original input.

## Initial research campaign

The initial inventory contains 275 candidates in five original input batches:
169 pair kernels, 8 power-sum rules, 4 QM readout rules, 91 charge assignments
and 3 alternative generation counts. It was imported losslessly from the
existing local campaign; the original files were not changed.

| Generation | Original checker commit | Observations | Role |
| --- | --- | --- | --- |
| Radius-2 finite screen | `033d6f4320ac089a9737acdd321c6bf6e53af89c` | 275 | Historical evidence, retained |
| Exact kernel certificate added | `651be3b880997fe24cd87dc7a49e04c4dce6d760` | 275 | Initial comparison baseline |

Generation two is selected because the certificate validator and independent
principal-minor tests resolved the known grid blind spot. Twelve kernel
aggregate statuses changed from bounded survival to counterexample; all 169
kernels gained an explicitly scoped algebraic check. The baseline has 130
kernel survivors and 39 kernel counterexamples. This is not an assertion that
the survivors are physically correct or that rejected kernels are impossible
under other reference/composition assumptions. Both historical generations
remain available, including the earlier misses.

The dedicated checker CI step replays this inventory and new archived
submissions. Regression checks protect known cases; they cannot guarantee that
an unknown correct theory will never be rejected, nor that a shared checker
bug is absent from the original observations. Independent positive controls,
negative controls and assumption audits remain essential. No QM/SM/GR proof
status or experimental status is upgraded by this archive.
