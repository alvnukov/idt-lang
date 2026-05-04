# Public Claim Sheet

This sheet is the public boundary for the current IDT snapshot.

## One-Sentence Thesis

IDT is an executable reconstruction language for separating physical readouts,
calibrations, bridge assumptions, experimental gates, and blocked claims before
turning a candidate theory into public claims.

## Why It Is Needed

Many speculative theory projects fail because derivations, calibrations, fitted
parameters, bridge assumptions, and empirical checks are mixed together in prose.
IDT is useful now because it makes those roles explicit and machine-checkable.

The current value is not a replacement for QM or GR. The value is a disciplined
workflow for:

1. stating what is derived, conditional, calibrated, or blocked;
2. freezing assumptions before touching data;
3. rejecting bridges that only work after post-fit tuning;
4. keeping failed, near-miss, and surviving candidates comparable;
5. giving AI scientific agents a structured claim ledger instead of free-form
   theoretical text;
6. turning the ledger into a compact research graph before escalating physics
   claims.

## Auditable Successes

Current theory version: `v6.12.0`.

The current verifier manifest is executable and checks the public claim ledger:

```bash
python3 -m theory_verifier --json theory_verifier_manifest_v6_0.json
python3 -m unittest discover -s tests
```

The main current successes are bounded and methodological:

1. Finite QM readout compatibility is executable. The verifier covers
   Born/context probability tables, two-path interference, Sorkin `I3 = 0`,
   marker/eraser visibility, unitary context maps, projective readout
   repeatability, Bell/CHSH no-signalling checks, amplitude-derived CHSH tables,
   and the singlet angle model with `|S| = 2*sqrt(2)`.
2. The QM boundary is explicit. These are finite readout gates and known-formula
   compatibility checks, not a claim that full QM is derived.
3. The action-scale route is controlled. `calibrated_hbar_I` can be used as an
   explicit our-universe anchor for operational reconstruction, while
   first-principles `hbar_I` remains a blocked claim.
4. The gravity route is controlled. `calibrated_G_I` is a calibrated target, and
   first-principles `G_I` remains blocked until the missing source-response and
   vacuum-stiffness inputs are independently supplied.
5. The SPARC weak-gravity front already produces useful exclusions. It anchors
   real DDO154 data, rejects insufficient amplitudes, blocks post-fit residual
   provenance, rejects a proportional radius map, records a baryonic
   acceleration near miss, and rejects a frozen-`q` held-out transfer.
6. The sector role taxonomy is machine-guarded. Symbols must be classified as
   structural selectors, dimensional anchors, dimensionless couplings, bridge
   assumptions, derived readouts, experimental gates, or blocked claims.
7. The IDT-MetaLang research graph contract is executable. It records claim
   role typing and dependency DAG checks as implemented, while proof status,
   prediction protocol, failure ledger, compact core, and theorem cards remain
   partial rather than complete. Its evidence references must resolve to real
   manifest objects, schema surfaces, verifier checks, or Markdown sections.
   Full-QM frontier blockers now have first-class theorem cards.

## What The Verifier Catches

The verifier is designed to reject progress by relabeling. It blocks:

1. a derived claim that depends on an open or blocked object;
2. a calibrated anchor presented as a first-principles derivation;
3. a structural selector used as a dimensional constant;
4. a bridge assumption relabeled as a derived readout;
5. SPARC residual claims that reuse the observed residual as their own source;
6. full-QM claims while the action scale, generator, apparatus, and facticity
   spine remain incomplete.

## What Is Explicitly Not Claimed

IDT currently does not claim:

1. a completed derivation of QM;
2. a completed derivation of GR;
3. a numerical first-principles derivation of `hbar_I`, `G_I`, or
   `alpha_em_I`;
4. an explanation of dark matter or dark energy;
5. experimental confirmation as a replacement theory;
6. a successful SPARC galaxy-rotation fit.

## Derived, Conditional, Calibrated, Blocked

Current public classification:

| Category | Examples |
|---|---|
| Derived or finite executable readouts | context Born table, two-path interference, Sorkin `I3 = 0`, finite Bell/CHSH gates |
| Derived conditional | amplitude packet, unitary context evolution, generator-side QM spine, operational QM with declared anchors |
| Calibrated anchors | `calibrated_hbar_I`, calibrated gravity anchors and targets |
| Structural selectors | primitive holonomy/source and topology/winding selector targets |
| Experimental gates | SPARC gates, Bell/CHSH gates, residual provenance gates |
| Blocked claims | first-principles `hbar_I`, first-principles `G_I`, first-principles `alpha_em_I`, `full_QM_I = derived` |

## Next Public Milestones

The next public milestone is not a stronger slogan.

The immediate language milestone is to promote prediction and failure records
into first-class manifest objects, and then extend theorem cards beyond the
full-QM frontier.

The next physics milestone remains one pre-registered, non-refitted bridge that
survives an independent holdout gate. The most promising current route is
weak-gravity closure:

```text
source response + vacuum stiffness + calibrated action anchor
=> calibrated_G_I target
=> independent no-refit gate
```

Until that gate survives, the project should be presented as a controlled
research programme with auditable successes and useful exclusions, not as a
completed physical theory.
