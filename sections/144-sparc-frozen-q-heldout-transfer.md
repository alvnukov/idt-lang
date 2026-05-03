## 144. SPARC Frozen-q Held-Out Transfer

Status:

`heldout_transfer_rejected`

Section 143 found a diagnostic DDO154 pass for \(q=2.5\). This section freezes
that value and asks the next required question:

does the same map transfer to held-out SPARC galaxies without reselecting q?

### 144.1. Pre-registered held-out selection

The selection rule is independent of residual quality:

1. sort SPARC rotmod members by filename;
2. start after `DDO154_rotmod.dat`;
3. keep the first three galaxies with at least 8 rows.

This selects:

1. `DDO161_rotmod.dat`;
2. `DDO168_rotmod.dat`;
3. `DDO170_rotmod.dat`.

The verifier also checks this with a no-postfit provenance gate. The candidate
sources are filename order, row-count filter, and fixed held-out count. Observed
residuals, fit quality, q-grid selection, and screened residual error are
forbidden sources.

### 144.2. Frozen map

No new parameter is fitted:

\[
q=2.5,\quad
A=6.842377551859201,\quad
L_t=8271.860462954632,\quad
n=2 .
\]

For each held-out galaxy, only the outer baryonic acceleration anchors the
scale:

\[
L_I(a_b)=100000
\left(\frac{a_{b,\mathrm{out}}}{a_b}\right)^{2.5}.
\]

This uses baryonic readout data, not the observed residual, to build the
prediction.

### 144.3. Result

Acceptance threshold is kept at the DDO154 diagnostic level:

\[
\max_i|\mathcal R_{\mathrm{pred},i}-\mathcal R_{\mathrm{obs},i}|\le1 .
\]

The held-out metrics are:

| galaxy | rows | RMS error | max abs error | mean abs error |
|---|---:|---:|---:|---:|
| DDO161 | 31 | 2.167412481319462 | 3.472139558653409 | 1.7492127149324677 |
| DDO168 | 10 | 3.4184206624318167 | 4.476556241800259 | 3.3546521953364468 |
| DDO170 | 8 | 2.7656598030931256 | 3.509040879343504 | 2.7040281728403945 |

Aggregate over 49 held-out rows:

\[
\mathrm{RMS}=2.5701384629361645,\quad
\max|\Delta|=4.476556241800259,\quad
\langle|\Delta|\rangle=2.2327416632447776 .
\]

Therefore the frozen \(q=2.5\) local baryonic-acceleration map is rejected as a
transfer law.

### 144.4. Meaning for the theory

This is a useful negative result. It blocks the easiest overclaim:

DDO154 diagnostic success is not a galaxy-rotation explanation.

The remaining routes are narrower:

1. derive q from primitives before testing a new hold-out set;
2. replace the local one-row baryonic anchor by a nonlocal packet functional;
3. allow an additional independently justified galaxy parameter, then register a
   calibration/validation split before reading validation residuals;
4. abandon this screened local map family.

Accepted:

`sparc_q25_heldout_transfer_I = derived_conditional`.

Accepted:

`sparc_heldout_selection_policy_I = derived_conditional`.

Not accepted:

validated SPARC transfer.
