## 143. SPARC Baryonic Exponent Family

Status:

`diagnostic_family_pass_not_validated`

This section closes the immediate ambiguity left by Section 142. A single
baryonic-acceleration map with fixed exponent \(q=2\) was a near miss, but that
does not prove the local map route is dead. The next honest test is a
predeclared small family:

\[
L_I(a_b;q)=L_{\mathrm{out}}
\left(\frac{a_{b,\mathrm{out}}}{a_b}\right)^q ,
\qquad
q\in\{1,1.5,2,2.5,3\}.
\]

Here \(a_b=v_b^2/R\) is the baryonic acceleration read from the SPARC mass-model
packet, and \(L_{\mathrm{out}}=100000\) is anchored at the outer DDO154 row.

The screened residual profile is unchanged:

\[
\mathcal R(L)=
\frac{A}{1+(L_t/L)^n},
\quad
A=6.842377551859201,
\quad
L_t=8271.860462954632,
\quad
n=2 .
\]

### 143.1. Diagnostic q scan

For the 12 DDO154 rows, the finite verifier obtains:

| \(q\) | RMS error | max abs error | mean abs error |
|---:|---:|---:|---:|
| 1.0 | 2.5352051265854065 | 5.013432558195559 | 2.0052150740682904 |
| 1.5 | 1.937624995759783 | 3.5231209288627565 | 1.5842273597245127 |
| 2.0 | 0.9226475712953834 | 1.2041618124170617 | 0.8163298146002157 |
| 2.5 | 0.41184161715564477 | 0.7174826101020031 | 0.33277922579801605 |
| 3.0 | 1.229423259166758 | 2.163585695463742 | 0.9549864916563973 |

With the diagnostic threshold

\[
\max_i|\mathcal R_{\mathrm{pred},i}-\mathcal R_{\mathrm{obs},i}|\le1 ,
\]

the best scanned value is \(q=2.5\). It passes the DDO154 diagnostic threshold.

### 143.2. Why this is not a fit claim

The q value was selected after looking at the DDO154 residual packet. Therefore
the verifier records a separate postfit provenance gate:

`sparc_q_selection_postfit_demo`

This gate must pass only by declaring the q selection postfit-contaminated.

So the accepted statement is narrow:

there exists a simple baryonic-acceleration exponent family with one member
that tracks DDO154 better than the rejected \(q=2\) map.

The rejected statements are:

1. \(q=2.5\) is derived from IDT primitives;
2. DDO154 is fitted by a validated model;
3. the screened residual is dark matter;
4. the result transfers to other galaxies without held-out validation.

### 143.3. Experimental meaning

This is still useful because it creates a falsifiable next step. The next
version must freeze either:

1. \(q=2.5\) as a provisional diagnostic value before testing other galaxies; or
2. a primitive derivation of \(q\), before reading any held-out residuals.

If held-out SPARC galaxies fail, the local baryonic-acceleration map is rejected.
If they pass without reselecting q, the route becomes a real predictive
candidate.

Section 144 performs the frozen-q held-out test and rejects this local transfer
law for the first deterministic held-out set.

### 143.4. Verifier gates

New finite gate:

`screened_baryonic_exponent_scan`

New manifest gates:

1. `sparc_baryonic_exponent_family_scan_demo`;
2. `sparc_q_selection_postfit_demo`.

Accepted:

`sparc_baryonic_exponent_family_I = derived_conditional`.

Accepted:

`sparc_q_selection_postfit_policy_I = derived_conditional`.

Not accepted:

validated screened-galaxy residual theory.
