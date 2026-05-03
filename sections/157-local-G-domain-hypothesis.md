## 157. Local G Domain Hypothesis

Status:

`local_G_domain_hypothesis_initialized`

This section records the weaker and safer reading of the \(G\) anchor.

The measured \(G_N\) is not assumed to be a universal constant across all
domains.

It is a local calibration anchor for our validated weak-field domain.

### 157.1. Local anchor

Let:

\[
\mathcal D_0
\]

be the local laboratory / solar-system weak-field domain where the standard
tests are already validated.

Define:

\[
G_{\mathcal D_0}
:=
G_N.
\]

In manifest language this is:

`local_G_anchor_I`.

The previous `calibrated_G_anchor_I` should be read as this local-domain
anchor unless a broader domain is explicitly declared.

Status:

`G_anchor_reinterpreted_as_local_domain_anchor`

### 157.2. Domain-dependent effective coupling

For another domain \(\mathcal D\), allow:

\[
G_{\mathrm{eff}}(\mathcal D)
=
G_{\mathcal D_0}
\left[
1+\mathcal R_G(\mathcal D)
\right].
\]

The local domain condition is:

\[
|\mathcal R_G(\mathcal D_0)|
\le
\epsilon_{G,\mathrm{local}}.
\]

This does not assert that \(\mathcal R_G\neq0\).

It only removes the unjustified assumption:

\[
\mathcal R_G(\mathcal D)=0
\quad
\text{for every domain}.
\]

Status:

`global_G_constancy_not_assumed`

### 157.3. No-refit rule

A domain-dependent \(G_{\mathrm{eff}}\) is admissible only if its profile is
declared before comparison in the tested external domain.

Forbidden:

1. infer \(G_{\mathrm{eff}}(\mathcal D)\) from a residual after seeing it;
2. absorb every galaxy, lensing, or cosmology discrepancy into \(G(\mathcal D)\);
3. change \(G_{\mathcal D_0}\) inside the local validated domain;
4. hide source-mass calibration errors inside \(G_{\mathrm{eff}}\);
5. call a fitted \(G_{\mathrm{eff}}\) profile a derivation.

Allowed:

1. predeclare a domain profile \(\mathcal R_G(\mathcal D)\);
2. require it to vanish or stay bounded in \(\mathcal D_0\);
3. test it on held-out galactic, lensing, or cosmological domains;
4. reject it if it fails the local bound or held-out transfer.

Status:

`local_G_no_refit_rule_defined`

### 157.4. Relation to screened residuals

The existing scale-separated residual policy already permits residuals outside
the validated domain only with explicit profiles.

The local-\(G\) hypothesis is a special interpretation of such a residual:

\[
\mathcal R_{\mathrm{nonGR}}(\mathcal D)
\mapsto
\mathcal R_G(\mathcal D)
\]

when the residual acts as an effective multiplicative source coupling.

This is not always valid.

Clock redshift, dynamics, lensing, and source calibration can respond
differently. Therefore each proposed \(G_{\mathrm{eff}}\) profile must declare:

1. whether it affects clocks;
2. whether it affects dynamics;
3. whether it affects lensing;
4. how source mass is calibrated;
5. which domain variables control the profile.

Status:

`local_G_profile_must_declare_observable_channels`

### 157.5. Consequence for the calibrated branch

The calibrated branch should no longer say:

`G is a universal anchor`.

It should say:

`G_N is our local-domain anchor`.

The global question becomes:

\[
\mathcal D
\mapsto
G_{\mathrm{eff}}(\mathcal D)
\]

with:

\[
G_{\mathrm{eff}}(\mathcal D_0)=G_N
\quad
\text{within local bounds}.
\]

Current status:

`local_G_anchor_I = bridge_assumption`.

`G_domain_variation_hypothesis_I = target`.

`global_G_constancy_I = open`.

Status:

`local_G_domain_hypothesis_registered`
