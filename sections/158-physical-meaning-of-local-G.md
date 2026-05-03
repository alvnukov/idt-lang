## 158. Physical Meaning of Local G

Status:

`physical_meaning_of_local_G_initialized`

This section states what \(G\) means in the calibrated local-domain branch.

It is not a primitive force constant.

It is the local conversion factor between calibrated source content and
clock-vacuum / curvature response.

### 158.1. Operational meaning

In the validated local domain \(\mathcal D_0\), \(G_{\mathcal D_0}\) is the
single coefficient that makes the following readouts agree without refit:

1. source law:

\[
\nabla^2\Phi_I
=
4\pi G_{\mathcal D_0}\rho_{\mathrm{source}};
\]

2. clock-rate response:

\[
\frac{\Delta\nu}{\nu}
\simeq
\frac{\Delta\Phi_I}{c_I^2};
\]

3. dynamics:

\[
\ddot x=-\nabla\Phi_I;
\]

4. lensing / PPN readout in the same local weak-field sector.

Thus \(G_{\mathcal D_0}\) is the local normalization of:

\[
\text{calibrated source}
\longrightarrow
\text{clock-rate strain}
\longrightarrow
\text{radar/curvature readout}.
\]

Status:

`G_as_source_to_clock_strain_normalization`

### 158.2. Stiffness meaning

In the weak-gravity calculator:

\[
G_I
=
\frac{
c_I^4D_S\ell_{0,*}
}{
2\pi\kappa_{\chi,I}z_{I,*}q_{V,*}
}.
\]

So, after local geometry/readout factors are frozen:

\[
G_{\mathcal D_0}
\propto
\frac{1}{\kappa_{\chi,\mathcal D_0}}.
\]

Here \(\kappa_{\chi}\) is the physical clock-strain cost scale.

Therefore:

1. larger \(G_{\mathcal D_0}\) means a softer local clock-vacuum response:
   less cost per unit clock strain;
2. smaller \(G_{\mathcal D_0}\) means a stiffer local clock-vacuum response:
   more cost per unit clock strain.

This is the cleanest physical reading in the current theory:

\[
G
\sim
\text{inverse local clock-vacuum stiffness}
\]

after source calibration and geometry factors are fixed.

Status:

`G_as_inverse_clock_vacuum_stiffness`

### 158.3. Calibrated hbar/G reading

In the two-anchor branch:

\[
calibrated\_hbar_I,
\qquad
local\_G\_anchor_I
\]

select the local sector.

The \(G\)-anchor then fixes a target clock-vacuum frequency scale:

\[
\Omega_{Gcal,I}^2
=
\frac{
\rho_{\chi,I}D_Sc_I^5
}{
2\pi\,calibrated\_hbar_I\,z_Iq_{V,I}local\_G\_anchor_I
}.
\]

Physical reading:

`calibrated_hbar_I` sets the action/phase unit.

`local_G_anchor_I` sets the local stiffness/frequency scale of the
clock-vacuum response, once source and geometry readouts are frozen.

Status:

`hbar_G_anchors_select_local_stiffness_sector`

### 158.4. What G is not

In this theory \(G_{\mathcal D_0}\) is not:

1. a primitive attraction parameter;
2. a universal constant already proven to hold in every domain;
3. a free knob for galaxy or cosmology residuals;
4. a proof that the theory derives gravity;
5. a replacement for source-mass calibration.

It is a local anchor tying together the clock, dynamics, source, and lensing
readouts in \(\mathcal D_0\).

Status:

`G_not_primitive_force_constant`

### 158.5. If G varies by domain

If a later domain has:

\[
G_{\mathrm{eff}}(\mathcal D)
\ne
G_{\mathcal D_0},
\]

the theory should not interpret that as an arbitrary changing constant.

It means at least one of these effective structures differs by domain:

1. clock-vacuum stiffness \(\kappa_{\chi,\mathcal D}\);
2. source calibration;
3. geometry/readout factors \(D_S,z_I,q_V,\ell_0\);
4. channel coupling between clocks, dynamics, and lensing;
5. residual sector activation.

A domain profile is admissible only if it declares which structure changes and
which observables it affects.

Status:

`domain_G_variation_interpreted_as_response_structure_change`

### 158.6. Claim boundary

Allowed claim:

> Locally, \(G\) measures the calibrated compliance of the clock-vacuum/source
> sector: the amount of clock-rate/curvature response per calibrated source.

Forbidden claim:

> \(G\) is derived as a universal number.

Forbidden claim:

> Any anomaly can be absorbed into variable \(G\).

Current status:

`local_G_physical_meaning_I = target`.

Status:

`local_G_physical_meaning_claim_boundary_defined`
