## 50. Gravity-Gate Link Frequency

This section derives the link frequency value required by the gravity gate.

It is a comparison value, not an input.

Status:

`gravity_gate_link_frequency_initialized`

### 50.1. Required frequency from the orthogonal sector

The radar-orthogonal calculator is:

$$
G_I^{(\mathrm{orth})}
=
\frac{\rho_{\chi,I}c_I^5}
{4\pi\hbar_I\omega_{\ell,I}^2}.
$$

If this sector passes the Newtonian gravity gate:

$$
G_I^{(\mathrm{orth})}=G_N,
$$

then the required link frequency is:

$$
\omega_{\ell,G}
=
\left(
\frac{\rho_{\chi,I}c_I^5}
{4\pi\hbar_I G_N}
\right)^{1/2}.
$$

This value is not used to set \(\omega_{\ell,I}\).

It is the target that an independently derived \(\omega_{\ell,I}\) must hit.

Status:

`gravity_gate_required_link_frequency`

### 50.2. Required link length

Equivalently:

$$
\ell_{0,G}
=
\frac{c_I}{\omega_{\ell,G}}
=
\left(
\frac{4\pi\hbar_I G_N}
{\rho_{\chi,I}c_I^3}
\right)^{1/2}.
$$

Using the observed Planck length:

$$
l_{P,\mathrm{obs}}^2
=
\frac{\hbar_I G_N}{c_I^3},
$$

the success condition is:

$$
\ell_{0,G}
=
2\sqrt{\frac{\pi}{\rho_{\chi,I}}}
\;l_{P,\mathrm{obs}}.
$$

This is a diagnostic relation only.

It must not define \(\ell_{0,*}\).

Status:

`gravity_gate_required_link_length`

### 50.3. Non-gravity comparison ratio

Let a non-gravitational route produce:

$$
\omega_{\ell,\mathrm{NG}}.
$$

Then the comparison ratio is:

$$
\Xi_\ell
=
\frac{\omega_{\ell,\mathrm{NG}}^2}
{\omega_{\ell,G}^2}.
$$

Equivalently:

$$
\Xi_\ell
=
\Pi_G^{(\omega)}
=
\frac{4\pi\hbar_I G_N\omega_{\ell,\mathrm{NG}}^2}
{\rho_{\chi,I}c_I^5}.
$$

Successful closure:

$$
\Xi_\ell=1\pm\epsilon_G.
$$

Status:

`non_gravity_link_frequency_comparison_ratio`

### 50.4. Failure direction

If:

$$
\Xi_\ell>1,
$$

then:

$$
G_I^{(\mathrm{orth})}<G_N.
$$

If:

$$
\Xi_\ell<1,
$$

then:

$$
G_I^{(\mathrm{orth})}>G_N.
$$

The failure direction must be reported without retuning:

$$
\rho_{\chi,I},\quad
\omega_{\ell,I},\quad
D_S,\quad
z_{I,*},\quad
q_{V,*}.
$$

Status:

`gravity_gate_failure_direction_defined`

### 50.5. Minimal matched sector

For:

$$
\rho_{\chi,I}=1,
$$

the required link length is:

$$
\ell_{0,G}
=
2\sqrt{\pi}\;l_{P,\mathrm{obs}}.
$$

The required link frequency is:

$$
\omega_{\ell,G}
=
\frac{c_I}{2\sqrt{\pi}\;l_{P,\mathrm{obs}}}.
$$

These are not primitive Planck definitions.

They are the gravity-gate target of the already pre-registered minimal sector.

Status:

`minimal_matched_gravity_gate_target`

### 50.6. Experimental ledger columns

A future non-gravity ledger must record:

| Route | Measured or bounded object | Output | Uses \(G_N\)? | Status |
|---|---|---|---|---|
| phase/action cutoff | kernel pole or update spectrum | \(\omega_{\ell,\mathrm{NG}}\) | no | open |
| clock dispersion | \(v_g(\omega)/c_I-1\) | lower bound on \(\omega_{\ell,\mathrm{NG}}\) | no | open |
| clock noise | \(\mathcal R_{\ell,y}(f)\) | lower bound or signal | no | open |
| matter-wave residual | phase/decoherence residual | lower bound or signal | no | open |
| gravity gate | \(G_N\) | \(\omega_{\ell,G}\) | yes, comparison only | diagnostic |

Status:

`omega_link_experimental_ledger_schema`

### 50.7. What is closed

Closed:

$$
\omega_{\ell,G}
=
\left(
\frac{\rho_{\chi,I}c_I^5}
{4\pi\hbar_I G_N}
\right)^{1/2}
$$

as the gravity-gate target.

Closed:

$$
\Xi_\ell
=
\frac{\omega_{\ell,\mathrm{NG}}^2}
{\omega_{\ell,G}^2}
$$

as the non-gravity comparison ratio.

Open:

1. independent \(\omega_{\ell,\mathrm{NG}}\);
2. numerical \(\rho_{\chi,I}\) if non-minimal;
3. experimental bounds from clock dispersion/noise/matter waves;
4. actual numerical comparison.

Next target:

turn the ledger schema into concrete non-gravity bounds, starting with clock dispersion and matter-wave phase residuals.

Non-gravity link frequency bounds:

`sections/51-non-gravity-link-frequency-bounds.md`

Status:

`gravity_gate_target_separated_from_input`
