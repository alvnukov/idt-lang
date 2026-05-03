## 72. Coherence Magnitude Bridge

This section connects kernel-map magnitudes:

$$
r_j
$$

to recoverable coherence.

It prevents \(r_j\) from becoming a damping fit parameter.

Status:

`coherence_magnitude_bridge_initialized`

### 72.1. Word coherence factor

For a grammar word \(w_j\), define its compressed coherence factor:

$$
\gamma_j
=
r_je^{i\Phi_j}.
$$

The magnitude is:

$$
r_j=|\gamma_j|.
$$

Positivity requires:

$$
0\le r_j\le1.
$$

Status:

`word_coherence_factor_defined`

### 72.2. Recoverable magnitude

If the word has accessible conditioning channels \(E\), define:

$$
r_j^{\mathrm{rec}}
=
\max_E|\gamma_{j|E}|.
$$

The irreversible loss is:

$$
\Lambda_j
=
-
\log r_j^{\mathrm{rec}}.
$$

Thus:

$$
r_j^{\mathrm{rec}}
=
e^{-\Lambda_j}.
$$

Status:

`recoverable_word_magnitude`

### 72.3. Kernel-map magnitude input

The kernel-normalization map must use:

$$
r_j=r_j^{\mathrm{rec}}
$$

if the fixed-point route is meant to describe stable clock-vacuum coherence.

Using unconditioned visibility loss would confuse reversible marking with irreversible kernel damping.

Status:

`kernel_map_uses_recoverable_magnitude`

### 72.4. Additivity

For independent word segments:

$$
w=w_1\circ w_2,
$$

coherence factors multiply:

$$
\gamma_w=\gamma_{w_1}\gamma_{w_2}.
$$

Therefore:

$$
\Lambda_w
=
\Lambda_{w_1}+\Lambda_{w_2}.
$$

This matches the action-cocycle additivity on the phase side.

Status:

`coherence_loss_additivity`

### 72.5. No-fit rule

Forbidden:

1. choose \(r_j\) to move the fixed point toward \(\omega_{\ell,G}\);
2. use unconditioned visibility as irreversible loss;
3. hide missing grammar phases inside \(r_j\);
4. change accessible conditioning channels after comparison.

Allowed:

1. derive \(r_j\) from recoverable marker/coherence channels;
2. set \(r_j=1\) only for a declared fully coherent vacuum word;
3. carry \(\Lambda_j\) as a residual if coherence loss is physical.

Status:

`coherence_magnitude_no_fit_rule`

### 72.6. What is closed

Closed:

$$
r_j=e^{-\Lambda_j},
\qquad
\Lambda_j=-\log r_j^{\mathrm{rec}}.
$$

Open:

1. primitive derivation of \(\gamma_j\);
2. recoverability channels for clock-vacuum words;
3. whether stable vacuum words have \(r_j=1\);
4. fixed point \(\Theta_*\).

Next target:

combine PF weights, action cocycle phases, and coherence magnitudes into a front-status for \(F_G\).

Fixed-point map front status:

`sections/73-fixed-point-map-front-status.md`

Status:

`coherence_magnitude_route_defined`
