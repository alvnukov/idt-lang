## 19. Marker-Channel Update Rule

This section supplies the first packet update rule for the compressed two-path calculator.

It describes how an apparatus or environment changes coherence without modelling every microscopic degree of freedom.

Status:

`marker_channel_update_rule_initialized`

### 19.1. Marker channel as compressed map

Let two alternatives \(a,b\) couple to marker/readout channels:

$$
\mathcal M_a,\quad \mathcal M_b.
$$

The compressed marker overlap is:

$$
\gamma_{ab}
=
\langle \mathcal M_b,\mathcal M_a\rangle_{\mathrm{readout}}.
$$

The coherence update is:

$$
\Gamma_{ab}
\mapsto
\Gamma'_{ab}
=
\Gamma_{ab}\gamma_{ab}.
$$

Therefore:

$$
\kappa'_{ab}
=
\kappa_{ab}|\gamma_{ab}|,
$$

and:

$$
\theta'_{ab}
=
\theta_{ab}+\arg\gamma_{ab}.
$$

This updates both visibility and phase.

Status:

`marker_overlap_updates_coherence_packet`

### 19.2. Channel composition

For successive independent marker channels:

$$
\mathcal M^{(1)},\mathcal M^{(2)},\ldots,\mathcal M^{(n)},
$$

the compressed update is:

$$
\gamma_{ab}^{\mathrm{tot}}
=
\prod_{r=1}^{n}
\gamma_{ab}^{(r)}.
$$

Thus:

$$
\kappa_{ab}^{\mathrm{tot}}
=
\kappa_{ab}^{0}
\prod_{r=1}^{n}
|\gamma_{ab}^{(r)}|,
$$

and:

$$
\theta_{ab}^{\mathrm{tot}}
=
\theta_{ab}^{0}
+
\sum_{r=1}^{n}
\arg\gamma_{ab}^{(r)}.
$$

This is the compressed alternative to explicit tensoring of many environmental subsystems.

Status:

`marker_channels_compose_multiplicatively`

### 19.3. Weak marking expansion

For weak marking:

$$
\gamma_{ab}
=
1-\varepsilon_{ab}+i\varphi_{ab}
+
O(\varepsilon^2,\varphi^2),
$$

with:

$$
\varepsilon_{ab}\ge0.
$$

Then:

$$
\kappa'_{ab}
\approx
\kappa_{ab}(1-\varepsilon_{ab}),
$$

and:

$$
\theta'_{ab}
\approx
\theta_{ab}+\varphi_{ab}.
$$

Interpretation:

1. \(\varepsilon_{ab}\) is distinguishability leakage;
2. \(\varphi_{ab}\) is apparatus-induced phase shift.

Known gate:

weak which-way marking can reduce visibility continuously and shift fringes.

Status:

`weak_marker_update_expansion`

### 19.4. Eraser conditioning

A later readout condition \(E\) changes the accessible marker overlap:

$$
\gamma_{ab}
\mapsto
\gamma_{ab|E}.
$$

Conditional coherence:

$$
\kappa_{ab|E}
=
\kappa_{ab}^{0}
|\gamma_{ab|E}|.
$$

Conditional phase:

$$
\theta_{ab|E}
=
\theta_{ab}^{0}
+
\arg\gamma_{ab|E}.
$$

Eraser recovery occurs when:

$$
|\gamma_{ab|E}|
\approx
1.
$$

Known gate:

quantum eraser experiments recover fringes only after conditioning on the eraser readout channel.

Status:

`eraser_conditioning_updates_packet`

### 19.5. Recoverability and irreversibility

Define the best recoverability channel:

$$
E_\star
=
\arg\max_E
|\gamma_{ab|E}|.
$$

Then:

$$
|\gamma_{ab}^{\mathrm{rec}}|
=
|\gamma_{ab|E_\star}|
=
\max_E|\gamma_{ab|E}|.
$$

Recoverable coherence:

$$
\kappa_{\mathrm{rec}}
=
\kappa_{ab}^{0}
|\gamma_{ab}^{\mathrm{rec}}|.
$$

Irreversibility index:

$$
\Lambda_{\mathrm{irrev}}
=
-
\log
|\gamma_{ab}^{\mathrm{rec}}|.
$$

If:

$$
\Lambda_{\mathrm{irrev}}=0,
$$

then the marking was reversible in the accessible readout domain.

If:

$$
\Lambda_{\mathrm{irrev}}>0,
$$

then some coherence has moved into uncontrolled inheritance channels.

Status:

`irreversibility_from_unrecoverable_marker_overlap`

### 19.6. Facticity threshold

Define operational facticity:

$$
f_{ab}
=
1-\kappa_{ab}.
$$

For a declared readout tolerance \(\epsilon_F\), alternatives are effectively factual when:

$$
\kappa_{\mathrm{rec}}
\le
\epsilon_F.
$$

This avoids treating mere unconditioned visibility loss as collapse.

Factuality is therefore:

$$
\text{unrecoverable coherence loss}
$$

not:

$$
\text{temporary loss of observed fringes}.
$$

Status:

`facticity_threshold_requires_unrecoverability`

### 19.7. Residual gates

The marker update predicts:

$$
V_{\mathrm{marked}}
=
V_0|\gamma_{ab}|,
$$

and:

$$
V_E
=
V_0|\gamma_{ab|E}|.
$$

Residuals:

$$
\mathcal R_V
=
V_{\mathrm{obs}}-V_0|\gamma|,
$$

and:

$$
\mathcal R_{\theta}
=
\theta_{\mathrm{obs}}
-
(\theta_0+\arg\gamma).
$$

If residuals persist across controlled marker channels, the compressed marker model is incomplete.

Status:

`marker_update_residual_gates`

### 19.8. What v5.20 closes

This section gives a packet update rule:

$$
\gamma_{ab}
\Rightarrow
(\kappa_{ab},\theta_{ab})
\Rightarrow
(V,\text{fringe phase},\Lambda_{\mathrm{irrev}}).
$$

It reduces the need to model the full environment when only visibility, phase, and recoverability are measured.

It remains conditional because:

1. the marker overlap \(\gamma_{ab}\) must be derived from apparatus/readout physics;
2. uncontrolled channels must be bounded experimentally;
3. non-bilinear residuals still require \(I_3\) gates.

Next target:

derive \(\gamma_{ab}\) from a primitive apparatus coupling rather than treating it as an input packet.

Coherence magnitude bridge:

`sections/72-coherence-magnitude-bridge.md`

Status:

`marker_channel_compression_rule_defined`
