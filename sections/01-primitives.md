## 1. Primitive Structure

Current executable v6 core:

$$
\mathfrak T_0=(H,\mathcal E,\mathsf M,\mathcal I)
$$

This is the current verifier-facing carrier-neutral contract. It is not yet the
lowest acceptable base. The Bell/Hilbert/gravity audit shows that the theory
must avoid making any global fact table, Hilbert carrier, or metric geometry
primitive.

| Symbol | Meaning | Status |
|---|---|---|
| \(H\) | possible histories / event bundles | executable v6 primitive; candidate derived inheritance traces |
| \(\mathcal E\subseteq2^H\) | event algebra | executable v6 primitive; candidate derived local event algebras |
| \(\mathsf M\) | admissible readout contexts | executable v6 primitive; candidate context cover/category |
| \(\mathcal I\) | admissible inheritance acts | executable v6 primitive; candidate transition family |

The deeper base candidate is context-first:

$$
\mathfrak B_0=(\mathcal C,\mathcal O,\mathcal I,\mathcal R,\mathcal D)
$$

| Symbol | Meaning | Status |
|---|---|---|
| \(\mathcal C\) | admissible context cover/category | lower-base candidate |
| \(\mathcal O\) | local outcome-event presheaf over \(\mathcal C\) | lower-base candidate |
| \(\mathcal I\) | admissible inheritance transitions between contexts | lower-base candidate |
| \(\mathcal R\) | facticization/readout witness relation | lower-base candidate |
| \(\mathcal D\) | stable distinguishability relation | lower-base candidate |

Candidate derived objects:

| Object | Derivation requirement |
|---|---|
| global history \(H\) | admissible inheritance traces, not a primitive realized global ontology |
| event algebra \(\mathcal E\) | local context algebras plus successful gluing, not a primitive global algebra |
| global section / global fact table | allowed only if local sections glue |
| obstruction / holonomy | derived from failed gluing or nontrivial context cycles |
| carrier | minimal faithful representation of local facticity and distinguishability |
| probability/readout measure | theorem obligation, not primitive probability |
| metric spacetime | clock/source projection after inheritance and coarse-graining |

Base rule:

```text
No Primitive Global Structure:
  no primitive global fact table;
  no primitive Hilbert carrier;
  no primitive metric spacetime.
```

Migration boundary:

The executable v6 verifier still locks \((H,\mathcal E,\mathsf M,\mathcal I)\)
as the current carrier-neutral core. Replacing it with \(\mathfrak B_0\)
requires a new verifier gate proving that the old core is recovered as a
readout-facing derived interface, or explicitly marking the old contract as a
superseded scaffold.

Current finite-QM readout scaffold:

$$
\mathfrak T_{\mathrm{QM\ scaffold}}=(H,\mathcal E,\mathsf M,W,\Gamma_I,\mathcal I)
$$

| Symbol | Meaning | Status |
|---|---|---|
| \(W:H\to\mathbb C\) | coherent history weight | QM carrier import / readout scaffold |
| \(\Gamma_I\) | inherited distinguishability kernel | core positivity assumption |

The scaffold is useful for executable QM gates, but it is not a derivation of
complex scalars, Hilbert space, the Born rule, or first-principles
\(\hbar_I\). Those are theorem obligations or blocked/bridge objects until a
carrier-neutral derivation is supplied.

Inheritance act:

$$
I_\eta:
(W,\Gamma,\mathsf M)
\mapsto
(W_\eta,\Gamma_\eta,\mathsf M_\eta)
$$

Minimally:

$$
\Gamma_\eta=\Gamma\circ K_\eta
$$

with:

$$
K_\eta\succeq0,\quad K_\eta(h,h)=1
$$

Primitive update spectrum:

`sections/61-primitive-update-spectrum.md`

---
