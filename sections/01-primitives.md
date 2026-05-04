## 1. Primitive Structure

Carrier-neutral core:

$$
\mathfrak T_0=(H,\mathcal E,\mathsf M,\mathcal I)
$$

| Symbol | Meaning | Status |
|---|---|---|
| \(H\) | possible histories / event bundles | primitive |
| \(\mathcal E\subseteq2^H\) | event algebra | primitive |
| \(\mathsf M\) | admissible readout contexts | primitive |
| \(\mathcal I\) | admissible inheritance acts | primitive / dynamics |

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
