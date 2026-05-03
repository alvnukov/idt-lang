## 1. Primitive Structure

Basic protostructure:

$$
\mathfrak T=(H,\mathcal E,\mathsf M,W,\Gamma_I,\mathcal I)
$$

| Symbol | Meaning | Status |
|---|---|---|
| \(H\) | possible histories / event bundles | primitive |
| \(\mathcal E\subseteq2^H\) | event algebra | primitive |
| \(\mathsf M\) | admissible readout contexts | primitive |
| \(W:H\to\mathbb C\) | coherent history weight | readout primitive |
| \(\Gamma_I\) | inherited distinguishability kernel | primitive |
| \(\mathcal I\) | admissible inheritance acts | primitive/dynamics |

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
