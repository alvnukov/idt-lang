## 108. Two-Path Interference Result

This section records the first finite QM-front result intended for direct
comparison with a standard interference formula.

The target is not to assume quantum mechanics. The target is to compute the
two-path fringe from the actualization kernel:

$$
\mathcal A(A,B)
=
\sum_{h\in A,h'\in B}
W(h)\overline{W(h')}\Gamma_I(h,h').
$$

Status:

`two_path_interference_result_initialized`

### 108.1. Two alternatives

Take two alternatives \(h_0,h_1\). A controllable phase shift \(\phi\) on the
second alternative changes only the second weight:

$$
W_\phi(h_0)=W_0,
\qquad
W_\phi(h_1)=e^{i\phi}W_1.
$$

The open two-path actualization measure is:

$$
\mu_\phi(\{0,1\})
=
\mathcal A_\phi(\{0,1\},\{0,1\}).
$$

The complementary output is represented by the shifted phase \(\phi+\pi\). The
finite readout probability is therefore:

$$
P_+(\phi)
=
\frac{\mu_\phi(\{0,1\})}
{\mu_\phi(\{0,1\})+\mu_{\phi+\pi}(\{0,1\})}.
$$

This is a context readout, not a global probability measure.

Status:

`two_path_context_probability_defined`

### 108.2. Derived fringe formula

Let:

$$
D
=
\mathcal A(\{0\},\{0\})
+
\mathcal A(\{1\},\{1\}),
$$

and:

$$
Z
=
W_0\overline{W_1}\Gamma_I(0,1).
$$

Then:

$$
\mu_\phi(\{0,1\})
=
D+2\operatorname{Re}(Ze^{-i\phi}).
$$

The complementary denominator is \(2D\), so:

$$
P_+(\phi)
=
\frac12
+\frac{\operatorname{Re}(Ze^{-i\phi})}{D}.
$$

Define:

$$
V=\frac{2|Z|}{D},
\qquad
\phi_0=\arg Z.
$$

Then:

$$
\boxed{
P_+(\phi)
=
\frac12
+\frac{V}{2}\cos(\phi-\phi_0)
}
$$

or equivalently:

$$
P_+(\phi)
=
\frac12
\left[
1
+V\cos(\phi-\phi_0)
\right].
$$

For \(\phi_0=0\):

$$
P_+(\phi)
=
\frac12(1+V\cos\phi).
$$

This is the standard two-output interference fringe shape, derived here from
bilinear actualization.

Status:

`two_path_fringe_formula_derived_from_actualization`

### 108.3. Executable comparison gate

The verifier gate:

`two_path_interference_fringe`

does not use the fringe formula to compute the readout. It computes:

$$
\mu_\phi,
\qquad
\mu_{\phi+\pi},
\qquad
P_+(\phi)
$$

directly from \((W,\Gamma_I)\). It then compares the result against a declared
known ideal table.

The current manifest:

`theory_verifier_manifest_v6_0.json`

uses:

$$
W_0=W_1=\frac1{\sqrt2},
\qquad
\Gamma_I=
\begin{pmatrix}
1 & 0.8\\
0.8 & 1
\end{pmatrix}.
$$

The derived visibility is:

$$
V=0.8.
$$

The computed table is:

| phase \(\phi\) | computed \(P_+(\phi)\) | ideal comparison |
|---:|---:|---:|
| \(0\) | \(0.9\) | \(0.9\) |
| \(\pi/2\) | \(0.5\) | \(0.5\) |
| \(\pi\) | \(0.1\) | \(0.1\) |
| \(3\pi/2\) | \(0.5\) | \(0.5\) |

No \(\hbar\), Schrodinger equation, Hilbert-space state vector postulate, or
Born rule is used as an input to compute this table.

Status:

`two_path_fringe_gate_registered`

### 108.4. Relation to experiments

The result matches the standard ideal form measured in two-path interferometry:

$$
P(\phi)=\frac12(1+V\cos\phi).
$$

The parameter \(V\) is not fitted after the table is computed. In this finite
gate it is the coherence magnitude already present in the actualization kernel.
In an experimental comparison, \(V\) is the independently measured visibility
of the prepared interferometer context.

Status:

`known_two_path_interference_formula_matched`

### 108.5. Limits

Closed in this finite gate:

1. cosine fringe shape from bilinear actualization;
2. visibility from \(|\Gamma_I(0,1)|\);
3. complement-output normalization;
4. no use of \(\hbar\) or Schrodinger dynamics;
5. no use of Born rule as a primitive.

Open:

1. continuous detector screen geometry;
2. propagation kernel that predicts \(\phi(x)\) from path length;
3. matter-wave de Broglie scale;
4. Bell/CHSH probability bridge;
5. experimental residual beyond standard QM.

Status:

`two_path_interference_result_closed_finite`
