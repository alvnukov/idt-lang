## 136. SPARC Rotation Data Gate

Status:

`real_data_residual_gate`

This section replaces the previous purely synthetic galactic survival window
with one real rotation-curve point from SPARC.

Source:

`SPARC. I. Mass Models for 175 Disk Galaxies with Spitzer Photometry and Accurate Rotation Curves`

Local files:

1. `data/sparc/raw/Rotmod_LTG.zip`
2. `data/sparc/raw/SPARC_Lelli2016c.mrt`

The verifier reads the downloaded zip file directly. The current finite gate uses:

$$
\texttt{DDO154\_rotmod.dat},\qquad \text{data row }10.
$$

The gate also checks the SHA-256 hash of `Rotmod_LTG.zip` before reading the
row, so the result is tied to a fixed downloaded artifact.

The raw row is:

$$
R=4.94\ \mathrm{kpc},
\quad
V_{\mathrm{obs}}=48.20\ \mathrm{km/s},
\quad
V_{\mathrm{gas}}=16.93\ \mathrm{km/s},
\quad
V_{\mathrm{disk}}=6.89\ \mathrm{km/s},
\quad
V_{\mathrm{bul}}=0.
$$

### 136.1. No-fit calculation

This gate does not fit the galaxy. It fixes a conventional demonstration
stellar mass-to-light factor:

$$
\Upsilon_{\mathrm{disk}}=0.5,
\qquad
\Upsilon_{\mathrm{bul}}=0.
$$

Then:

$$
a_{\mathrm{obs}}
=
\frac{V_{\mathrm{obs}}^2}{R},
$$

and:

$$
a_{\mathrm{bar}}
=
\frac{
V_{\mathrm{gas}}^2
+\Upsilon_{\mathrm{disk}}V_{\mathrm{disk}}^2
+\Upsilon_{\mathrm{bul}}V_{\mathrm{bul}}^2
}{R}.
$$

The verifier computes in the native SPARC units
\((\mathrm{km/s})^2/\mathrm{kpc}\):

$$
a_{\mathrm{obs}}
=
470.2914979757085,
$$

$$
a_{\mathrm{bar}}
=
62.82610323886638,
$$

$$
a_{\mathrm{miss}}
=
a_{\mathrm{obs}}-a_{\mathrm{bar}}
=
407.46539473684214,
$$

$$
\mathcal R_{\mathrm{SPARC}}
=
\frac{a_{\mathrm{obs}}}{a_{\mathrm{bar}}}-1
=
6.485606678288621.
$$

This is the empirical object that a future residual theory must explain. It is
not a fitted prediction yet.

### 136.2. Why this matters

The screened slip candidate previously had only a scale-window gate:

$$
\mathcal R(L_\odot)\le \epsilon_\odot,
\qquad
0.1\le\mathcal R(L_g)\le1.
$$

That was a survival test, not data contact.

The new gate anchors the same front to an actual observed acceleration
residual:

$$
\texttt{sparc\_rotation\_curve\_data\_I}
\Rightarrow
\texttt{observed\_centripetal\_acceleration\_I},
\quad
\texttt{baryonic\_rotation\_acceleration\_I}.
$$

The theory may now ask a sharper question:

$$
\mathcal R_{\mathrm{screen}}(L;\Theta_I)
\stackrel{?}{\longrightarrow}
\mathcal R_{\mathrm{SPARC}}(R)
$$

without changing \(\Theta_I=(A,L_t,n)\) after seeing the galaxy point.

### 136.3. Finite gate

Finite gate:

`sparc_ddo154_outer_baryonic_residual_demo`

Gate type:

`sparc_baryonic_residual_point`

The gate fails if:

1. the source zip checksum changes;
2. the raw SPARC row read from the zip does not match the declared values;
3. \(V_{\mathrm{obs}}^2/R\) is not recomputed correctly;
4. the baryonic acceleration is not recomputed correctly;
5. the missing acceleration or residual fraction is altered.

### 136.4. Accepted and not accepted

Accepted:

`sparc_rotation_curve_data_I = experimental_gate`.

Accepted:

one real SPARC point exposes a large no-fit baryonic residual.

Not accepted:

`screened_slip_residual_candidate_I = observed`.

Not accepted:

`dark matter explained`.

Not accepted:

the chosen \(\Upsilon_{\mathrm{disk}}\) as a derived primitive.

### 136.5. Next required upgrade

Section 137 turns this single-point residual into a full DDO154 residual
packet and checks whether the current screened demo profile is even large
enough. The remaining work is to turn the packet into a pre-registered
multi-galaxy gate:

1. choose a fixed SPARC subset before evaluating residual quality;
2. derive or externally declare \(\Upsilon_{\mathrm{disk}}\) policy;
3. map each radius to a theory-side scale \(L_I(R)\);
4. compute predicted residuals from one fixed \(\Theta_I\);
5. reject the candidate if the same \(\Theta_I\) fails the held-out points.

Until that is done, this section is a real-data anchor, not a validated
galactic theory.
