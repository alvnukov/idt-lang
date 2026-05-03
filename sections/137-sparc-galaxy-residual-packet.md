## 137. SPARC Galaxy Residual Packet

Status:

`real_data_packet_and_candidate_capacity_bound`

Section 136 anchored the front to one real SPARC point. This section upgrades
that anchor to the full DDO154 rotation-curve packet and asks a stricter
question:

> Is the current screened residual candidate even large enough to explain the
> measured acceleration residuals?

The answer for the current demo profile is no.

### 137.1. Fixed data policy

Dataset:

`SPARC Rotmod_LTG.zip`

Galaxy:

`DDO154`

Rows:

all 12 data rows in `DDO154_rotmod.dat`

Stellar mass-to-light policy for this demonstration:

$$
\Upsilon_{\mathrm{disk}}=0.5,
\qquad
\Upsilon_{\mathrm{bul}}=0.
$$

This \(\Upsilon\) policy is not derived by the theory. It is a declared
external data-reduction convention for this gate.

### 137.2. Residual vector

For each radius:

$$
\mathcal R_i
=
\frac{a_{\mathrm{obs},i}}{a_{\mathrm{bar},i}}-1,
$$

where:

$$
a_{\mathrm{obs},i}
=
\frac{V_{\mathrm{obs},i}^2}{R_i},
$$

and:

$$
a_{\mathrm{bar},i}
=
\frac{
V_{\mathrm{gas},i}^2
+\Upsilon_{\mathrm{disk}}V_{\mathrm{disk},i}^2
+\Upsilon_{\mathrm{bul}}V_{\mathrm{bul},i}^2
}{R_i}.
$$

The verifier computes:

$$
N=12,
\qquad
R_{\min}=0.49\ \mathrm{kpc},
\qquad
R_{\max}=5.92\ \mathrm{kpc}.
$$

Residual range:

$$
\min_i\mathcal R_i=1.1217605799746315,
$$

$$
\max_i\mathcal R_i=6.842377551859201,
$$

$$
\langle\mathcal R\rangle=4.581090117622583.
$$

This packet is now a hard empirical object. A future galaxy-sector model must
either explain it or fail.

### 137.3. Capacity test for the current screened demo profile

The current screened profile used in the survival gate was:

$$
\mathcal R_{\mathrm{screen}}(L)
=
A
\frac{(L/L_t)^n}{1+(L/L_t)^n},
\qquad
A=1.
$$

Therefore:

$$
\max_L\mathcal R_{\mathrm{screen}}(L)=1.
$$

But the DDO154 packet requires:

$$
\max_i\mathcal R_i=6.842377551859201.
$$

So the capacity ratio is:

$$
\frac{1}{6.842377551859201}
=
0.1461480300408564.
$$

The finite gate records:

`declared_status = insufficient`

This is a negative result, and it is useful. It prevents the theory from
silently upgrading a survival toy profile into a claimed galaxy explanation.

### 137.4. Finite gates

Finite gate:

`sparc_ddo154_residual_packet_demo`

Gate type:

`sparc_residual_packet`

It fails if:

1. the SPARC zip checksum changes;
2. the row count changes;
3. the radius range changes;
4. any residual fraction in the 12-row vector changes;
5. min, max, or mean residual changes.

Finite gate:

`screened_sparc_capacity_bound_demo`

Gate type:

`screened_sparc_capacity`

It fails if:

1. the declared capacity ratio is not recomputed correctly;
2. a candidate with \(A<\max\mathcal R_{\mathrm{SPARC}}\) is declared
   sufficient.

### 137.5. Accepted and not accepted

Accepted:

`sparc_galaxy_residual_packet_I = experimental_gate`.

Accepted:

`screened_sparc_capacity_test_I = derived_conditional`.

Accepted:

current \(A=1\) screened demo profile is insufficient for DDO154 if it is
interpreted as the full missing acceleration fraction.

Not accepted:

`screened_slip_residual_candidate_I = observed`.

Not accepted:

changing \(A\) after seeing SPARC.

Not accepted:

dark matter explained.

### 137.6. Next required upgrade

The next cluster must choose between two honest routes:

1. reject the current \(A=1\) screened profile as a galaxy explanation and
   search for a derived amplitude source;
2. reinterpret the profile so it is not the full acceleration residual and
   derive the missing mapping to \(\mathcal R_{\mathrm{SPARC}}\).

Section 138 turns the first route into an explicit amplitude lower-bound and
no-postfit provenance gate. Both routes require pre-registration before checking
more galaxies.
