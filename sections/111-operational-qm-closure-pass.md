## 111. Operational QM Closure Pass

This section is the large QM pass requested after the finite readout gates.

It does not claim that the whole of quantum mechanics is derived. It closes the
finite operational layer that the current protolanguage can honestly close:

$$
\text{amplitude packet}
\Rightarrow
\text{unitary context/network}
\Rightarrow
\text{projective readout}
\Rightarrow
\text{standard finite QM tables}.
$$

Status:

`operational_qm_closure_pass_initialized`

### 111.1. Finite unitary network

The verifier now accepts a normalized amplitude packet:

$$
\psi_0,
$$

and a finite sequence of unitary update/context maps:

$$
U_n\cdots U_2U_1.
$$

It computes:

$$
\psi_n=U_n\cdots U_1\psi_0,
\qquad
P_i=|\psi_{n,i}|^2.
$$

This closes finite interferometer/network calculation at the operational level.
The manifest gate `unitary_network_probability_demo` uses a Hadamard-phase-
Hadamard network and checks the output table.

Status:

`finite_unitary_network_probability_executable`

### 111.2. Projective measurement update

The verifier now accepts a projective readout:

$$
\{P_i\},
\qquad
P_i^2=P_i,
\qquad
P_i^\dagger=P_i,
\qquad
\sum_iP_i=I.
$$

It computes:

$$
p_i=\langle\psi|P_i|\psi\rangle.
$$

For each nonzero outcome it also checks repeatability of the facticized
post-readout state:

$$
\psi_i'
=
\frac{P_i\psi}{\sqrt{p_i}},
\qquad
\langle\psi_i'|P_i|\psi_i'\rangle=1.
$$

This is the finite ideal-measurement limit. It does not yet derive irreversible
environmental facticity, but it makes the projective update executable.

Status:

`finite_projective_measurement_update_executable`

### 111.3. Bell from setting angles

The Bell front now has a stronger finite bridge than copied tables.

For the singlet spin sector, setting angles define:

$$
E(x,y)=-\cos(\alpha_x-\beta_y).
$$

The corresponding zero-marginal outcome table is:

$$
P(a,b|x,y)
=
\frac14
\left[
1-ab\cos(\alpha_x-\beta_y)
\right].
$$

The verifier builds the four tables from the four setting angles, checks
no-signalling, then computes:

$$
S=E_{00}+E_{01}+E_{10}-E_{11}.
$$

For:

$$
\alpha_0=0,\quad
\alpha_1=\frac\pi2,
\quad
\beta_0=\frac\pi4,\quad
\beta_1=-\frac\pi4,
$$

it verifies:

$$
|S|=2\sqrt2.
$$

This is still a finite singlet-sector gate. It closes the setting-angle to
CHSH-table bridge, but it does not derive spin representation theory or the
physical apparatus angles from primitive update dynamics.

Status:

`finite_spin_bell_angle_model_executable`

### 111.4. Current manifest

The current manifest:

`theory_verifier_manifest_v6_0.json`

adds:

1. `unitary_network_probability_demo`;
2. `projective_measurement_update_demo`;
3. `spin_bell_angle_model_demo`.

Together with sections 108-110, the finite QM layer now checks:

1. Born/context readout;
2. two-path interference;
3. Sorkin \(I_3=0\);
4. marker/eraser visibility;
5. unitary measurement contexts;
6. finite unitary networks;
7. projective readout repeatability;
8. Bell/CHSH from probabilities, amplitudes, and singlet setting angles.

Status:

`operational_qm_manifest_registered`

### 111.5. Closure boundary

Closed:

finite operational QM readout.

Not closed:

1. \(\hbar_I\) as an independently computed action-phase constant;
2. de Broglie scale \(p\lambda=h_I\);
3. Schrodinger equation as a continuum generator;
4. physical derivation of apparatus context maps \(U_K\);
5. environmental irreversibility / collapse from primitive facticity dynamics;
6. new residual prediction beyond standard QM.

Therefore the correct status is:

`finite_operational_qm_closed`

not:

`full_qm_derived`.

Status:

`qm_operational_closure_honest_boundary_declared`
