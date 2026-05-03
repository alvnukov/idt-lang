## 27. Experimental Gate Ledger

This section prevents post-hoc fitting.

Each accepted bridge must declare:

1. validated formula;
2. domain of validity;
3. experimental anchor;
4. proto quantity being tested;
5. residual symbol;
6. current status.

No residual may be introduced after comparing to the target dataset unless it is declared as a failed gate.

Status:

`experimental_gate_ledger_initialized`

### 27.1. Ledger rule

For a gate \(G_k\), define:

$$
\mathcal R_k
=
O_k^{\mathrm{proto}}
-
O_k^{\mathrm{known}}.
$$

Acceptance requires:

$$
|\mathcal R_k|
\le
\epsilon_k
$$

on the declared domain:

$$
\mathcal D_k.
$$

The tolerance \(\epsilon_k\) must come from the selected experimental source or from an explicitly declared conservative bound.

Status:

`gate_residual_rule`

### 27.2. QM gates

| Gate | Validated formula | Domain | Experimental anchor | Proto quantity | Residual | Current status |
|---|---|---|---|---|---|---|
| Born readout | \(P_i=\mu_i/\sum_j\mu_j\) | admissible decohered context | standard quantum probability tests | \(\mu(A)\) | \(\mathcal R_{\mathrm{Born}}\) | theorem block added; context admissibility required |
| two-path visibility | \(V=2\sqrt{p_ap_b}|\Gamma_{ab}|/(p_a+p_b)\) | controlled two-path interference | interferometry / which-way tests | \(\Gamma_{ab}\) | \(\mathcal R_V\) | formula derived in bilinear sector |
| Sorkin | \(I_3=0\) | bilinear actualization | triple-slit bounds | \(I_3\) | \(\mathcal R_{I_3}\) | theorem block added |
| Bell/CHSH | \(|S|\le2\sqrt2\) with no-signalling marginals | bipartite admissible contexts | Bell tests | \(P(a,b|x,y)\) | \(\mathcal R_{\mathrm{Bell}}\) | compatibility only; bridge incomplete |
| AB phase | \(\Delta\phi=q\Phi_B/\hbar\) | gauge/phase readout | Aharonov-Bohm interferometry | \(\Theta_{q,I}\) | \(\mathcal R_{\mathrm{AB}}\) | conditional bridge |

Status:

`qm_gate_ledger_initialized`

### 27.3. Clock and weak-gravity gates

| Gate | Validated formula | Domain | Experimental anchor | Proto quantity | Residual | Current status |
|---|---|---|---|---|---|---|
| gravitational redshift | \((\nu_A-\nu_B)/\nu_B\approx[\Phi(A)-\Phi(B)]/c^2\) | weak static field | clock redshift tests | \(\chi,\Phi_I\) | \(\mathcal R_z\) | derived from clock-rate ratio |
| SR time dilation | \(d\tau/dt=\sqrt{1-v^2/c^2}\) | flat/boost domain | particle clocks / atomic clocks | \(c_I,\tau_I\) | \(\mathcal R_{\mathrm{SR}}\) | required fixed point |
| LPI | clock species agree on redshift coefficient | local position invariance domain | multi-clock comparisons | \(\alpha_C-\alpha_{C'}\) | \(\mathcal R_{\mathrm{LPI}}\) | residual gate |
| WEP | \(\eta_{AB}=2|a_A-a_B|/|a_A+a_B|\) bounded | weak free fall | Eotvos/free-fall tests | \(\epsilon_{\mathrm{EP},I}\) | \(\mathcal R_{\mathrm{WEP}}\) | active/passive/source gate added |
| Newtonian free fall | \(\ddot x=-\nabla\Phi\) | slow weak field | laboratory/solar-system dynamics | \(\Phi_I\) | \(\mathcal R_a\) | conditional on interval readout |
| Poisson source | \(\Delta\Phi=4\pi G\rho_m\) | weak static source | inverse-square/source tests | \(\alpha_I,\sigma_{\Phi,I}^G\) | \(\mathcal R_{\mathrm{P}}\) | conditional candidate only |

Status:

`clock_gravity_gate_ledger_initialized`

### 27.4. Spatial-curvature and PPN gates

| Gate | Validated formula | Domain | Experimental anchor | Proto quantity | Residual | Current status |
|---|---|---|---|---|---|---|
| light bending | \(\Delta\theta=2(1+\gamma)GM/(c^2b)\) | weak solar-system lensing | solar deflection / VLBI-type tests | \(\gamma_I^{\mathrm{PPN}}\) | \(\mathcal R_\gamma\) | requires \(\gamma_I\to1\) |
| Shapiro delay | delay coefficient \(\propto1+\gamma\) | weak solar-system delay | radar / spacecraft timing | \(\gamma_I^{\mathrm{PPN}}\) | \(\mathcal R_{\mathrm{Shapiro}}\) | target |
| perihelion | PPN \(\beta,\gamma\) combination | weak orbital correction | Mercury / ephemerides | \(\beta_I,\gamma_I\) | \(\mathcal R_{\mathrm{peri}}\) | target |
| lensing/dynamics split | \(\Phi_{\mathrm{lens}}=(\Phi+\Psi)/2\) | weak lensing | lensing vs dynamics | \(\Psi_I-\Phi_I\) | \(\mathcal R_{\mathrm{slip}}\) | residual declared |
| no-slip sector | \(\Psi=\Phi\) when anisotropic stress vanishes | no-residual weak sector | GR weak-field consistency | \(\Pi_I^{ij}\) | \(\mathcal R_{\mathrm{slip}}\) | support conditions only |

Status:

`ppn_gate_ledger_initialized`

### 27.5. Constants and no-refit gates

| Gate | Validated formula | Domain | Experimental anchor | Proto quantity | Residual | Current status |
|---|---|---|---|---|---|---|
| Planck action scale | \(\Delta\phi=\Delta S/\hbar\) | action-phase readout | spectroscopy / matter waves / phase tests | \(\hbar_I\) | \(\mathcal R_\hbar\) | universal calibration, not numerical derivation |
| fine structure | \(\alpha=e^2/(4\pi\epsilon_0\hbar c)\) or equivalent | EM quantum readout | spectroscopy/scattering/Josephson/Hall | \(\alpha_{\mathrm{em},I}\) | \(\mathcal R_\alpha\) | bridge target |
| vacuum impedance | \(\alpha=Z_0/(2R_K)\) | EM/vacuum response | impedance/Hall/Josephson routes | \(Z_{0,I},R_{K,I}\) | \(\mathcal R_Z\) | numerical response open |
| Newton constant | \(G_I=c_I^4/(4\pi\alpha_I)\) after calibration | weak gravity source readout | Newtonian/solar-system gates | \(a_{EF}\to\alpha_I\) | \(\mathcal R_G\) | prediction chain defined; \(a_{EF}\) open |
| weak-gravity closure ladder | \(a_{EF},\lambda_I,\sigma_{\Phi,I}^G\Rightarrow G_I,\rho_m\) | weak-gravity Mode C route | redshift/free-fall/WEP/lensing gates | \(\mathcal R_{\mathrm{WG}}\) | \(\mathcal R_{\mathrm{WG}}\) | architecture integrated; numerical inputs open |
| weak-gravity input ledger | \(G_I=c_I^4D_S/(4\pi\kappa_{\chi,I}n_Lx_0^2\ell_0^2)\) | minimal link ensemble | no hidden \(G_N\) input | \(x_0,\kappa_{\chi,I},n_L,\ell_0\) | \(\mathcal R_{\mathrm{input}}\) | anti-fit ledger added |

Status:

`constants_gate_ledger_initialized`

### 27.6. Current verification status

Current accepted status:

1. formulas and domains are declared structurally;
2. residual symbols are declared;
3. no-refit rule is explicit;
4. numerical tolerances \(\epsilon_k\) are not yet populated from a source table;
5. therefore the ledger is a design-control closure, not yet a completed empirical validation.

Next required verification task:

populate \(\epsilon_k\) and selected data sources for each gate before claiming quantitative confirmation.

Status:

`quantitative_validation_not_yet_complete`
