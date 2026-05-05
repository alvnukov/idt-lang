## 171. QM Experiment Language Ledger

Status:

`qm_experiment_language_ledger_initialized`

This section records how known quantum-mechanical experiments are described in
the IDT language.

The purpose is not to claim that full quantum mechanics has been derived from
first principles. The purpose is to test whether the same IDT primitives can
organize a large class of QM experiments without changing vocabulary from case
to case.

The ledger is manifest-backed. The verifier reads `qm_experiments` from
`theory_verifier_manifest.json` and checks that each entry has:

1. a known coverage status;
2. a standard QM result;
3. nonempty mappings for all six IDT primitives;
4. a stable invariant;
5. an explicit claim boundary;
6. existing finite gates when the status is `executable_gate`;
7. a proposed gate id when the status is `gate_candidate`.

Status:

`qm_experiment_coverage_machine_guard_registered`

The required vocabulary is:

1. `event`;
2. `distinguishability`;
3. `inheritance of distinguishability`;
4. `readout context`;
5. `facticity`;
6. `stable invariant`.

In the formal packet:

$$
\mathfrak T=(H,\mathcal E,\mathsf M,W,\Gamma_I,\mathcal I),
$$

the experiment is read as:

| Experimental role | IDT object |
|---|---|
| possible alternatives | histories or event bundles \(H,\mathcal E\) |
| preparation | initial weights \(W(h)\) and inherited kernel \(\Gamma_I\) |
| controllable operation | inheritance act \(I_\eta\in\mathcal I\) |
| apparatus setting | admissible readout context \(\mathsf M\) |
| observed outcome | facticized event in the selected context |
| reproducible result | stable invariant or finite gate |

Status:

`qm_experiment_translation_rule_declared`

### 171.1. Claim Boundary

The ledger has four statuses:

| Status | Meaning |
|---|---|
| `executable_gate` | the current verifier computes the finite readout or invariant |
| `idt_language_description` | the experiment has a direct IDT translation, but no dedicated gate yet |
| `gate_candidate` | the next finite verifier check is clear enough to implement |
| `not_claimed` | the experiment needs a missing primitive bridge or residual model |

An experiment in this ledger does not upgrade:

`full_QM_I = target`

to:

`full_QM_I = derived`.

It may support the weaker claim:

`QM_experiment_language_coverage_I = derived_conditional`.

The verifier check is intentionally weaker than a physics derivation and
stronger than prose. It proves only that the experiment has been placed inside
the IDT vocabulary and that claimed executable coverage points to real manifest
gates.

Status:

`qm_experiment_ledger_boundary_declared`

### 171.2. Experiments Already Covered By Executable Gates

| Experiment class | Standard result | IDT description | Current status |
|---|---|---|---|
| Born/context probability tests | probabilities are normalized context weights | events \(A_i\) acquire \(\mu(A_i)\) from actualization; the readout context normalizes the table | `executable_gate`: `born_context_probability_table_demo` |
| two-slit / Mach-Zehnder interference | \(P(\phi)=\frac12(1+V\cos\phi)\) | two alternatives are not fully facticized; visibility is inherited distinguishability magnitude in \(\Gamma_I\) | `executable_gate`: `two_path_interference_fringe_demo` |
| finite \(I_3=0\) actualization | no third-order interference in bilinear QM | three event bundles keep pairwise interference but no primitive triple interference term | `executable_gate`: `actualization_demo_i3_zero` |
| triple-slit / Sorkin parameter | normalized third-order term is zero within tolerance | the stable invariant is \(I_3=0\) under the bilinear actualization measure | `executable_gate`: `triple_path_sorkin_parameter_demo` |
| which-way marking | visibility decreases when path distinguishability increases | marker inheritance increases effective distinguishability between alternatives | `executable_gate`: `marker_eraser_visibility_demo` |
| quantum eraser | conditioned readout can recover visibility | a later context changes which distinctions are read out as factual, without rewriting the prepared histories | `executable_gate`: `marker_eraser_visibility_demo` |
| unitary measurement context | probabilities change with basis/context | \(U_K\) maps an amplitude packet into the selected readout context | `executable_gate`: `unitary_measurement_context_demo` |
| finite interferometer network | cascaded unitary maps produce output tables | a sequence of admissible context/update maps propagates the amplitude packet before readout | `executable_gate`: `unitary_network_probability_demo` |
| projective repeatability | repeating the same ideal measurement gives the same outcome | facticity is stable inside the same readout context after projection | `executable_gate`: `projective_measurement_update_demo` |
| Stern-Gerlach single-axis readout | a prepared spin-axis eigenpacket gives the corresponding two-output context table | magnet orientation selects the readout context; same-axis facticity is repeatable | `executable_gate`: `stern_gerlach_context_readout_demo` |
| sequential Stern-Gerlach | same-axis repetition is stable, incompatible-axis insertion rebuilds the partition | a nonselective incompatible context dephases the old factual partition before the final readout | `executable_gate`: `sequential_sg_noncommuting_context_demo` |
| Rabi oscillation | a driven two-level system transfers population sinusoidally | the inheritance act rotates amplitude weight between two facticizable outcomes in a fixed readout context | `executable_gate`: `two_level_update_oscillation_demo` |
| delayed choice | a late apparatus choice selects path or interference statistics | the final readout context chooses which distinguishability partition becomes factual | `executable_gate`: `delayed_context_partition_demo` |
| Ramsey interferometry | two separated pulses produce phase-dependent population fringes | clock histories inherit a relative phase before final population-context readout | `executable_gate`: `ramsey_clock_phase_demo` |
| Aharonov-Bohm phase | enclosed flux shifts interference phase with no local path force | a closed holonomy is inherited as a stable phase relation between alternatives | `executable_gate`: `ab_holonomy_phase_demo` |
| Aharonov-Bohm flux period | the phase is periodic with \(\Phi_0=h/|q|\) | the declared charge/action bridge closes the finite flux-period readout | `executable_gate`: `ab_flux_period_demo` |
| photoelectric threshold | emission appears only above the work-function threshold | the declared action-frequency anchor selects when emission becomes a facticizable event | `executable_gate`: `action_frequency_threshold_demo` |
| spectroscopy lines | one action-frequency anchor maps multiple transition energies to frequencies | a shared anchor is inherited across spectral readout contexts without per-line refit | `executable_gate`: `spectral_anchor_consistency_demo` |
| tunneling through a barrier | a finite forbidden barrier has nonzero suppressed transmission | the blocked alternative keeps suppressed inherited weight until detector readout | `executable_gate`: `barrier_transmission_demo` |
| quantum Zeno effect | frequent same-context readouts inhibit transition | repeated facticity refreshes the survival context and suppresses update away from it | `executable_gate`: `repeated_context_zeno_demo` |
| Hong-Ou-Mandel interference | identical photons suppress coincidence counts | indistinguishable two-particle alternatives inherit exchange symmetry at the beamsplitter readout | `executable_gate`: `bosonic_indistinguishability_demo` |
| antibunching / single-photon source tests | zero-delay coincidences are suppressed below the classical bound | one source-context fact excludes simultaneous double facticity in the same run | `executable_gate`: `single_quantum_facticity_demo` |
| entanglement swapping | a Bell readout conditions correlations between remote systems | the Bell context facticizes a subensemble and transfers the correlation table | `executable_gate`: `conditional_inheritance_swap_demo` |
| teleportation | Bell readout plus correction reconstructs the input state at the target | context structure is transferred to the target branch without copying an extra instance | `executable_gate`: `context_transfer_no_cloning_demo` |
| no-cloning | nonorthogonal unknown states cannot be universally duplicated | preserving all future readout overlaps conflicts with cloned inner-product closure | `executable_gate`: `no_cloning_context_invariance_demo` |
| GHZ/Mermin contextuality | deterministic context products obstruct a global value assignment | incompatible product contexts cannot be combined into one factual assignment table | `executable_gate`: `multipartite_contextuality_demo` |
| Kochen-Specker contextuality | compatible-context constraints obstruct noncontextual global assignment | a finite context hypergraph has no global fact table satisfying every local context | `executable_gate`: `ks_contextuality_obstruction_demo` |
| Leggett-Garg temporal facticity | temporal correlations violate a macrorealist assignment bound | two-time readouts cannot be merged into one noninvasive temporal fact table | `executable_gate`: `temporal_facticity_demo` |
| weak measurement | small pointer shifts extract partial information below full facticity | partial distinguishability is inherited without crossing the declared facticity threshold | `executable_gate`: `partial_facticity_readout_demo` |
| quantum random walk | unitary graph propagation yields an interference distribution | coin/shift inheritance keeps path alternatives coherent until final position readout | `executable_gate`: `unitary_graph_walk_demo` |
| Bell/CHSH probability table | no-signalling marginals and \(|S|\le2\sqrt2\) | no global factual context is assumed; only context-indexed joint readouts are checked | `executable_gate`: `bell_chsh_table_demo` |
| Bell/CHSH from amplitudes | probability tables arise from amplitudes | joint outcome probabilities are read out from amplitude packets rather than copied as primitive probabilities | `executable_gate`: `bell_chsh_from_amplitudes_demo` |
| singlet angle CHSH | \(E(\alpha,\beta)=-\cos(\alpha-\beta)\), \(|S|=2\sqrt2\) | apparatus settings select readout contexts; the stable invariant is the context-indexed correlation table | `executable_gate`: `spin_bell_angle_model_demo` |
| calibrated action-phase consistency | one anchor supports \(E=\hbar\omega\), \(p=\hbar k\), \(\phi=S/\hbar\) | `calibrated_hbar_I` is a declared action-phase readout anchor, not a primitive derivation | `executable_gate`: `hbar_known_gate_holdout_demo` |
| decoherence and recoverability loss | environment marking suppresses coherence; recoverability loss separates erasure from stable facticity | environment inheritance increases distinguishability and makes factual records stable only past a recoverability threshold | `executable_gate`: `premeasurement_decoherence_demo`, `recoverability_loss_demo` |

These gates support the claim that IDT can already express and check a finite
operational QM layer.

They do not prove:

1. first-principles numerical \(\hbar_I\);
2. primitive derivation of all apparatus contexts;
3. irreversible collapse from primitive dynamics;
4. a beyond-standard-QM residual.

Status:

`qm_executable_experiment_coverage_recorded`

### 171.3. Current Gate-Candidate Queue

| Experiment class | IDT description | Needed finite gate |
|---|---|---|
| none in the current manifest | all registered QM experiment rows now point to finite verifier gates | n/a |

This does not mean the experiments are derived from first principles. It means
the currently registered experiment rows have executable finite readout or
obstruction gates.

Future QM rows may still enter as `gate_candidate` when the next finite checker
is clear but not implemented.

Status:

`qm_language_only_experiment_coverage_recorded`

### 171.4. First Implemented Two-State Gate Cluster

The first new gate cluster is the finite two-state context family:

1. `stern_gerlach_context_readout_demo`;
2. `sequential_sg_noncommuting_context_demo`;
3. `two_level_update_oscillation_demo`.

The central gate is sequential Stern-Gerlach.

It tests three core IDT ideas at once:

1. facticity is stable inside the same readout context;
2. facticity is not a global context-independent property;
3. incompatible readout contexts rebuild the admissible distinguishability
   partition.

The standard finite result is:

$$
SG_z(+)\rightarrow SG_z
\Rightarrow
P(z+)=1,\quad P(z-)=0,
$$

but:

$$
SG_z(+)\rightarrow SG_x\rightarrow SG_z
\Rightarrow
P(z+)=\frac12,\quad P(z-)=\frac12.
$$

The IDT reading is:

1. the first \(SG_z\) context facticizes a \(z\)-partition;
2. the \(SG_x\) context reads a different admissible partition;
3. after the \(x\)-context, the old \(z\)-distinguishability is no longer a
   stable factual invariant;
4. the final \(SG_z\) readout produces the standard half-half table.

This is a strong QM gate because it directly tests context-dependent facticity
without introducing new constants, SPARC data, gravity bridges, or fitted
parameters.

The neighboring Rabi gate checks the same two-state vocabulary in an update
mode rather than a measurement-context mode: a fixed inheritance act transfers
amplitude weight between two facticizable outcomes and the population table is
read out at declared times.

Status:

`two_state_qm_gate_cluster_executable`

### 171.5. Phase And Interferometer Gate Cluster

The second implemented cluster promotes finite phase/readout experiments:

1. `delayed_context_partition_demo`;
2. `ramsey_clock_phase_demo`;
3. `ab_holonomy_phase_demo`;
4. `ab_flux_period_demo`.

This cluster tests a different pressure point from the two-state measurement
cluster. The checked invariant is not just context-dependent facticity, but a
stable phase relation that becomes visible only in the selected final readout
context.

The delayed-choice gate checks two readout contexts for the same prepared
two-path packet:

$$
\text{open path context}\Rightarrow P=(1/2,1/2),
$$

but:

$$
\text{closed interference context}\Rightarrow P=(1,0).
$$

The Ramsey gate checks the same structure in a clock-history form:

$$
P_0(\varphi)=\frac12(1+\cos\varphi),\quad
P_1(\varphi)=\frac12(1-\cos\varphi).
$$

The AB gates deliberately remain finite closure checks. They verify:

$$
\Delta\phi_{AB}=q\Phi_B/\hbar
$$

and:

$$
|q|\Phi_0/h=1.
$$

They do not derive \(q\), \(h\), or \(\hbar\) from IDT primitives.

Status:

`phase_interferometer_qm_gate_cluster_executable`

### 171.6. Threshold And Repeated-Context Gate Cluster

The third implemented cluster promotes finite threshold and suppressed-update
experiments:

1. `action_frequency_threshold_demo`;
2. `spectral_anchor_consistency_demo`;
3. `barrier_transmission_demo`;
4. `repeated_context_zeno_demo`.

The photoelectric and spectroscopy gates are calibrated-anchor checks. They
verify that one declared action-frequency anchor is used consistently:

$$
E=hf,\quad K_{\max}=\max(0,hf-W),
$$

and:

$$
\Delta E_i=h f_i
$$

for all declared spectral lines.

The tunneling gate checks a finite suppressed-history readout:

$$
T=\exp(-2\kappa a),\quad R=1-T,
$$

with \(0<T<1\) in a classically forbidden finite barrier.

The Zeno gate checks repeated compatible readout for a finite two-state update:

$$
P_{\mathrm{surv}}(N)=
\left[\cos^2\left(\frac{\theta}{2N}\right)\right]^N,
$$

and verifies that survival increases for the declared higher readout counts.

These gates do not derive the material work function, atomic levels, barrier
profile, or continuous measurement limit.

Status:

`threshold_repeated_context_qm_gate_cluster_executable`

### 171.7. Quantum-Information Facticity Gate Cluster

The fourth implemented cluster promotes finite quantum-information readouts:

1. `bosonic_indistinguishability_demo`;
2. `single_quantum_facticity_demo`;
3. `conditional_inheritance_swap_demo`;
4. `context_transfer_no_cloning_demo`;
5. `no_cloning_context_invariance_demo`.

The HOM gate checks the finite overlap rule:

$$
P_{\mathrm{coinc}}=\frac12(1-\Lambda),
$$

with \(\Lambda=1\) giving a zero-coincidence dip.

The antibunching gate computes:

$$
g^{(2)}(0)=\frac{N_{ab}N}{N_aN_b}
$$

from declared coincidence counts and checks the declared single-quantum bound.

The swapping gate treats the Bell readout as a conditioning fact and verifies
the remote Bell-correlation table selected by that fact. The teleportation gate
checks finite Bell-branch correction for one target state. The no-cloning gate
checks the inner-product obstruction:

$$
\langle\psi|\phi\rangle
\neq
\langle\psi|\phi\rangle^2
$$

for nonorthogonal unknown states.

These gates are still finite protocol checks. They do not derive photon
sources, Bell-state analyzers, classical communication, or a universal physical
network.

Status:

`quantum_information_facticity_gate_cluster_executable`

### 171.8. Contextuality, Temporal, And Graph Gate Cluster

The fifth implemented cluster promotes the remaining registered QM experiment
rows:

1. `multipartite_contextuality_demo`;
2. `ks_contextuality_obstruction_demo`;
3. `temporal_facticity_demo`;
4. `partial_facticity_readout_demo`;
5. `unitary_graph_walk_demo`.

The GHZ/Mermin gate checks a finite parity obstruction: every local observable
appears an even number of times across the declared contexts, but the product
of the context products is \(-1\), so a global pre-existing value assignment is
impossible.

The KS gate checks the same obstruction style as a finite context hypergraph:
an odd number of contexts each require one true projector, while every
projector appears an even number of times.

The Leggett-Garg gate computes:

$$
K=C_{12}+C_{23}-C_{13}
$$

and checks violation of the declared macro-facticity bound.

The weak-measurement gate checks pointer shift and partial facticity:

$$
\Delta x=g A_w,
$$

while verifying that disturbance and distinguishability stay below the declared
full-facticity thresholds.

The graph-walk gate computes a finite Hadamard walk distribution from coin and
shift updates, then compares the final position table.

These gates are finite executable reconstructions. They do not derive all
operator algebras, physical projector sets, macroscopic invasiveness,
weak-measurement apparatus dynamics, or general graph-walk theory.

Status:

`contextuality_temporal_graph_qm_gate_cluster_executable`

### 171.9. Universal Pattern Audit

The next level is not to add more one-off gates. The registered `35` finite
QM gates now reduce to six primary universal patterns:

| Universal pattern | Experiments | Compiler target |
|---|---:|---|
| contextual probability and facticized readout | 6 | `context_readout_kernel` |
| coherent alternatives and interference readout | 9 | `coherent_alternative_kernel` |
| phase/action anchor and periodic closure | 5 | `phase_action_anchor_kernel` |
| finite update, reset, suppression, and survival | 4 | `finite_update_survival_kernel` |
| composite correlation and contextual obstruction | 7 | `contextual_correlation_obstruction_kernel` |
| record stability, context transfer, and noncopyability | 4 | `record_transfer_noncopyability_kernel` |

The manifest now records this as `qm_universal_patterns`. The verifier checks:

1. every registered QM experiment belongs to exactly one primary universal
   pattern;
2. every executable QM finite gate is covered by at least one pattern;
3. every pattern declares the same six operations:
   `event_packet`, `distinguishability_partition`, `inheritance_update`,
   `readout_context`, `facticity_rule`, and `stable_invariant`;
4. every pattern has an explicit compiler target and claim boundary.

This changes the interpretation of the `35/35` result.

The stronger statement is not:

`IDT has 35 separate QM explanations`.

The stronger statement is:

`IDT has six candidate universal mechanisms that compile the current 35 finite
QM readouts`.

These patterns are still candidates for a future universal QM bench/compiler.
They are not yet proof that the IDT primitive layer derives the Hilbert-space
formalism, physical apparatus, or dimensional constants.

The first bench runner is now executable:

```bash
python3 scripts/qm_bench.py --json
```

It compiles the manifest pattern audit into a kernel summary:

1. `6` universal kernels;
2. `35` registered QM experiments;
3. `35` executable QM finite-gate references;
4. the shared operation sequence used by every pattern family.

This is not yet a full simulator. It is the first reproducible compiler surface
for turning the gate ledger into a smaller set of universal QM mechanisms.

Status:

`qm_universal_pattern_audit_registered`

Status:

`qm_universal_bench_compiler_added`

### 171.10. QM Usefulness Claim

The current honest usefulness claim is:

IDT can describe the current registered class of known QM experiments as
variations of six finite mechanisms built from one process:

$$
\text{unknown alternatives}
\Rightarrow
\text{inherited distinguishability}
\Rightarrow
\text{readout context}
\Rightarrow
\text{facticity}
\Rightarrow
\text{stable invariant}.
$$

This supports IDT as a useful QM reconstruction language before it becomes a
completed first-principles derivation of quantum mechanics.

The stronger confirmation target is:

1. compile the six pattern families into shared kernels rather than one-off
   experiment gates;
2. keep `full_QM_I = target`;
3. keep `hbar_I = blocked` unless the action scale is independently derived;
4. count failed gates and rejected translations as useful exclusions.

Status:

`qm_language_usefulness_claim_bounded`
