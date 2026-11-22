# Which differences can a particle experiment see?

A candidate may match a table of charges, an intensity or a flux ratio for
several physically different reasons. These four probes give the checker
examples of **observations that separate two assignments** and **observations
that cannot**. None turns a graph label into a laboratory particle.

| Question | Observable | Surviving ambiguity |
| --- | --- | --- |
| Does swapping the electron's two neutral-current weights matter? | A polarized electron beam measures a **signed** asymmetry. Electron-only unpolarized forward/backward data determine a squared asymmetry in the stated pole model. | An internal charge table alone does not identify a laboratory helicity or fix the coupling strengths. |
| Does the solar flux reaching the detector contain an active non-electron component? | SNO's charged-current, elastic and neutral-current reactions have different calibrated flavor responses. | The three rates cannot separate muon from tau flux, identify coherence, or count sterile states without further assumptions. |
| Can relative reactor spectra distinguish a propagation clock? | PROSPECT compares energy-bin populations across baselines. | A common multiplicative suppression cancels. An arbitrary circuit depth is not a distance in metres. |
| Could changing separately addressed plates distinguish readout mechanisms? | A three-arm **simulated intervention** exceeds the bound for access to at most two of three independently chosen local bits. | Mechanisms accessing all three bits are not bounded that way. This was not an experiment on a solar or reactor beam. |

### Handedness: a sign that total rates lose

The [polarized-electron probe](probe_polarized_z_electron.py) retains the
same 16-mask carrier and the same externally assigned lepton labels. Exchanging
only the two laboratory helicity weights preserves their sum. At a factorizing
spin-one pole with the stated real-effective-coupling and angular assumptions,
the electron-only forward/backward asymmetry is 3 A_e²/4. The
[LEP electron result](https://arxiv.org/html/hep-ex/0509008), 0.0145 ± 0.0025,
therefore calibrates the **magnitude**, not the sign. The
[SLD polarized-beam measurement](https://arxiv.org/html/hep-ex/0004026)
found **+0.15138 ± 0.00216**, and the independently measured
[OPAL electron asymmetry from tau polarization](https://arxiv.org/html/hep-ex/0103045)
was **+0.1454 ± 0.0108 (stat) ± 0.0036 (syst)**, using a V−A tau decay
model. We do not combine these as independent Gaussian constraints. The
script reproduces the raw selected SLD counting asymmetries but not the
polarimeter calibration, detector corrections or the pole extraction.

### Active solar neutrinos, not an identification of the propagation law

The [SNO probe](probe_solar_active_flux.py) replays the published yields,
normalizations and correlations in [the detailed analysis, Tables 18–20](https://arxiv.org/html/nucl-ex/0610020).
In units of one million per cm² per second the simple difference NC−CC is
3.329. A statistical Gaussian projection of all three rounded yields gives
3.373 ± 0.450. Neither is the collaboration's [direct joint result](https://arxiv.org/html/nucl-ex/0204008),
**3.41 ± 0.45 (stat) +0.48/−0.45 (syst)**, for the non-electron active
flux under standard responses and the imposed boron-8 shape. The reported
5.3σ is theirs, not a new significance computed by this checker.

For equal incident flavor populations and matched spectra, a coherent
three-mode map, a fresh classical random choice, and an already mixed source
give exactly the same normalized CC, ES and NC responses: **1/3, 6559/15000,
and 1**. Even a perfect return after a second operation would not rule out a
classical swap with a retained hidden register. Those examples establish
identifiability limits; they are not fitted accounts of the solar data.

### Short-baseline reactors: the normalization is part of the test

The [reactor replay](probe_reactor_relative_clocks.py) uses the
[final PROSPECT-I release](https://arxiv.org/html/2406.10408), not unfolded
survival probabilities. The observed bins are background-subtracted and
have experimental uncertainties. With the optional unmodified
[source-data archive](https://arxiv.org/src/2406.10408v2), its relative
central-shape calculation agrees within **0.000161 event** across five
periods, six baseline groups and 33 prompt-energy bins, after a common
normalization for each period. That is closeness to a published numerical
table, not precision on a physical flux. A covariance diagnostic using
explicit proposed weights gives **831.49**, not the collaboration's null
statistic of about **829.57**. The discrepancy is unresolved. There is no
IDT confidence level or exclusion; [STEREO](https://arxiv.org/html/2210.07664)
is a separate experiment, not a replication of a native-clock prediction.

A permanently bright state and a three-phase clock with one bright phase
and a uniform initial phase have different absolute responses (1 versus
1/3), yet **exactly identical relative baseline shapes**. A biased initial
phase can change the shape in a synthetic control. Real use of that
contrast would require an independently fixed propagation length/energy law,
source preparation, detector response and a validated uncertainty calculation.

### A deliberately different intervention

In the [three-arm circuit](probe_three_arm_setting_contacts.py), all three
local plate bits are chosen independently *after* heralding. Score a point
for identifying the odd bit, zero for uniform triples, losses and wrong
answers. All eight bit strings stay in the denominator. Over 2,187
deterministic depth-two decision trees the classical maximum is **4/8**;
independent shared randomness cannot raise a convex maximum. The existing
six-rail circuit, with prepared intensities 1/2,1/4,1/4, sign plates and
coherent recombination, gives **5/8 per herald** (5/16 per original source
attempt for the displayed preparation). Recording the path and ignoring
the record reduces this to 1/4. Reading all three classical settings gives
6/8. Thus the discriminator tests **access to settings**, not classical
physics in general. The circuit is an application of
[amplitude amplification](https://arxiv.org/abs/quant-ph/0005055); no claim
of a new algorithm, measured violation, or derived Born rule is intended.

Run the offline controls with
`python3 -B -m scripts.replay_primitive_probe_campaign --bundle particle_observation_contrasts`.
For the optional reactor data use
`python3 -B -m scripts.probe_reactor_relative_clocks --archive /path/to/2406.10408v2.tar.gz`.
The archive hash is pinned in the script; it is not downloaded by the checker.
