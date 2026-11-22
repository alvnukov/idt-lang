# A width measures couplings, not a count of slots

The finite carrier has sixteen addressed states, but does not yet specify
a light mass spectrum or a neutral weak current. The following is a
**conditional forward comparison** for models which actually supply both.
It does not bind the sixteen-state candidate to a Z boson.

## Which data enter?

| Source | Reported quantity | What is shared |
| --- | --- | --- |
| [Original combined LEP lineshape, §7.2.2](https://arxiv.org/html/hep-ex/0509008#Ch7.S2.SS2) | Invisible-to-single-charged-lepton width ratio 5.943 ± 0.016; effective neutrino number 2.9840 ± 0.0082 with the then-used SM ratio 1.99125 ± 0.00083 | Universality of charged leptons and an external single-neutrino normalization. These are fitted widths, not tagged neutrino counts. |
| [Janot & Jadach, Table 9](https://arxiv.org/html/1912.02067#S6.T9) | 2.9963 ± 0.0074 after luminosity and theory updates; single-neutrino ratio 1.99060 ± 0.00021 | A reanalysis of the **same LEP data**, not a second independent constraint. |
| [ATLAS recoil measurement](https://arxiv.org/html/2312.02789#S1.E2), [HEPData Table 1](https://doi.org/10.17182/hepdata.151651.v1/t1) | Invisible width 506 ± 2 (stat.) ± 12 (syst.) MeV | Different events and method. The conversion from the missing-to-dilepton ratio to MeV still uses external charged-lepton widths. |

The [offline replay](probe_z_width_data_replay.py) starts from the rounded
three-parameter fit and its correlations in [Table 12](https://arxiv.org/html/1912.02067#A2.T12).
It obtains 2.996370 ± 0.007406. That agrees at the precision supported by
the printed parameters, not at every last digit. It is not an event-level fit
or an independent measurement. The [small numeric receipt](../data/published_observations/z_invisible_width_v1.json)
distinguishes measured summaries from conversion inputs.

## What can a candidate predict?

Supply distinguishable, effectively massless invisible Dirac species and
a dimensionless Hermitian matrix C for their left-handed Z current in the
mass basis. Each ordered particle–antiparticle final state is a distinct
channel, with the same kinematics and the supplied standard lepton
normalization. Its rate in single-neutrino units is the squared modulus of
its entry. With no additional invisible contribution:

`N_eff = sum_(i,j) |C_ij|² = tr(C† C)`.

This comparison does **not** assume that every Hermitian example has a
complete electroweak realization. Three unit couplings give three; four
unit couplings give four. But four diagonal couplings (1, 1, 3/5, 4/5)
also give three. Mixing one active state with a sterile one in a fully
accessible four-state space gives three when both off-diagonal channels are
retained. Removing them in that representation gives 1587/625 instead.
Conjugating a current or changing a relative phase need not alter the width.
Invisible but sterile states and the number of families are not counted
by this observable. Near-threshold masses, altered charged-lepton couplings,
right-handed currents and other missing-energy contributions require new
forward models.

```sh
python3 -B -m scripts.probe_z_width_data_replay
python3 -B scripts/screen_hypotheses.py --batch-file data/neutral_current_width_controls.json --max-cases 16 --no-cache
```

The checker computes the model value **before comparing** it to the data.
It reports the signed residual relative to the quoted LEP uncertainty as
descriptive arithmetic only. The ATLAS comparison separately displays a
hybrid MeV scale using the original LEP single charged-lepton width and
the updated SM ratio; calibration uncertainties have not been propagated.
No combined significance, tail probability, fit or discovery verdict is
returned. The last two controls deliberately have an unknown mass regime
or no physical bridge and return **unsupported**; the example batch thus
has a nonzero exit status. Insufficient budget returns **inconclusive**
without presenting a partial sum as a width.
