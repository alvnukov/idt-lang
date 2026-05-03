# SPARC Data Anchor

This directory documents the first real-data gate used by the IDT verifier.
Raw SPARC files are not committed to git. Fetch them with:

```bash
python3 scripts/fetch_sparc_data.py
```

Source record:

`https://zenodo.org/records/16284118`

Downloaded files:

1. `raw/Rotmod_LTG.zip` - 175 SPARC rotation-curve mass-model files.
2. `raw/SPARC_Lelli2016c.mrt` - SPARC galaxy metadata table.

SHA-256:

1. `0a80cc90714828cc28b7dd57923576714d209f2490328c087c4a4ad607faf588`
   for `raw/Rotmod_LTG.zip`.
2. `5aa0501f6b0d881fa579030e315e7b5b6ef561a5bd3a07472f9929c7e5728243`
   for `raw/SPARC_Lelli2016c.mrt`.

Current verifier use:

`sparc_ddo154_outer_baryonic_residual_demo` reads `DDO154_rotmod.dat` from
`raw/Rotmod_LTG.zip` and recomputes one no-fit residual point. This is a data
anchor, not a fit and not a claim that the screened residual candidate explains
galaxy rotation curves.

`sparc_ddo154_residual_packet_demo` reads all 12 rows of `DDO154_rotmod.dat`
and recomputes the residual vector. `screened_sparc_capacity_bound_demo` records
that the current `A=1` screened demo profile is insufficient for the largest
DDO154 residual fraction.

`sparc_ddo154_amplitude_lower_bound_demo` records the resulting lower bound on
any full-residual screened amplitude, and `galaxy_residual_no_postfit_demo`
rejects amplitude provenance that uses SPARC residual data as its own source.

`sparc_amplitude_solar_transition_bound_demo` combines the DDO154 lower
amplitude with the solar residual bound. `old_screened_profile_solar_rejection_demo`
records that the old transition scale is excluded for the SPARC-minimum
amplitude.

`sparc_solar_galactic_corridor_demo` records that the SPARC-solar corridor is
nonempty. `sparc_no_fit_claim_status_demo` records that this is still not a
DDO154 fit because the radius-to-scale map and held-out validation are missing.

`sparc_proportional_radius_map_rejection_demo` tests the first explicit
radius-to-scale map candidate, \(L_I\propto R\), and rejects it against the full
DDO154 residual vector.

`sparc_baryonic_acceleration_power_map_demo` tests the next local map candidate
based on baryonic acceleration and rejects it as a near miss.
`sparc_inverse_residual_map_forbidden_demo` records that exact inverse maps
from the observed residual are post-fit contaminated.

`sparc_baryonic_exponent_family_scan_demo` scans the fixed diagnostic family
\(L_I\propto(a_{b,\mathrm{out}}/a_b)^q\) for
`q = [1.0, 1.5, 2.0, 2.5, 3.0]`. The best DDO154 member is `q=2.5`, with max
absolute residual error `0.7174826101020031`, but this is not a validation
claim. `sparc_q_selection_postfit_demo` marks q selection from DDO154 as
post-fit contaminated until q is fixed before held-out galaxy tests or derived
from primitives.

`sparc_q25_heldout_transfer_demo` freezes `q=2.5` and selects the first three
post-DDO154 rotmod files with at least 8 rows: DDO161, DDO168, and DDO170. It
rejects the transfer law with aggregate max absolute residual error
`4.476556241800259`. `sparc_heldout_selection_no_postfit_demo` verifies that
the held-out selection uses filename order and row count rather than residual
quality.
