# Pedalino Real Data Import Report v3.2

## Source

- fixture: `pedalino_2026_sodium_nanoparticle_interferometry`
- dataset DOI: `10.5281/zenodo.17502163`
- article DOI: `10.1038/s41586-025-09917-9`
- source record: https://zenodo.org/records/17502163

## Import Result

- import_status: `real_data_import_complete`
- scans_imported: 95
- points_total: 3895
- mean_mass_da_from_mass_spectrum_window: 168940
- tau_single_spacing_s: 0.00622627
- tau_two_spacing_s: 0.0124525
- delta_x_proxy_m: 1.33e-07

## Extracted Raw Visibility Anchor

- best_scan: `Sodium_int_powerscan_55_s1.dat`
- V_obs_raw_fit: 0.0975351
- sigma_V_raw_fit: 0.00698315
- phase_rad: -2.40076
- baseline_counts: 3155.01
- residual_rms_counts: 95.924

## Bound Gate

- lambda_I_bound_status: `blocked_missing_V_env`
- missing_for_lambda_bound: `V_env`, `frozen_tau_policy`, `frozen_delta_x_policy`

No `lambda_I` bound is emitted by v3.2 import. The imported raw visibility
is an observed data anchor, not an environment-corrected residual.
