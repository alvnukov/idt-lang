# Dataset Binding Report v3.1

## dibartolomeo_2024_levitated_optomechanics_collapse_bounds

- title: Experimental bounds on linear-friction dissipative collapse models from levitated optomechanics
- year: 2024
- type: collapse_like_bounds_comparison
- status: comparison_fixture
- can_compute_lambda_bound: False

## eibenberger_2013_molecules_exceeding_10000_amu

- title: Matter-wave interference of particles selected from a molecular library with masses exceeding 10000 amu
- year: 2013
- type: matter_wave_visibility
- status: incomplete_for_numerical_lambda_bound
- can_compute_lambda_bound: False
- missing: V_obs, V_env, sigma_V, tau_s, delta_x_m

## gerlich_2011_large_organic_molecules

- title: Quantum interference of large organic molecules
- year: 2011
- type: matter_wave_visibility
- status: incomplete_for_numerical_lambda_bound
- can_compute_lambda_bound: False
- missing: V_obs, V_env, sigma_V, tau_s, delta_x_m

## kim_2000_delayed_choice_quantum_eraser

- title: Delayed 'Choice' Quantum Eraser
- year: 2000
- type: quantum_eraser
- status: conceptual_benchmark_incomplete_for_visibility_bound
- can_compute_lambda_bound: False

## pedalino_2026_sodium_nanoparticle_interferometry

- title: Probing quantum mechanics with nanoparticle matter-wave interferometry
- year: 2026
- type: matter_wave_visibility
- status: partially_quantitative_fixture
- can_compute_lambda_bound: False
- missing: V_obs, V_env, sigma_V, tau_s, delta_x_m
- derived_rough:
  - single_spacing_time_s_at_160mps: 0.00614375
  - two_spacing_time_s_at_160mps: 0.0122875
  - mass_kg_at_172kDa: 2.856127194552e-22

## sinha_2010_triple_slit_science

- title: Ruling Out Multi-Order Interference in Quantum Mechanics
- year: 2010
- type: higher_order_interference
- status: benchmark_complete_for_structural_test
- can_compute_lambda_bound: False
