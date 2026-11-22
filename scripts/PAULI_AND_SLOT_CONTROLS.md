# Pauli and slot controls: what the four probes test

These exact executable controls separate four conditional questions. They
do not form a derivation in which the output of one probe supplies the
hypotheses of the next. The accompanying analytic arguments are not Lean
proofs.

1. **Collision support** — [collective Pauli frame](probe_collective_pauli_frame.py).
   Supply a positive normalized state on an ordered tensor power, identical
   collective mode transformations, complete mode access (including internal
   labels), and number-resolving occupation readout. The bare setting plus
   disjoint edge-mixing settings give a pair frame whose kernel is the
   antisymmetric subspace. Zero mean pair collisions in every setting selects
   support in the fully antisymmetric power. With `m` copies and at least `m`
   modes, the leakage bound is `2E/m`, where `E` is the **sum of mean pair
   collision counts** across settings, not a click probability. One setting
   can miss a symmetric state, and orbital-only optics can miss total symmetry
   carried by hidden internal labels. The weighted projective 2-design is a
   separate, stronger frame: raw native modes fail its uniform-vector test;
   the encoded construction supplies extra phase control, preparation, and
   complete logical readout.
2. **Exchange sign** — [finite exchange relator](probe_exchange_sign_relator.py).
   Supply hard-core capacity, coherent number-preserving lifts, unchanged
   outside occupations, and `Z` calibrated to count the addressed occupation.
   Test that the one-particle relation `C X C† = Z` holds as a many-body word
   identity up to **one common scalar on the same fixed-number sector**. Empty
   and full addressed pairs can then be compared with two total occupations
   on four modes; the scalar cancels and the full/empty swap ratio is `−1`.
   Independent phases across total numbers would not cancel. An uncalibrated
   `Z` can counterfeit the relation, and a bosonic symmetric square satisfies
   it with swap `+1` on the one-in-each-mode state because `C` can mix in
   double occupations. Going from the local sign to a path-independent
   permutation action needs additional implementation-independence relations:
   spectator-blind swaps pass the local test but fail a fixed-number loop.
   The exterior lift passes that loop as a supplied comparator, not a unique
   lift or a consequence of one-particle agreement. If physical paths retain
   distinct histories, that agreement need not identify the many-body words.
3. **Exterior-family slot minimum** — [exterior slot minimality](probe_exterior_slot_minimality.py).
   Supply the full even exterior carrier on `n` complex slots, a continuous
   determinant-one block action, and two nonabelian blocks. Within this
   family, four slots are self-conjugate and five is the first size with a
   non-self-conjugate representation and vanishing local linear and cubic
   traces; its only split is `3+2` up to order. The ordinary `SU(2)` doublet
   parity test also passes. Interpreting the traces as anomalies supplies
   left Weyl fields and does not check all global anomalies. Removing the
   invariant vacuum gives 15 instead of 16 dimensions without changing the
   positive-degree traces or chirality witness. More strongly, a faithful
   **13-dimensional non-exterior four-slot** control cancels the tested
   anomalies and is chiral, with its net chirality in singlets. Neither the
   16-dimensional carrier nor a universal five-slot minimum follows from
   those tests.
4. **Quartic split selection** — [five-slot quartic selector](probe_five_slot_quartic_selector.py).
   Independently supply five real eigenvalues (or a Hermitian carrier), zero
   trace, a fixed nonzero second moment, and the quartic objective. The exact
   normalized quartic range is `[7/30, 13/20]`: minimizing a positive quartic
   term favors `3+2`, reversing its sign favors `4+1`, and a zero coefficient
   leaves the shape undetermined. An allowed cubic tilt defeats `3+2` even
   at fixed radius. A two-color complete-graph cut also balances the supplied
   slots but does so at other sizes as well. The quartic neither selects the
   slot count nor derives its objective or the exterior representation.

None of these results derives physical Pauli exclusion, spin-statistics,
creation laws or CAR, particle assignments, gauge symmetry or dynamics, or
full quantum mechanics.

From the repository root, replay the probes and the separate boundary checks:

```sh
python3 -B -O -m scripts.probe_collective_pauli_frame
python3 -B -O -m scripts.probe_exchange_sign_relator
python3 -B -O -m scripts.probe_exterior_slot_minimality
python3 -B -O -m scripts.probe_five_slot_quartic_selector
python3 -B -m unittest discover -s tests -p test_pauli_and_slot_controls.py
python3 -B -O -m unittest discover -s tests -p test_pauli_and_slot_controls.py
```
