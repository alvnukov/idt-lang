# Two-port conservation and conditional reconstruction

The checked cluster reconstructs positive quadratic readout from a supplied
finite-rejoin, reversible two-port contract. A lower-premise theorem extracts a
pairing while retaining an additive linear remainder. The observable quotient
then supports faithful generated arithmetic, canonical conjugation and quadratic
gains. Each conclusion carries the hypotheses of its Lean declaration.

The authoritative task records are `twoPortConservationPairingOrigin`,
`finiteRejoinReversibleQuadraticOrigin` and
`finiteRejoinObservableNativeReadoutChecked`. Each has conditional-kernel status
and parent-accepted review. The broader
`finiteRejoinObservationalQuotientNativeArithmetic` task remains in formalization.

## Pairing under the minimal conservation contract

Supply an additive commutative monoid `V`, additive endomorphisms `A,B,C,D`,
and a real readout `W`. Require surjectivity of both `A` and `B`. For each `z`,
require a pair `(x,y)` whose output under the complete two-port map is `(z,0)`.
For every pair `x,y`, require

```text
W(A(x)+B(y)) + W(C(x)+D(y)) = W(x) + W(y).
```

`base_independent_of_conservation` proves that the second additive difference
of `W` is independent of its base preparation. Centered polarization gives

```text
P(u,v) = (W(u+v)-W(u)-W(v)+W(0))/2
L(x)   = W(x)-W(0)-P(x,x)
W(x)   = W(0)+P(x,x)+L(x).
```

`Polarization.symmetric`, `Polarization.add_left`, `Polarization.add_right`
and `remainder_add` prove symmetry, biadditivity and additivity of `L`.
`i3_eq_vacuum` gives the seven-term algebraic `I3=W(0)`, with `I3=0` when
`W(0)=0`. The physical identification with a Sorkin experiment remains open.

The compiled natural-number control has `A=B=id`, `C=D=0` and `W(n)=n`.
It obeys this contract with nonnegative response and zero vacuum, while `P=0`
and `L(1)=1`. Its two-port outputs lie on the first axis. The identity-mixer
control with `W(n)=n^3` has full mixer surjectivity and first-axis reachability,
a failed `B`-surjectivity premise and `I3(1,1,1)=6`.

The complete pairing artifact and its controls are in
[TwoPortConservationPairing.lean](../Proofs/QMClosure/TwoPortConservationPairing.lean).

## Full-domain finite-rejoin contract

Supply an additive commutative monoid `V` and additive endomorphisms `a,b`.
Require `a+b=id` and `a^n=b^n` for one positive natural `n`. Require surjectivity
of the complete map

```text
F(x,y) = (a(x)+b(y), b(x)+a(y))
```

on all of `V × V`. Supply `W(0)=0`, `W(p)≥0` for every `p`, and conservation
`W(a(x)+b(y))+W(b(x)+a(y))=W(x)+W(y)` for every pair `x,y`.
These quantifiers concern the whole supplied carrier and pair domain.

`Gate.additive_inverses` derives an inverse for every original monoid element.
`Gate.carrierGroup` preserves the original addition and zero in the derived
group. `half_responses` gives the two branch gains `W(a(p))=W(b(p))=W(p)/2`.
`parallelogram_of_reversible_half_conservation` supplies the parallelogram law.
`reconstruct` packages positive quadraticity and the same/cross responses

```text
W((a²+b²)(p)) = 0
W((2ab)(p))   = W(p).
```

`Reconstruction.null_translate`, `integer_square` and `third_order_zero`
give null insertion, integer-square gains and algebraic `I3=0`.
`prepared_count_weight` proves, for every preparation and natural `m,n`,
`W(n·a(p)+m·b(p))=((n²+m²)/2)W(p)`.
`prepared_count_order` gives the corresponding componentwise count order.
The equation for `c=2ab` expresses readout invariance. Integer doubling has
its separate square gain `W(2p)=4W(p)`.

The core and separate vacuum, positivity and accessibility controls are in
[FiniteRejoinReversibleQuadraticReadout.lean](../Proofs/QMClosure/FiniteRejoinReversibleQuadraticReadout.lean)
and [FiniteRejoinQuadraticReadoutControls.lean](../Proofs/QMClosure/FiniteRejoinQuadraticReadoutControls.lean).

## Observable equality and generated native arithmetic

The null subgroup is `N={x | W(x)=0}` in the reconstructed additive group.
`projection_eq_iff` identifies equality in `V/N` with `W(x-y)=0`.
`projection_eq_iff_all_reference_tests` identifies that same equality with
`W(x+z)=W(y+z)` for every additive reference `z`.
The quotient has a descended positive quadratic readout with zero response
exactly at the zero class.

On this observable carrier, `same_coefficients` and `cross_coefficients` give
`A²+B²=0` and `AB+BA=id`. `operation_square` gives swap-square and
`native_fourth_rejoin` gives exact fourth branch equality.

Supply a preparation `p` with `W(p)>0` for the faithful arithmetic adapter.
`sourceResponse` normalizes by division by `W(p)` and derives its serial
response law. `generatedEvaluation_injective` supplies faithful evaluation.
`generatedArithmeticEquiv` identifies the descended native generated ring
with its Gaussian-dyadic arithmetic image. `canonicalConjugation` swaps the
branches and is involutive.

The generated operators live in the additive-endomorphism algebra of the
observable carrier. Literal identification with the original generated
operator quotient `R0/kerDelta` remains an outstanding obligation.
The artifact is [FiniteRejoinObservableQuotient.lean](../Proofs/QMClosure/FiniteRejoinObservableQuotient.lean).

## Native gain, conjugation and paired echo

`operator_normal_form` covers every native generated operator by a form
`H^k(z₁+z₂U)`, with integer `z₁,z₂`, native half `H` and native phase `U`.
`gain_value` gives the numerical gain `(z₁²+z₂²)/4^k`.
`weight_action` proves the same gain on every native preparation.
`gain_reference_independent`, `gain_mul` and `gain_conjugation` give reference
independence, composition multiplicativity and conjugation invariance.
Faithful operator evaluation and numerical gain have separate claims, with
phase degeneracy retained by the numerical gain.

`pairing_operator_adjoint` identifies canonical conjugation as adjoint for
the derived real polarization. `value_paired_echo` gives its exact arithmetic
operator identity. For any generated `T,S` with `gain(T)+gain(S)=1`,
`normalized_paired_echo` proves `T·conj(T)+S·conj(S)=id`.
All reference-normalized conclusions use `W(p)>0` with internal normalization.
Physical adjoint, time reversal and detector realization remain open.
The artifact is [NativeOperatorQuadraticReadout.lean](../Proofs/QMClosure/NativeOperatorQuadraticReadout.lean).

## Controls and remaining obligations

The canonical complex norm-square model witnesses the complete nonzero
contract. Separate compiled controls retain conservation while violating
vacuum normalization or positivity. The nonnegative-real half mixer satisfies
the remaining period-one contract and has only diagonal outputs, exposing the
whole-pair accessibility premise.

The unbalanced complex control has transparent invertible branches, an onto
mixer and universal norm-square conservation. Its branches fail to rejoin at
every positive exponent, its half-gain and same-null conclusions fail, and its
readout remains quadratic. The hidden-sector `ℂ × ℂ` control satisfies the
complete core contract with period twelve and a normalized visible readout.
Its original carrier has a nonzero same-branch output and unequal fourth
powers in the invisible coordinate. Both certificates are in
[FiniteRejoinCarrierChoiceControls.lean](../Proofs/QMClosure/FiniteRejoinCarrierChoiceControls.lean).

Five broad-continuation obligations remain unencoded in the checked substage.
They are divisibility `4 | n` for a nonzero readout, positive-history
accessibility, literal `R0/kerDelta`, the ambient null-ideal countercontrol
and the combined P8 conservation-omission certificate.

The additive carrier, full-domain accessibility, finite rejoin and lossless
conservation retain independent physical-origin obligations. Scalar extension,
completion, normalized-detector realization, Born actualization, Hilbert
reconstruction, dynamics, composites, full QM, GR and physical-scale origins
remain open. The overall operational-origin research goal remains active.
