# Reversible echo and scalar reflection boundaries

The checked controls separate three operational obligations behind the
rational count-order readout route. Genuine reversible undo can coexist with
a failed conjugate echo test. Conjugate undo and balanced detector output can
coexist with a raw branch total of one half. A transparent additive square-swap
gate can have reconstructed phase and half while its finite scalar image
admits no additive unital phase-reversing map. A small positive bridge states
exactly which return and accounting premises supply a nondegenerate echo.
[Reversible echo controls](../Proofs/QMClosure/ReversibleEchoAccountingBoundary.lean)
[Finite scalar reversal control](../Proofs/QMClosure/FiniteScalarReversalBoundary.lean)

## Supplied carrier and response laws

The first two controls use the supplied rational Gaussian carrier `Q x Q`,
with named multiplication, conjugation and unit

```text
(x,y) * (z,t) = (xz-yt, xt+yz),
conj(x,y) = (x,-y),
unit = (1,0),
N(x,y) = x^2+y^2.
```

Serial scalar products in these controls use the named Gaussian operation
`gmul`. A real raw response satisfies `WeightLaws` when it is nonnegative,
vanishes at zero, equals one at the unit, is multiplicative, preserves
conjugation, and satisfies adjacent natural-count order for every natural
count. Both responses constructed below satisfy all six laws. The rational
carrier, real codomain and coherent operations remain supplied mathematical
structure.
[Carrier and operations](../Proofs/QMClosure/RationalEchoRegularityControl.lean)
[WeightLaws and the existing selection theorem](../Proofs/QMClosure/RationalCountOrderReadout.lean)

## Actual undo and conjugate return are separate obligations

Set `a=(1/3,0)` and `b=(2/3,0)`. The two-port operation and its inverse are

```text
R(x,y) = (a*x+y, b*x-y),
U(x,y) = (x+y, b*x-a*y).
```

The checked identities `U(R(p))=p` and `R(U(p))=p` hold for every input pair.
The unit input splits into the two nonzero branches `a,b`. With the raw
response `w(z)=sqrt(N(z))`, their responses are `1/3` and `2/3`, so their raw
sum is one. The actual return row has coefficients `u=v=unit`, giving
`u*a+v*b=unit`.

The conjugate return instead evaluates to

```text
a*conj(a)+b*conj(b) = (5/9,0),
w(a*conj(a)+b*conj(b)) = 5/9.
```

Thus the actual inverse and the normalized nonzero branch responses coexist
with a failed normalized conjugate echo. The raw normalization checked here
concerns the displayed unit-input split. All-input raw conservation remains
a separate requirement.
[Two-sided inverse, raw normalization and echo failure](../Proofs/QMClosure/ReversibleEchoAccountingBoundary.lean)

## Conjugate undo and observed balance leave the raw scale open

Now set `a=(1/2,1/2)` and `b=(1/2,-1/2)`. The symmetric gate and reverse gate
are

```text
F(x,y) = (a*x+b*y, b*x+a*y),
U(x,y) = (b*x+a*y, a*x+b*y).
```

The coefficients satisfy `a+b=unit`, `a*a+b*b=zero` and
`a*b+b*a=unit`. The gate is transparent on every diagonal input, its square
swaps the ports, and both inverse compositions are the identity. Conjugation
exchanges `a,b`, and their scalar echo is the unit.

For `w4(z)=N(z)^2`, both nonzero branch responses equal `1/4`. Their raw
sum is `1/2`, while the scalar echo response is one. Define the explicit
context-normalized detector by

```text
p1(x,y) = w4(x)/(w4(x)+w4(y)),
p2(x,y) = w4(y)/(w4(x)+w4(y)).
```

The checked split context `(a,b)` gives detector values `(1/2,1/2)`.
The checked return context `(unit,zero)` gives `(1,0)`. These two evaluations
exhibit observed balance and deterministic return alongside a raw deficit.
The detector evidence in this cluster consists of these evaluated contexts.
The quartic response family already appears in the earlier normalized echo
controls. The contribution here is its explicit reversible gate, conjugate
undo and evaluated detector tests.
[Gate laws, quartic WeightLaws, raw deficit and detector evaluations](../Proofs/QMClosure/ReversibleEchoAccountingBoundary.lean)
[Earlier quartic family](../Proofs/QMClosure/NormalizedEchoReadoutControls.lean)

## Finite scalar phase reconstruction and reversal descent

Use the supplied scalar ring `ZMod 5`, coefficients `a=4`, `b=2`, and the
same symmetric gate and coefficient-swapped reverse gate. The gate is
additive, transparent on every diagonal input, squares to port exchange,
and has the stated two-sided inverse. Both coefficients are nonzero units.

The phase and half have the checked values

```text
g = 2*a^2 = 2,
g^2 = -1,
g^4 = 1,
g^3 = 3,
h = a*b = 3,
h+h = 1.
```

The existing `TransparentSwapRoot.reconstruct` theorem applies to the
coefficient endomorphisms in this example. The general reconstruction of
phase, half and cancellation is a prior result. This control instantiates
that reconstruction in a finite scalar image.
[Prior general reconstruction](../Proofs/QMClosure/TransparentSwapRoot.lean)
[Finite instantiation and evaluated scalar laws](../Proofs/QMClosure/FiniteScalarReversalBoundary.lean)

There is no additive unital map `J` on this scalar ring with `J(g)=g^3`.
Additivity and `J(1)=1` force `J(2)=2`, whereas `g^3=3`. The checked
coefficient-swap obstruction similarly excludes an additive unital map
sending `a` to `b`.

This finite example blocks a universal inference from the local gate laws
to conjugation on an arbitrary scalar image. Reversal descent needs separate
justification. Faithful generated arithmetic is one sufficient route.
The relevant semantic equality must be stable under reflection of histories.
[Phase-reversal and coefficient-swap obstructions](../Proofs/QMClosure/FiniteScalarReversalBoundary.lean)

## A one-row reciprocity and accounting bridge

For an arbitrary response `w`, supply nonzero branches `a,b`, return
coefficients `u,v`, and the following premises

```text
u*a+v*b = unit,
u = conj(a),
v = conj(b),
w(a)+w(b) = 1,
w(unit) = 1.
```

Then `NondegenerateEcho w` follows. The proof uses the supplied return row,
its one-column reciprocity and same-scale exhaustive accounting. The complete
assumption list is the displayed premises and branch nonzeroness. Whole-gate
invertibility, matrix unitarity, balanced calibration and all-input
conservation are unnecessary for this implication. With `WeightLaws`, the
existing count-order selection theorem then identifies `w` with `N` on the
supplied rational Gaussian carrier.
[Exact one-row bridge](../Proofs/QMClosure/ReversibleEchoAccountingBoundary.lean)
[Existing conditional readout selection](../Proofs/QMClosure/RationalCountOrderReadout.lean)

## Reproducing the checks

Run the registered targets sequentially from the repository root.

```bash
lake build Proofs.QMClosure.ReversibleEchoAccountingBoundary
lake build Proofs.QMClosure.FiniteScalarReversalBoundary
lake build Proofs.MetaLang.V8OperationalPrimitiveResearchLedger
```

All three registered targets passed their sequential builds. A shared
transitive-dependency audit selected declarations by their exact owning-module
metadata. It covered all 84 declarations across the two new proof modules,
including generated declarations. The module counts were 51 and 33, with zero
private declarations, zero local axioms and zero unsafe declarations. The exact
aggregate transitive axiom set was `propext`, `Quot.sound` and `Classical.choice`.

The audit exited successfully in 9.358 seconds. Both proof-source hashes and
the target-registration hash matched their frozen values before and after the
audit. All 45 checked-evidence citations in the accepted research task matched
their audited owning modules.

## Open operational obligations

The physical origins of return reciprocity, same-scale raw branch accounting
and reflection-stable semantic equality remain open. Conditional scalar,
generated-operator and source-specific faithfulness results are recorded in
[Calibrated branch-history faithfulness](195-calibrated-branch-history-faithfulness.md).
Their supplied bridges include raw response extensionality, stationary serial
gains and one native column normalization.

Native-circuit passivity, the initial history presentation, the finite-window
boundary and finite-history readout regularity remain separate analytic research
plans with empty checked evidence.

Physical Born readout, detector selection, event actualization, Hilbert and
spectral representation, dynamics, tensor and entanglement closure, and physical
scales remain open. This cluster records mathematical countermodels and a
conditional bridge within the supplied contracts.
[Authoritative operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
