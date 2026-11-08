# Normalized echo readout

A global continuous raw weight on the supplied complex algebra is selected as
`w(z) = normSq(z)` by multiplicativity, conjugate reversal and normalized echoes.
The result derives native two-port weight conservation under this mathematical
contract. Physical realization of the complex operations and echo contexts
remains an independent obligation.

## Normalized echoes select the quadratic weight

Let `w : Complex -> Real` be continuous and nonnegative, with `w(0) = 0`,
`w(1) = 1`, `w(ab) = w(a)w(b)` and `w(conj(a)) = w(a)`. Supply the echo law for
every algebraic pair satisfying `w(a) + w(b) = 1`.

```text
w(a conj(a) + b conj(b)) = 1.
```

Complex inverses first make the weight strictly positive away from zero.
The intermediate value theorem supplies a real scalar with weight `1/2`.
Its balanced echo forces `w(2) = 4`. Powers of two and continuity then supply
every positive real weight level. Common-scalar normalization extends the
echo law to every input pair.

```text
w(a conj(a) + b conj(b)) = (w(a) + w(b))^2.
```

The complex star identity and nonnegativity give the parallelogram law.
Existing polarization, continuity and conjugation then identify the weight
with `Complex.normSq`. Conservation follows for the supplied native coordinate
mixer. The normalized-pair premise is stated in terms of `w` itself, and the
proof proceeds directly through the intermediate value theorem and algebra.
[Weight selection and native conservation](../Proofs/QMClosure/NormalizedEchoReadout.lean)

| Supplied condition | Role or boundary |
| --- | --- |
| Global complex carrier, addition, multiplication and conjugation | Supply the algebra used in normalization and the star identity. |
| Global continuity | Supplies balanced and arbitrary positive scalar weight levels. |
| Every `w`-normalized algebraic echo pair | Extends normalized echo to the universal identity. Physical context coverage remains supplied. |
| Native coordinate mixer | Receives the derived conservation law. |
| Raw weight on the whole complex carrier | Can exceed one. In particular `w(2) = 4`. |

The scalar witnesses are mathematical points of the supplied carrier.
Their interpretation as available preparations or measurements requires a
separate operational construction. A weaker sufficient contract uses continuity
at one and one actual normalized echo with both inputs nonzero, while retaining
global complex multiplication. Absolute minimality and physical availability
of such a pair remain open.
[Single-echo theorem and rational control](191-single-echo-readout-and-rational-control.md)

## Controls separate continuity and context coverage

The nonzero-support indicator has nonnegative multiplicative,
conjugation-invariant weights and satisfies every normalized echo. It is
discontinuous and violates the parallelogram law. This control separates
continuity from the remaining global echo laws.

The quartic weight `normSq(z)^2` satisfies the continuous weight laws and has
every positive real response level. Restrict its admitted contexts to one
unit-phase branch and one zero branch. Every admitted pair is normalized and
passes its echo, while the quartic weight violates the full normalized echo
law and the parallelogram law. These restricted tests therefore leave a
nonquadratic candidate available.
[Echo controls](../Proofs/QMClosure/NormalizedEchoReadoutControls.lean)

## Reproducing the checks

Run the registered targets sequentially from the repository root.

```bash
lake build Proofs.QMClosure.NormalizedEchoReadout
lake build Proofs.QMClosure.NormalizedEchoReadoutControls
lake build Proofs.MetaLang.V8OperationalPrimitiveResearchLedger
```

Both registered echo proof-module builds passed locally. An independent
frozen-source audit covered all 287 owning-module declarations across the nine
proof modules in this cluster, including 41 private declarations and generated
declarations. The two echo modules contributed 26 and 17 declarations. One
shared axiom traversal found no local axioms, unsafe declarations or `sorryAx`.
The exact transitive axiom set was `propext`, `Quot.sound` and `Classical.choice`.
All nine proof-source hashes and the target registration hash matched the
approved snapshot before and after the audit. The audit exited successfully
in 53.05 seconds. All 58 declarations cited by the three updated ledger entries
matched their audited module origins. The bounded-likelihood outlook remains
outside these checked results.

## Remaining operational obligations

The literature context is the operational-sequence discussion in Goyal,
Knuth and Skilling, sections II–III, equations 27–34. The present theorem uses
its own explicit complex weight contract. The sequence adapter remains open,
including coherent coarse-graining, temporal composition and closure,
repeatability, reversal, normalized-context availability, global amplitude
extension and actual readout factorization. The two-dimensional representation
hypotheses and the separate unitarity argument retain their own obligations.
[Goyal, Knuth and Skilling](https://arxiv.org/abs/0907.0909v3)

Two coordinates alone leave an ordered-pair history interpretation open.
Likewise, dense preparation means leave a physical amplitude interpretation
open. Independent identification of `Qraw`, Born readout, detector selection
and event actualization remains required. Hilbert representation, composites,
dynamics, physical scales, full QM and GR retain their separate obligations.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
