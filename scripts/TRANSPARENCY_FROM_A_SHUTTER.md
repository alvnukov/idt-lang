# Does transparency have to be supplied as a primitive?

**Not in the following exact model.** Assume two signed-integer ports of
rank two, an additive raw update M, and that two identical updates exchange
the *full* ports with an unknown positive integral multiplier g: M²=gS.
Assume a nonzero nonnegative port-separable stock F with a common gain
F(Mq)=hF(q) and zero stock at vacuum. Inject only into one input. Close
the other path between two mixers into its own dump (no feedback), and
ask for a nonzero raw return in the original port. One such return forces
identical port inputs to propagate identically **up to a scalar ±r**.
Thus g=r² and r is even. The smallest possible |r| is 2; it is *not*
inferred that nature uses this minimum.

The [shutter probe](probe_transparency_shutter.py) includes cases that fail
if any of the physical qualifications are forgotten. It is a finite check
accompanying the argument, not a Lean proof or measured apparatus.

### Why a hidden reflection cannot give the return

Commutation with S gives M=[A,B;B,A]. On port sums and differences put
U=A+B, V=A−B. Then U²=gI and V²=−gI. If U is not scalar, both U and V
are traceless in rank two. Thus A and B are traceless, A²=sI for some
integer s, and B²=−sI follows from the raw echo. If s=0, two same-port
transmissions give zero immediately. Suppose s≠0.

Symmetrize F over negation and port exchange, obtaining an even common
one-port response E. The sum E(x)+E(y) obeys the same gain. Take mixed
finite differences in separate inputs at points with output (gz,gw);
all such points are reachable since M²=gS. On the output side a difference
of E at gz plus a difference at gw is zero. Since z and w vary independently,
each term is constant. Write L=g|s|. Increments g·sign(s)Au and
−g·sign(s)Bv in the two inputs cause increments Lu,Lv in the first output.
Restricting the base to L times the lattice shows that **all mixed second
differences of E(Lz) are constant**. On ℤ² this gives a quadratic plus affine
function; evenness and zero at zero remove the affine part. Call it Q.
Nonnegativity on lattice points implies positive semidefiniteness of its
real quadratic extension (use integer multiples of rational vectors).

Equal and opposite port preparations give Q(Uz)=hQ(z)=Q(Vz).
If Q is nonzero it is positive definite: the kernel cannot be a real line
invariant under a map with V²=−gI. Squaring gives h=g. Relative to this
derived inner product U/√g is a reflection and V/√g a quarter turn; they
anticommute. This would give A²=0, contrary to s≠0. Thus Q vanishes.
But E(gs x)=h²E(sx) by the echo; its left side vanishes because |gs|=L.
Consequently E(sx)=0 for every input and the original nonnegative stock
of A²x vanishes too. This covers nonfaithful modular stocks: an actual
nonzero *vector* is insufficient, the shutter return must be detectable.

The remaining case is U=±rI, so g=r². Since V=U−2B, V²≡r²I modulo four
but also V²=−r²I, which excludes odd r. For the minimum |r|=2 this feeds
the [port-stock argument](PORT_STOCK_ORIGIN.md). For U=−2I use −M for the
algebraic normal form only: in the single-port identity both A and B then
have an extra minus relative to this representative. Four iterations
cancel that sign before any evenness assumption on individual responses.
The eight-state averaging argument yields evenness, after which the two
global signs agree in the measured stock.

### What population measurements do and do not certify

A port-only echo can exchange outputs while twisting internal states.
It is not the raw equation M²=gS. There is a separate check *assuming*
ordinary norm readout, a fixed orthogonal/unitary device T, and coherent
port selection P₀. Suppose two steps swap the port subspaces. With
Q=T†P₀T and B=P₀QP₀ restricted to the initial port, the return through
the retained arm for a unit input x is

    p(return after shutter) = ⟨x,(B−B²)x⟩ = 1/4 − ||(B−I/2)x||².

Indeed, pulling the output projection back two steps gives P₁. The return
is the squared norm of the off-diagonal block P₁QP₀ on x; Q²=Q gives the
identity. A quarter return on a spanning set certifies a balanced splitter
on that span. With measured deficits on an orthonormal basis, the square
root of their sum bounds the maximum first-split imbalance. These are
unconditional probabilities per input, not rates renormalized to survivors.

The raw skew control splits *both* tested input axes 50:50 and exchanges
all port populations after two steps. Yet a diagonal input goes 49/50
to one port, and the detected double-pass fraction is 49/2500, not 1/4.
Even observing saturation does not establish the literal raw echo or
derive the calibrated norm model just used to interpret it.
