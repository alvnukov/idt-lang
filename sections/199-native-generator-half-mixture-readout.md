# Native generator transfer and fixed-corner half-mixture readout

The reduced contract starts with an arbitrary real readout on the
existing initial two-generator history quotient. One normalization, two
universal native-generator transfer laws and one universal continuation law for
fixed equal-half probe pairs select the squared Gaussian-dyadic norm on every
presented history. The native transfer assumptions already supply a canonical
normalized raw echo. The pair rule supplies the additional readout selection
and general conservation argument.
[Generator-transfer source](../Proofs/QMClosure/NativeGeneratorMixtureReadout.lean)
[Single-continuation source](../Proofs/QMClosure/NativeSingleContinuationReadout.lean)

## Existing carrier and exact reduced premises

The carrier is the initial quotient of the free unital semiring on \(a,b\)
by the two relations

\[
a+b=1,\qquad a^2+b^2=0.
\]

Its previously proved algebra supplies a commutative ring, an exact half,
a phase \(u\) with \(u^2=-1\), syntactic reflection and a faithful
Gaussian-dyadic representation. Every element has a normal form
\(h^k(m+nu)\), where \(h=1/2\), \(k\in\mathbb N\) and
\(m,n\in\mathbb Z\). These carrier facts are available before introducing
the arbitrary readout \(W\).
[Initial-presentation source](../Proofs/QMClosure/NativeInitialHistoryPresentation.lean)

The reduced readout assumptions are exactly the following.

1. \(W\) is real-valued and \(W(a)+W(b)=1\).
2. For every presentation element \(p\),
   \(W(ap)=W(a)W(p)\) and \(W(bp)=W(b)W(p)\).
3. Set \(f(m,n)=W(m+nu)\) and prescribe the four probes
   \(P(z)=(f(z),f(z+1),f(z+i),f(z+1+i))\). For every four integer-lattice
   sources \(x,y,v,w\), the single \(+1\) continuation obeys

\[
P(x)+P(y)=P(v)+P(w)
\quad\Longrightarrow\quad
P(x+1)+P(y+1)=P(v+1)+P(w+1).
\]

The transfer laws cover every input \(p\). The pair law covers every source
quadruple with equal entire four-vectors. Arithmetic equality of raw pair sums
is equivalent to equality of external equal-half means. The four coordinates
are prescribed translated responses of this same \(W\).
[Single-continuation source](../Proofs/QMClosure/NativeSingleContinuationReadout.lean)

The external mean \(\tfrac12(P(x)+P(y))\) and the coherent history
\(ax+by\) are separately defined operations in this contract. Interpreting the
external mean as a physically accessible preparation mixture remains an open
operational-origin obligation.
[Generator-transfer source](../Proofs/QMClosure/NativeGeneratorMixtureReadout.lean)
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Calibration and the canonical raw echo precede pair sufficiency

The native transfer laws at \(p=1\), together with normalized generator
readings, derive \(W(1)=1\). The grammar gives \(a^4=b^4\), so universal
transfer yields \(W(a)^4=W(b)^4\). Real factorization and
\(W(a)+W(b)=1\) force

\[
W(a)=W(b)=\tfrac12.
\]

Generator symmetry and positive generator readings therefore follow from the
normalized real transfer contract. It also gives \(W(0)=0\), half scaling,
quadratic doubling, phase invariance and diagonal scaling.
[Generator-transfer source](../Proofs/QMClosure/NativeGeneratorMixtureReadout.lean)

The coherent two-channel mixer is

\[
T(p,q)=(ap+bq,bp+aq).
\]

The carrier relations give \(T^2(p,q)=(q,p)\),
\(T(1,0)=(a,b)\) and \(T(a,b)=(0,1)\). The calibrated readings give strictly
positive intermediate weights \(1/2,1/2\) and total raw weight one at the
canonical input, intermediate pair and return. These statements use the native
transfer contract. The general conservation law is obtained later from pair
sufficiency and selection.
[Generator-transfer source](../Proofs/QMClosure/NativeGeneratorMixtureReadout.lean)

## One continuation transports to the rectangle recurrence

Phase invariance makes the integer restriction quarter-turn invariant.
For the prescribed corners, the affine map

\[
K(z)=iz-1
\]

permutes the four probe coordinates by \((2,0,3,1)\). Its fourth iterate is
the identity. Transporting equal pair sums through \(K^{-1}\), the supplied
\(+1\) continuation and \(K\) gives the \(+i\) law. Repeating the same
transport gives the other two signed coordinate laws.
[Single-continuation source](../Proofs/QMClosure/NativeSingleContinuationReadout.lean)

The derived unit, zero, phase and diagonal readings give the exact seed

\[
P(0)+P(-1-i)=P(-1)+P(-i)=(2,2,2,2).
\]

Iterating the continuation rules propagates this equality to every lattice
translate and supplies the global rectangle identity

\[
f(z+1+i)+f(z)=f(z+1)+f(z+i).
\]

The checked integer argument separates coordinates as
\(f(m,n)=g(m)+g(n)\). Diagonal scaling gives the axis parallelogram law and
then the recurrence

\[
g(n+1)+g(n-1)=2g(n)+2,\qquad g(0)=0,\quad g(1)=1.
\]

The integer recurrence yields \(g(n)=n^2\) on all integers. The proof passes
through this rectangle argument and the derived generator laws.
[Fixed-corner source](../Proofs/QMClosure/FixedCornerHalfMixtureReadout.lean)
[Generator-transfer source](../Proofs/QMClosure/NativeGeneratorMixtureReadout.lean)

## Selection on every presented history

The resulting readout formula is

\[
W\bigl(h^k(m+nu)\bigr)=\frac{m^2+n^2}{4^k}.
\]

Every presentation element has such a normal form, so this determines the
arbitrary supplied \(W\) throughout the carrier. Equivalently, its value equals
\(\operatorname{normSq}(\operatorname{complexEval}(p))\), using the existing
faithful algebraic representation in the conclusion.
[Generator-transfer source](../Proofs/QMClosure/NativeGeneratorMixtureReadout.lean)
[Single-continuation source](../Proofs/QMClosure/NativeSingleContinuationReadout.lean)

The derived consequences include global multiplicativity, syntactic-reflection
invariance, nonnegativity and \(W(p)=0\iff p=0\). Natural counts satisfy
\(W(n)=n^2\) and \(W(m)\le W(n)\iff m\le n\). Dyadic counts have the exact
formula \(W(h^k n)=n^2/4^k\). The all-input mixer conserves total raw weight,
the readout obeys the parallelogram identity, and its raw third-order
inclusion-exclusion expression vanishes. The explicit norm-model witness
inhabits the complete reduced contract.
[Generator-transfer source](../Proofs/QMClosure/NativeGeneratorMixtureReadout.lean)
[Single-continuation source](../Proofs/QMClosure/NativeSingleContinuationReadout.lean)

## A countercontrol isolates the pair-sufficiency obligation

On the same initial presentation, let \(E\) be its existing evaluation into
\(\mathbb Z/5\mathbb Z\) and define

\[
W_{\rm mask}(p)=
\begin{cases}
0,&E(p\,\operatorname{reflection}(p))=0,\\
\operatorname{normSq}(\operatorname{complexEval}(p)),&
E(p\,\operatorname{reflection}(p))\ne0.
\end{cases}
\]

The countercontrol artifact gives nonnegativity, unit calibration,
global multiplicativity, reflection invariance, both universal native
half-transfer laws and the normalized canonical raw echo. It also gives a
nonzero null history \(5\), with \(W_{\rm mask}(5)=0\), while
\(W_{\rm mask}(1)=1\). Thus natural count monotonicity fails at \(1\le5\).
[Countercontrol source](../Proofs/QMClosure/NativeGeneratorReadoutCountercontrol.lean)

For its fixed corner probes, the seed pair sums are both \((2,2,2,2)\).
After the \(+1\) continuation the two pair sums are

\[
(2,6,2,1)\qquad\text{and}\qquad(2,1,2,6).
\]

The prescribed pair-sufficiency law therefore fails. At coherent mixer input
\((1,2)\), total input weight is five and total output weight is zero.
The raw third-order expression at \((1,1,i)\) is \(-5\). These explicit
controls identify an obstruction to deriving pair sufficiency or general
conservation from native transfer and the canonical echo.
[Countercontrol source](../Proofs/QMClosure/NativeGeneratorReadoutCountercontrol.lean)

## Research boundary and verification

The supplied premises retain the history grammar and destructive relation,
a real normalized readout, all-context native factorization and sufficiency of
the prescribed probe pairs under continuation. Their physical and robust
operational origins remain open. The next research stage tests independence of
the remaining premises and studies finite-precision stability of transfer and
pair sufficiency. A separate analytic candidate tests whether faithfulness,
continuity and scalar count order can replace fixed-corner pair sufficiency.
Its Lean formalization remains pending. Event frequencies, Born actualization,
Hilbert representation, full QM closure and physical scales retain separate
obligations.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
[Physical scope boundary](150-physical-scope-boundary.md)

All four registered targets compiled successfully. The fixed-corner audit
covered 24 exact-origin declarations. A second, joint audit covered 141
exact-origin declarations in the three native modules, including one private
declaration. Together these two audits cover 165 declarations across the four
modules. Each audit reported zero local axioms, zero unsafe declarations and
exactly `propext`, `Quot.sound` and `Classical.choice` as its aggregate transitive
axiom set. Source hashes remained unchanged through the audits.

Actual-dependency profiles trace native selection through the elementary
fixed-corner rectangle and integer recurrence, reusing only basic lattice
definitions from the earlier mixture and rank modules. The native echo profile
uses the native transfer contract. The grammar and complex normal-form
identities have their own readout-independent profiles. The operational ledger
records the accepted conditional theorems and the open next-stage obligations.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
