# Original a,b occurrence kernels and a resource boundary

The kernel selector starts with the actual unordered subsets of tagged
original \(a,b\) occurrences. One fixed finite subset-order cutoff and a
context-independent signed kernel, explicitly compatible with every evaluated
bag, selects the squared-norm readout under native normalization and the
two universal generator transfers. An independent resource wall uses native
dyadic growth to test an additional physical preparation/event-count bridge.
[Compiler source](../Proofs/QMClosure/OriginalOccurrenceKernel.lean)
[Selector source](../Proofs/QMClosure/OriginalOccurrenceNormSelection.lean)
[Resource-wall source](../Proofs/QMClosure/NativeBoundedResourceWall.lean)

## A kernel on actual original subsets

Use the existing initial presentation \(a+b=1\), \(a^2+b^2=0\), and an
arbitrary real readout \(W\). Supply

\[
W(a)+W(b)=1,\qquad
W(ap)=W(a)W(p),\qquad W(bp)=W(b)W(p)
\quad\text{for every presentation element }p.
\]

For every \(n,m\in\mathbb N\), the original occurrence carrier is
\(\operatorname{Fin}(n)\sqcup\operatorname{Fin}(m)\). The two disjoint tags
retain the identities of repeated \(a\) and \(b\) occurrences. Evaluating
the coherent sum of their native values gives the additive bag \(na+mb\).
[Compiler source](../Proofs/QMClosure/OriginalOccurrenceKernel.lean)

Supply one arbitrary finite \(K\) and one fixed real kernel
\(\kappa_{jk}\), depending only on the two label counts of a chosen subset.
The coefficients may be signed. The compatibility premise is

\[
\forall n,m\in\mathbb N,\qquad
W(na+mb)=
\sum_{\substack{s\subseteq\operatorname{Fin}(n)\sqcup\operatorname{Fin}(m)\\
                 |s|\le K}}
\kappa_{\#a(s),\#b(s)}.
\]

The sum includes each actual unordered subset once, including the empty
subset. The same \(K\) and kernel apply to all natural input counts. The
compatibility equation connects that static subset representation to the
readout of the evaluated bag.
[Compiler source](../Proofs/QMClosure/OriginalOccurrenceKernel.lean)

## Counting, polynomial selection and extension to the carrier

Grouping the tagged subsets by their label counts gives the identity

\[
W(na+mb)=\sum_{j+k\le K}\kappa_{jk}{n\choose j}{m\choose k}.
\]

Falling-factorial coordinate polynomials turn this into one finite bivariate
polynomial on all natural inputs. A natural-grid adapter turns the native
doubling law into the polynomial identity \(P(2X,2Y)=4P(X,Y)\), selecting
homogeneous degree two. The native values
\(W(a)=W(b)=1/2\) and \(W(a+b)=1\) fix

\[
W(na+mb)=\frac{n^2+m^2}{2}.
\]

The additional regularity premise is the original-subset compatibility
contract. Its finite order is arbitrary at input. The polynomial adapter uses
the calibration and doubling consequences of the supplied native transfers.
[Selector source](../Proofs/QMClosure/OriginalOccurrenceNormSelection.lean)
[Polynomial adapter source](../Proofs/QMClosure/QuadraticPolynomialDyadicSelection.lean)

The phase identities \(ua=-b\), \(ub=a\) transport the positive bag formula
through the four sign quadrants. For integer coordinates,
\(m+nu=(m+n)a+(m-n)b\). Half scaling and the existing Gaussian-dyadic normal
forms then give the carrier-wide conclusion

\[
W\bigl(h^r(m+nu)\bigr)=\frac{m^2+n^2}{4^r},\qquad
W(p)=\operatorname{normSq}(\operatorname{complexEval}(p)).
\]

The faithful algebraic representation appears in this conclusion under the
stated native and kernel premises.
[Selector source](../Proofs/QMClosure/OriginalOccurrenceNormSelection.lean)

The source also gives \(K\ge2\) as a conclusion and supplies a concrete
nonnegative order-two witness

\[
\kappa_{10}=\kappa_{01}=\tfrac12,\qquad
\kappa_{20}=\kappa_{02}=1,
\]

with all other coefficients zero. This witness evaluates to
\((n^2+m^2)/2\). Newton-basis uniqueness for arbitrary compatible kernels
remains a separate artifact obligation. The static subset-order and
context-independence assumptions also leave a physical causal-ancestry bound
as an additional obligation. Binary firing arity alone leaves that ancestry
question unresolved.
[Compiler source](../Proofs/QMClosure/OriginalOccurrenceKernel.lean)
[Selector source](../Proofs/QMClosure/OriginalOccurrenceNormSelection.lean)

## The regular family separates the finite-kernel premise

The separation adapter combines the new selector with the published
regular-family norm-difference witness. For every positive parameter \(c\),
it excludes every finite \(K\) and fixed signed kernel compatible with
all original \(a,b\) bags for that response. The continuous, faithful native
family therefore separates the finite-kernel compatibility premise.
[Separation adapter](../Proofs/QMClosure/RegularReadoutOccurrenceKernelSeparation.lean)
[Published regular-family boundary](200-native-regular-readout-boundary.md)

## An independent affine-resource wall

The resource argument starts only with native unit calibration and doubling

\[
W(2^k)=4^k.
\]

That subsequence rules out every uniform affine upper bound on \(W(n)\).
The wall uses these native identities independently of the subset
compiler and full norm selector.
[Resource-wall source](../Proofs/QMClosure/NativeBoundedResourceWall.lean)

The physical accounting model supplies complete firing-occurrence levels,
input-independent finite depth and outgoing degree bounds, at most \(AN+H\)
initial roots, and bounded events per firing. Repeated uses of a component are
distinct firing occurrences, and all firings and their events are counted.
The fixed background \(H\) is permitted. These assumptions give

\[
\operatorname{events}(N)
\le B(AN+H)\sum_{r=0}^{D}F^r.
\]

For original inputs, scalar \(n\) is the diagonal bag
\(na+nb=n\), containing \(2n\) tagged occurrences. A physical preparation
of that coherent bag with linear/affine cost is an extra bridge. The wall assumes a fixed nonnegative ceiling

\[
W(na+nb)\le\omega\,\operatorname{events}(2n).
\]

Reindexing the accounting doubles the initial slope and retains the same
background. The resulting affine raw bound conflicts with the native dyadic
subsequence. Exact positive-calibration identification is a special case.
[Resource-wall source](../Proofs/QMClosure/NativeBoundedResourceWall.lean)

History occurrences are syntactic alternatives. Assigning physical inputs,
firings or events to them, pricing coherent input assembly, and relating the
raw response to event count are additional contracts. The subset expansion
permits growing participation as input size increases. The wall is conditional
on the complete physical accounting and readout bridge supplied above.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Next analytic observation obligations

One separate analytic task records three parent-reviewed controller mechanisms.
They use polynomial relaxation with an input-dependent timer, a bounded
least-nonnegative polynomial guard, and a first hit among four uniformly
transverse polynomial guards. Their proposed outputs reproduce nonquadratic
native readouts through observation or stopping operations. The analytic relaxation argument gives
uniform absolute output convergence, while its near-vacuum relative and
second-order control remain distinct issues. The competing-guard construction
has a four-way vacuum tie, making the regularity of the complete selection
operation a substantive next question.

The next origin question is whether complete bounded-fanin/depth accounting of
event presence, stopping, control, normalization and output selection supplies
a uniform original-mask support bound. The same-W all-mask retained-bag
calibration used by the analytic Boolean-Möbius characterization is an
independent supplied bridge.

The source-level controller drafts are accepted for later compilation and
remain uncompiled, with empty checked evidence.
Aggregate coordinates, ideal real registers and clocks, exact event detection
and output interpretation are supplied. Discrete detector realization and
physical derivation remain open. Generic fixed-common-time \(C^2\) mechanisms
and the common-quadratic vacuum selector retain their separate open proof
obligations.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Verification and physical scope

Five registered proof targets passed. The exact-origin audit covered 98 new
declarations, with 95 in the four new modules and three in the polynomial
adapter. The new-origin set contains 18 private declarations, with 17 in the
four modules and one in the adapter additions. It reported zero local axioms
and zero unsafe declarations, with exactly `propext`, `Quot.sound` and
`Classical.choice` as the aggregate transitive axiom set.

All six recorded dependency profiles reported zero forbidden dependencies.
They distinguish the generic polynomial adapter, compiler/witness, universal
selector, native-only resource wall, independent regular control and the
kernel-separation consequence. Three individually reviewed generated
polynomial helpers have exact-name permissions in specified profiles.

The existing polynomial-source bytes are preserved around the insertion-only
adapter. A final selector documentation-comment adjustment preserves the
audited source by byte-exact reconstruction. The observation, mask-local and
stronger regularity tasks retain their analytic stages and empty checked
evidence.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The kernel compatibility contract, any physical ancestry bound, the resource
accounting bridges and the observation mechanisms each retain their stated
supplied scope. Outcome frequencies, Born actualization, Hilbert representation,
full QM closure and physical scales remain open.
[Physical scope boundary](150-physical-scope-boundary.md)
