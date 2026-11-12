# Initial count geometry and prepared order

Actual finite histories on the initial carrier now admit checked dyadic raw comparisons and exact denominator-cleared transports. The response comparisons follow from prepared count order and increase under the chosen finite program. This supplies a common geometric layer for the scalar and word readout routes, whose full classifications remain analytically accepted and await formalization. [Research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Actual elements and two-coordinate geometry

The carrier is the existing literal two-relator semiring `P`, with complex evaluation `E`, real shadow `q`, `c=2ab` and `h=ab`. The checked combined normal form reflects equality from **both** `E` and `q`. This retains the distinction between the vacuum and positive-null elements with zero complex evaluation. [Combined normal form](../Proofs/QMClosure/TransparentFourthInitialNormalForm.lean)

For nonnegative dyadic numbers `s,t`, the constructions `scalar(s)` and `raw(s,t)` are actual elements of `P`. Their finite binary representations are checked by `scalar_grid` and `raw_grid`. With `u=twoInv`, the raw construction has

\[
\operatorname{raw}(n/2^k,m/2^k)=u^k(na+mb),\qquad
(E, q)=\left(\frac{s+t}{2}+i\frac{s-t}{2},\frac{s+t}{2}\right).
\]

The inverse `u=ab+T²`, where `T=a²+b²`, is an existing finite algebraic expression. Rational division is used in numerical design, and positive integer denominator clearing produces natural counts. The API adjoins neither arbitrary odd-natural inverses nor arbitrary real-coefficient preparations. Endpoint recognition preserves the raw-cone condition `q=Re(E)` together with `|Im(E)|≤Re(E)`. [Initial count geometry](../Proofs/QMClosure/InitialCountGeometry.lean)

An `ExactRawTransport M p` displays four natural counts and an actual identity

\[
M\,(n a+m b)=(A a+B b)\,p.
\]

The checked API verifies both coordinates, clears rational designs, and transports this equality through repetition, actual scalar shifts and serial shifts. Each constructor keeps its own positivity premises. A strictly positive clearing integer alone permits zero target counts, so a use of count ratios must establish the required positive height separately. The same algebra proves `c^k u^j=2^(k-j)h^k` for every `j≤k`. [Initial count geometry](../Proofs/QMClosure/InitialCountGeometry.lean)

## Response comparisons without calibration

For arbitrary `W:P→ℝ`, `PreparedCountOrder W` requires coordinatewise natural-count monotonicity at **every actual preparation** `p`. `ResponseIncreasing W M` requires `W(p)≤W(Mp)` for every `p`. The plus, minus and paired finite words are response-increasing under prepared count order. Dyadic prepared order is obtained by choosing a common binary denominator and applying natural-count order at the actual preparation `u^k p`. The proof uses algebraic unit cancellation. It assumes no response rule for `W(u^k p)`. The additional premise `W(0)=0` is used for the separate nonnegativity corollary. [Prepared count order](../Proofs/QMClosure/InitialPreparedCountOrder.lean)

For an exact transport and natural `j,k` with `jA≤2^k` and `jB≤2^k`, prepared count order and `ResponseIncreasing W M` give

\[
W\!\left(u^k\,\operatorname{bag}(jn,jm)\right)\le W(p).
\]

The serial-shifted version keeps the target `p` fixed while changing the actual source using `c^r`. These comparisons carry no half-response, gain, exact serial-response equality or continuity premise. The upper-transfer theorem gives a comparison when an exact raw landing is supplied. Constructing arbitrarily close upper landings remains a separate obligation. [Prepared count order](../Proofs/QMClosure/InitialPreparedCountOrder.lean)

## Finite numerical control

The numerical module uses ordinary real arithmetic. Put `K=(1+t)²/(1+t²)` and `R=(1+t²)^n`. For `target>1`, `0<t≤1` and `K^n<target≤K^(n+1)`, its finite bounds give

\[
\frac{\mathrm{target}}K\le K^n,\qquad
nt^2<(\mathrm{target}-1)t,\qquad R\ge1.
\]

With the additional condition `(target−1)t<1`, the checked upper bound is `R≤1/(1−(target−1)t)`. These pointwise estimates remain available when a later argument chooses growing target ratios. Separate fixed-target theorems select finite paired words whose real amplification tends to one and whose shadow amplification tends to the fixed target. They assert numerical coordinate limits. Limits of arbitrary responses require further arguments. [Paired count bounds](../Proofs/QMClosure/InitialPairedCountBounds.lean)

## Remaining readout and physical obligations

The authoritative Lean ledger records the checked package as `initial_count_geometry_and_prepared_order`. Its original scalar-classification task and terminal one-sided word task retain analytic status and empty checked evidence. The word task still quantifies mixed zero over **every** word depth and adjacent raw cell `k,n,m`, together with vacuum zero, unit normalization, universal forward serial increase and prepared natural-count order. Its optional sixth schema remains `W(T)=0`. [Research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The remaining formalization plan includes actual finite dyadic-program endpoint limits and arbitrarily close upper landing, numeric envelope upper semicontinuity and real local rotations with exact angular subdivisions, one bound for each entire serial orbit, orbit-supremum transport to the scalar grid, the original scalar classification, uniform convergence on dyadic points in bounded real boxes, and changing-source word recovery. The real rotation paths concern the numeric envelope only. No real-coefficient P programs are introduced. The checked finite estimates support those obligations while fixed-target limits keep their fixed-target quantifiers. Physical origins of the carrier relations, available inverse contexts and response schemas remain open alongside Born actualization, Hilbert reconstruction, full QM, GR and physical scales. [Research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean) [Physical scope boundary](150-physical-scope-boundary.md)
