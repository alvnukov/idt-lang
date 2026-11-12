# Same-preparation square readout selection

## Conditional selection on the literal carrier

The literal initial carrier P4 has `a+b=1`, `a^4=b^4`, complex coordinate
`E`, norm square `N(p)=Complex.normSq(E(p))` and algebraic shadow `q`.
Set `c=2*a*b`. The response contract supplies five exact universal premises

1. `W(1)=1`.
2. `W(a*p)+W(b*p)=W(p)` for every preparation.
3. `W(c*p)>=W(p)` for every preparation.
4. Define `B(n,m)=n*a+m*b`. For natural `n<=n'`, `m<=m'` and every `p`,
   require `W(B(n,m)*p)<=W(B(n',m')*p)`.
5. `W(p*p)=W(p)^2` for every preparation.

`InitialSquareReadoutSelection.selected` gives `W(p)=N(p)` for every
actual preparation. `norm_model` and `exists_unique_response` provide the
inhabited, unique numerical model. Paired echo, multiplicativity, exact
`c` invariance and null insertion follow after selection.

The fifth premise governs the diagonal serial product `p*p`. Quadraticity
under addition and physical implementation of repeated preparations require
their own contracts. The shadow `q` satisfies normalization, column laws,
prepared order and self-square, while `q(c*p)=q(p)/2` violates the universal
oriented `c` comparison.

## Proof architecture

`InitialColumnOrderReadoutCore.BaseContract` contains the first four fields.
It derives vacuum zero, nonnegativity, column half responses and null silence.
Its real-axis callbacks quantify over `x : ℝ`.

1. Square response gives the positive real-axis upper bound.
2. Finite phase words, dyadic prepared comparisons and an annulus argument
   give `W(p)<=256*N(p)`. Iterated squares sharpen this to `W(p)<=N(p)`.
3. Natural calibration and real-axis exactness give `N(p)/16<=W(p)`.
4. A second square amplification gives equality, with null preparations
   already covered by the four-field core.

The geometry is in `InitialCountSectorBounds`, and the final amplification
is in `InitialSquareReadoutSelection`. The core extraction preserves the
legacy echo Contract and its 26 public statement signatures.

The square and echo contracts select the same model class. The new result
changes the supplied operational response premise. Mathematical paired
constants and complex-coordinate conjugation geometry remain in the proof.
Physical origins of either terminal response law remain open.

## Finite calibration countercontrol

On the same carrier define `F(p)=sqrt(max(N(p)^2,N(p)*q(p)))` and
`e=2*(a*a+b*b)`. This response has normalization, column half laws,
prepared count order, universal self-square response, all-null silence and
unit `F(c)=1`. Its coordinate formula is continuous on `ℝ × ℝ`.

The actual positive finite preparation `p=1+e` gives

| Preparation | `E` | `q` | `N` | `F` |
| --- | --- | --- | --- | --- |
| `1` | 1 | 1 | 1 | 1 |
| `e` | 0 | 1 | 0 | 0 |
| `p=1+e` | 1 | 2 | 1 | `sqrt(2)` |
| `c*p` | 1 | 1 | 1 | 1 |

Thus the global `c` comparison fails, `F` differs from `N`, and null insertion
and multiplicativity fail. The witness uses finite positive expressions.

`InitialSquareFiniteCalibrationCountermodel.calibration_replacement_does_not_select`
rejects the stated unit-`c` plus null-calibration replacement. The separate
`coordinateReadout_continuous` and `F_coordinate_formula` declarations prove
continuity for the same response. Other finite replacement families require
their own analysis.

## Analytic limit of approximate comparison

The following extension is accepted analytically and awaits formalization.
Define `F_0=max(N,q)` and `F_(k+1)=sqrt(N*F_k)`. For each fixed `k>=1`,
the family retains normalization, column laws, prepared order, self-square,
all-null silence, coordinate continuity and unit `F_k(c)=1`.

With `gamma_0=1/2`, `gamma_(k+1)=sqrt(gamma_k)` and
`gamma_k=2^(-2^(-k))`, every preparation satisfies
`gamma_k*F_k(p)<=F_k(c*p)<=F_k(p)`. The ratio is sharp at `p=1+e`.

For each `epsilon>0`, choose one fixed `k>=1` with `gamma_k>=1-epsilon`.
The same response then satisfies the relative comparison for every
preparation, yet has no finite global upper factor against `N`.
Indeed `p_m=(1+e)^(2^k*m)` has `E=N=1`, `q=2^(2^k*m)` and `F_k=2^m`.
For every real `C`, one such actual positive finite expression has `F_k>C`.
These values follow from the explicit family formula.

For `N(p)>0`, `F_k(p)/N(p)=max(1,(q(p)/N(p))^(2^(-k)))`.
Hence `F_k` converges pointwise to `N` and uniformly on fixed finite sets.
A finite bound on `q/N` gives uniform relative convergence for this family.
Combining this restriction with a finite `N` bound gives uniform absolute convergence.
General bounded-domain stability requires a separate theorem.

The shadow `q` is algebraic. A `q/N` bound restricts the mathematical
preparation domain. A laboratory resource interpretation requires an
independent bridge. Both exact square selection and the earlier
echo-distortion theorem retain exact universal `c` comparison.

## Remaining origin obligations

The next question is an independent physical source for same-preparation
square response and full universally prepared `c` comparison. The
scalar-process versus actual-preparation interface remains open.
Adding finite calibration rules solely to remove a countercontrol leaves
that origin question unresolved.

The existing branch-word action identifies concatenation with operator
composition. Its stationary numerical gain is supplied, and its response
domain consists of serial words. Extending the response to arbitrary
coherent sums and all preparations remains an open obligation in
`gks_operational_sequence_bridge`.

Physical repeatability, copying, detector locality, reset comparison and
resource interpretation require their own operational contracts. Born
actualization, Hilbert reconstruction, full QM, GR and physical-scale
origins remain open.
