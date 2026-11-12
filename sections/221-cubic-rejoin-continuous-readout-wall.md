# Continuous multiplicative readout on a cubic-rejoin carrier

The checked construction gives a concrete generated positive carrier with a continuous, globally multiplicative response, a local four-law readout base, and natural square gain. Its branches rejoin at powers three and six while their fourth powers differ. An exact depth-two witness has third inclusion-exclusion value `−3/4`.

## Carrier and response

Let `r = √3`, `ζ = (1 + i r)/2`, and let the ambient commutative semiring be `ℂ × ℝ≥0`. Define

\[
a=(\zeta,1/2),\qquad b=(\overline\zeta,1/2),\qquad
G=\operatorname{Subsemiring.closure}\{a,b\}.
\]

Write an element as `(z,q)`. On every element of `G`, the coordinate `q` reflects algebraic zero. Consequently `G` has no zero divisors, and `p+s=0` forces `p=s=0`. Native conjugation `J(z,q)=(z̄,q)` preserves `G` and is involutive. The response is

\[
W(z,q)=\lVert z\rVert q.
\]

It is continuous for the inherited product topology, nonnegative, normalized by `W(0)=0` and `W(1)=1`, and satisfies `W(ps)=W(p)W(s)` for all `p,s∈G`. The coordinate-zero reflection concerns `q`, whereas a nonzero element can have response zero.

## Universal response laws

The formal artifact checks the following laws over the entire generated carrier.

- Transparency and first-column conservation hold with `a+b=1`, `W(ap)=W(bp)=W(p)/2`, and `W(ap)+W(bp)=W(p)`.
- For `c=2ab=(2,1/2)`, exact serial preservation gives `W(cp)=W(p)`.
- Every natural count satisfies `W(np)=n²W(p)`. In particular `W(3p)=9W(p)=W(3)W(p)`.
- Conjugation, self-square, and self-echo satisfy `W(Jp)=W(p)`, `W(p²)=W(p)²`, and `W(pJp)=W(p)²`.
- For `B(n,m)=na+mb`, coordinatewise count growth preserves response order after every preparation `p`. Its proof uses

\[
W(B(n,m))^2=\frac{n^4+n^3m+nm^3+m^4}{4},
\]

whose coefficients are nonnegative. Multiplicativity transfers the comparison to `W(B(n,m)p)`.

The local `BaseContract` states the four fields directly on `G`, covering normalization, first-column conservation, `c`-increase, and prepared count order. The combined theorem `continuous_countermodel_certificate` packages these response laws and the countermodel witnesses. [Lean artifact](../Proofs/QMClosure/CubicRejoinReadoutCountermodel.lean)

## Finite rejoin and depth-two witness

The exact branch identities are `a³=b³`, `a⁶=b⁶`, and `a⁴≠b⁴`. Positive inverse words lie in `G`, and the constructed phase `ρ=a bInv` satisfies `ρ³=1`.

Choose the three distinct depth-two word values

\[
x=a^2,\qquad y=ab,\qquad z=b^2,\qquad t=x+y+z=(0,3/4).
\]

Each singleton has response `1/4`. Each pair sum has response `1/2`, and `W(t)=0` with `t≠0`. Thus

\[
I_3(x,y,z)=W(t)-W(x+y)-W(x+z)-W(y+z)+W(x)+W(y)+W(z)-W(0)=-3/4.
\]

These are the word labels `aa`, `ab`, and `bb` among the four binary words at depth two. The value violates grade-two additivity. Also `t+y=1`, so `W(t+y)=1` while `W(y)=1/4`. Response-dark insertion changes the response, even though the response nullset is additively closed. A second exact value is `W(1+t)=7/4`.

## Scope of the wall

The fixed-P4 selection theorem retains its stated carrier-specific domain and conclusion. This cubic construction establishes that the listed generic finite-rejoin and response laws admit a different carrier.

Earlier P8 artifacts already supply generic carrier-selection walls and generated positive carriers, with some additional prepared mixed-zero laws. The contribution here combines continuity and global multiplicativity on the generated cubic carrier with the short exact `I3` witness. [Earlier P8 artifact](../Proofs/QMClosure/EighthRejoinReadoutCountermodels.lean)

The checked result is algebraic. Physical-origin selection and a physical three-path experimental realization remain open bridges.
