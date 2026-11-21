# A basis-free count for one port

Can the square weight be obtained without assuming that two invisible
channels *inside* the same port count independently? **Yes, conditionally.**
One conserved nonnegative stock, additive only between distinct ports,
suffices in the minimal integer architecture. It selects an intrinsic
count, not a preferred name for either internal coordinate.

For any nonzero port state x the result is, up to one common scale κ,

**W(x)/κ = number of cosets of ℤx + ℤJx in the port lattice Λ.**

That number is |det(x,Jx)| in any integral lattice basis. The zero state
has zero weight; the quotient at zero is infinite and is *not* used.
The quotient gives a count for each path. It does not by itself say
which path is detected or exert a force on a detector.

### What is supplied

As in the [minimal raw-root argument](SEPARABLE_STOCK_SELECTION.md), two
addressable ports have signed additive substitutions, transparent common
amplitude scaling by 2, and two updates act as four times port exchange.
Work at the first possible internal rank, Λ=ℤ². Consequently an integer
map J with J²=−I exists; put A=I+J, B=I−J=−JA. The raw mixer acts by
M(x,y)=(Ax+By,Bx+Ay). Allow **different arbitrary functions of a whole
port** W₀,W₁: Λ→ℝ. They are nonnegative, zero on zero, and not both
identically zero. The only gain premise is F(Ms)=h F(s) for every
preparation s, for F(x,y)=W₀(x)+W₁(y) and one unknown positive h.
No dot product, complex algebra, arm equality, sign symmetry, probability,
or choice of basis is put into the stock.

### One finite orbit forces equality and the gain

Apply the gain to a source in just port p:
hWₚ(x)=Wₚ(Ax)+W₁₋ₚ(Bx). Also M²=4S gives Wₚ(4x)=h²W₁₋ₚ(x).
Expand the single-port identity four times. A⁴=−4I and B=−JA, so after
removing the common scale the result is

    h² Wₚ(x) = Σₖ binom(4,k) W_{p ⊕ (k mod 2) ⊕ 1}(−(−J)ᵏx),  k=0,…,4.

Each of the five terms permutes the eight port/phase labels (p,Jʲx).
Sum over a nonzero-stock orbit: h²=16, hence h=4. The identity now
expresses each value as a convex average. The k=1 term cycles phase at
fixed port, k=0 switches ports and advances phase by two; these connect
all labels. A maximum must propagate to every label. Thus on **every**
orbit both ports share one J-invariant W. In particular W is even,
and W(Ax)=2W(x).

### The output geometry and a canonical count

The two output arguments are A(x−Jy) and A(y−Jx). The latter has the
same weight as A(x+Jy) by J-invariance. The gain law therefore gives
W(x+z)+W(x−z)=2W(x)+2W(z), since z=Jy ranges over the lattice.
The integer recurrence (or polarization) gives W(x)=Q(x,x) for a real
symmetric bilinear form. For example the two basis values and
(W(e₁+e₂)−W(e₁)−W(e₂))/2 determine all its entries. Choose a lattice v
with W(v)>0. The two real-linearly independent vectors v,Jv have equal
weight and Q(v,Jv)=0 by J-invariance. This makes Q positive definite:
faithfulness and coercivity were conclusions, not assumptions.

Choose a shortest nonzero lattice vector v for this Q. Round the two real
coordinates of any lattice point in the orthogonal basis v,Jv to the
nearest integers. The remaining lattice vector has weight at most W(v)/2.
By minimality it vanishes. Thus v,Jv form an **integer** basis, and
W(mv+nJv)=κ(m²+n²), κ=W(v)>0. In this basis x and Jx span a sublattice
of index m²+n²: its count of residue classes is the formula above. It is
preserved by any unimodular change of labels. In raw coordinates
J=[a,b;c,−a] the same answer is κ|c x₁²−2a x₁x₂−b x₂²|.
If the original raw axes must *also* contribute independently, the cross
term forces a=0, recovering the stronger chart restriction from the
[independent raw-channel probe](probe_separable_event_stock.py).

### What does not follow

- Conditional [exact checks](probe_port_stock_origin.py) accompany this
  argument. It is not a new checked Lean result. The nearby
  [dyadic-mixer theorem](../Proofs/QMClosure/NativeDyadicMixerSelection.lean)
  starts with a given Gaussian composition law, mixer, and common
  multiplicative response; this is a different inverse problem.
- If the readout of one port can depend on what is in the other, multiply
  both visible weights by a positive common factor depending on the joint
  input. All normalized probabilities are unchanged. The factor can even
  be chosen constant on mixer orbits, preserving the raw gain. Normalized
  detector tables alone cannot certify port separability.
- For four internal real/integer coordinates with two independent copies
  of J, different weights on the copies, or a dark copy, also pass. The
  unique metric up to scale here is a **rank-two** statement.
- Linear substitutions, exact transparency, the lattice, minimum dimension,
  and common gain remain substantive hypotheses. The finite counts are
  not a continuum, an energy quantum, a rule for sampling outcomes, the
  particle spectrum, or a derivation of our physical dimensions.

Two additional controls make the interpretation operational:

- [Spectator comparison](probe_spectator_stock_bridge.py): in a terminal
  menu with stable positive pairwise odds and consistent triangles, odds
  relative to a common reference reconstruct relative weights. An untouched
  positive reference whose rate is unchanged while the other two ports mix
  forces their combined weight to scale by the same factor as the reference.
  One fixed reference suffices if its local response really is stable. A
  dark reference gives no information; a drifting reference hides unequal
  gains. Removing a terminal alternative in an odds comparison is **not**
  the act of closing a coherent upstream path. All conclusions are about
  an observable equivalence class, not the absolute microscopic stocks.
- [Coset-address trial](probe_coset_address_transport.py): serial composition
  of nonzero Gaussian amplitudes gives a map from addresses modulo zw to
  addresses modulo z, with each fiber the size of the quotient modulo w.
  An additive split need not exist (z=w=2). More importantly, cosets alone
  do not supply a mixer router equivariant under a fixed address-translation
  action. With a single unity input, four seeds at the first port must
  form two orbits of size two; with a unity in both ports the same seeds
  must form one orbit of size four. The 120 commuting pairs of permutations
  on four seeds confirm the incompatibility. Allowing state-dependent
  translation actions avoids it. This rejects a *particular* bare-address
  mechanism, not the intrinsic count or every possible detector.
