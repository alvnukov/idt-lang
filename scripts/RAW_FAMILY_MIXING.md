# Can the raw three-port mixer describe quark mixing?

**No, for one direct identification.** Identify both the up- and down-family
mass bases with words of the same three-port mixer, in the same raw frame
and with no unobserved ports. Their relative unitary must obey two triangle
inequalities on off-diagonal magnitudes when mixing is small. The quark data
violate both. This is a necessary-condition test with no fitted parameters.
It does not test arbitrary embeddings, derive quark masses, reject all
three-generation theories, or exclude the mixer as a microscopic operation.

## Observable and external comparison

We froze the [2024 PDG CKM review](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf),
not a live data feed. Its Eq. (12.27), p. 12, is a global fit imposing the
three-generation Standard Model. Its nine entries are not nine independent
measurements. No statistical significance is assigned to the following
arithmetic comparison:

| Necessary triangle (central magnitudes) | Large side | Sum of smaller sides | Excess |
| --- | ---: | ---: | ---: |
| us ≤ cb + td | 0.22501 | 0.04183 + 0.00858 | 0.17460 |
| cd ≤ ts + ub | 0.22487 | 0.04111 + 0.003732 | 0.180028 |

Any raw table misses at least one central magnitude by **0.06000933…**.
The distance lower bound is still 0.059496 for every table in the rectangle
of the review's individual quoted ranges. That rectangle is a sensitivity
test, not a joint confidence region. Independently of using all nine global-fit
values, Eqs. (12.8), (12.11) and (12.12) report decay-based estimates for
a=|us|, b=|cb| and c=|ub| of 0.22431(85), 0.0411(12), 0.00382(20).
Their extraction has theoretical inputs; in particular the review discusses
inclusive/exclusive determinations. Even the deliberately broad box
0.20≤a≤0.25, b≤0.06, c≤0.01 contradicts this raw model:
unitarity cofactors give |td|≤ab+c, |cd|≤a+c, |ts|≤b+c. The necessary
triangle a≤b+|td| implies a(1−b)≤b+c, yet 0.188>0.07 over the whole box.
These are absolute matrix-element magnitudes, not transition probabilities.

## Why the triangle is compulsory

The addressed raw mixer T fixes the all-ones vector, is unitary in the
supplied norm, and has determinant i. So does the corresponding fixed-vector
condition for every relative word; its determinant is a fourth root of unity.
Let S be the sum of the six off-diagonal magnitudes. Row sums give
|3−tr U|≤S. If the two centered eigenvalues have product ±i, their sum
lies on a line at 45° to the real axis, giving |3−tr U|≥√2; for product
−1 it is ≥2. Thus S<√2 locks the determinant to +1. Both comparators,
including the small perturbations used in the distance bound, obey this lock.

The centered block is then in SU(2), so its Hermitian part is scalar.
The two oriented off-diagonal triples of U have the form
(a+ix,a+iy,a+iz) and (b+ix,b+iy,b+iz), with real a,b,x,y,z and x+y+z=0.
Indeed the imaginary parts of opposite entries agree, the symmetric real
parts are constant, the row and column sums force the three antisymmetric
real differences around the cycle to agree, and the trace is real.
Now (a,x)=(a/2,−y)+(a/2,−z); taking lengths gives the stated triangle.
Each possible convention for external quark-field phases has identical
magnitudes. Independent relabelings of up and down families are raw swaps
and cannot hide the gap. An **internal change of embedding** is not a
convention and can change the result. [Exact controls and data pin](probe_ckm_raw_family_wall.py).

## How many unobserved ports change the answer?

Keep the same physical frame with three directly occupied input/output ports
and blank spectator inputs. Write A for the visible block; do **not**
renormalize its columns after discarding the other outputs.

| Contract | Consequence |
| --- | --- |
| Exactly zero leakage, any finite number of blank ports, finite raw word | Unitarity block-diagonalizes the map. A fixes the three-port uniform vector, and its determinant belongs to ℤ[i,1/2] and has norm one, hence is ±1 or ±i. The same wall applies. |
| One blank port, any word or its norm limit | With total leakage ℓ and maximum absolute visible magnitude error δ against the central target, δ + √(3ℓ) ≥ 0.06000933…. |
| Two blank ports, arbitrarily long words and arbitrarily small nonzero leakage | In norm closure every three-family unitary can be approximated up to external row and column phases. Thus the measured hierarchy cannot select this larger model without an additional cost or microscopic prediction. |

For the one-spare statement, let u=(1,1,1,1)/2, d=U₄₄ and
q=(e₄−u/2)/(√3/2). The total leakage from the three separately prepared
input basis states is ℓ=1−|d|². Cauchy–Schwarz on the last column gives
|1−d|²≤3ℓ; hence ‖Uq−q‖²≤16ℓ/3. On u⊥ choose a special unitary S
returning Uq to q, with ‖S−I‖=‖Uq−q‖: in a two-plane, extend the vectors
to SU(2) frames. The eigenvalues of their relative rotation are conjugate,
so the squared norm is 2−2 Re⟨Uq,q⟩. For parallel vectors use an arbitrary
orthogonal companion. Extend S by identity on the remaining directions.
Now SU fixes e₄ and u and has the original four-valued determinant. Its
visible block belongs to the excluded continuous containing class. The change
SU−U annihilates u on the left and on the right. Each coordinate vector has
projection of norm √3/2 on u⊥, so changing any entry modulus costs at most
(3/4)‖S−I‖ ≤ √(3ℓ). At δ=0 the resulting necessary total
leakage is at least **0.001200373…** (at least one input leaks a third of this
amount or more). This is **not measured missing probability in CKM data**.

There is a stronger joint test. The correction Δ=SU−U has rank at most two
and nuclear norm ν=2‖Uq−q‖ (the two nonzero singular values, when present,
are equal). Its absolute changes summed on one oriented cycle cost at most ν:
the mask that aligns their three phases is a partial permutation of norm one.
On all six off-diagonals the cost is at most 2ν by the same dual-norm
inequality; the corresponding mask has maximum absolute row/column sum two.
Let v be a lower bound on a violated cyclic triangle excess in the supplied
rectangle and s an upper bound on its total off-diagonal sum. If s+2v<√2,
then ν<v would leave the repaired determinant locked and its triangle still
violated. Therefore ℓ≥3v²/64. For the whole nine-entry PDG rectangle,
v=0.178488 gives **ℓ≥0.001493342163**. But unitarity of the full four-port
matrix also gives ℓ=3−Σ|Aᵢⱼ|², so the nine lower endpoints imply
**ℓ≤0.001417497735**. These disjoint intervals exclude one raw blank port
even if its leakage is not separately bounded. This tests reproducibility
of a published **unitary fit**, not independent evidence against new quarks;
the nominal central table is rounded and is not an exact unitary matrix.

For two spares, [Idel and Wolf](https://arxiv.org/abs/1408.5728)
establish that every unitary can be externally rephased to a unitary A
whose rows and columns sum to one. Take a two-port block fixing its
uniform vector with other eigenvalue conjugate(det A). The full five-port
matrix fixes the uniform vector and has determinant one. The [centered
native density argument](OPERATIONAL_SECTOR_WORDS.md) puts it in the
operator-norm closure of raw words on a connected five-port graph.
Consequently both the visible entries and the zero-leakage limit can be
approached; no finite word with exactly returned spares is promised. This
escape preserves the rephasing equivalence class, not only the nine moduli.
An explicit non-dyadic two-block example has |us|²=1/17 and both other
cyclic entries zero. It is an algebraic countercontrol, not a fit.
[Blank-port checks](probe_ckm_blank_ports.py). All arguments here are
conditional mathematics and finite replays, not new Lean proofs.
