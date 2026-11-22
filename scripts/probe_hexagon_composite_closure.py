"""What can two copies of the measured F5 contact hexagon consistently join?

Replay: python3 -B -O -m scripts.probe_hexagon_composite_closure

This finite diagnostic is about stocks of translated four-history preparations
and their six terminal binary dials. Not all F5 microstates, circuits or effects
are in this subtheory. Local convex mixing, unbiased independent skip coins and
the reader are supplied. On pairs we TEST extending the local affine effect
equalities to joint experiments (so products are separately affine), and an
additional remote-conditioning rule. Neither is a consequence of the F5 gate.
No amplitude sum, fitted joint probability row, postselection or experimental
data enter the upper bounds. Attainability in a mathematical family is not an
F5 source, a spacelike implementation, or a derivation of a physical joint law.
"""

from fractions import Fraction as F
from itertools import combinations, product

from scripts.probe_affine_contact_fringe import Six, cycle, detector, need


# There are three settings up to opposition but only two independent contrast
# coordinates. The normalized state space is two-dimensional.
U = ((1, 0), (0, 1), (-1, 1))
U6 = U + tuple((-a, -b) for a, b in U)
N = ((2, -1), (1, 1), (-1, 2))  # signed facet observables are (2/3)N
F6 = tuple((F(2*a, 3), F(2*b, 3)) for a, b in N)
F6 += tuple((-a, -b) for a, b in F6)
GRAM = (1, F(1, 2), F(1, 2), 1)
SIGN = (-1, 1)


def pair(u, k, v):
    return u[0] * (k[0]*v[0] + k[1]*v[1]) + u[1] * (k[2]*v[0] + k[3]*v[1])


def dot(v, w):
    return sum(x*y for x, y in zip(v, w))


def tensor(u, v):
    return tuple(a*b for a in u for b in v)


def mul(c, v):
    return tuple(c*x for x in v)


def chsh(k):
    # Chronology is not being interpreted as spacelike locality.
    reads = [pair(U6[i], k, U6[j]) for i, j in ((0, 1), (0, 0), (2, 1), (2, 0))]
    s = sum(reads[:3]) - reads[3]
    need(s == 2*k[0] - k[2] + k[3], "dial convention")
    return s


def local_sector():
    states = cycle((0, 1, 0), Six)
    contacts = tuple(2*int(detector(s, 0))-1 for s in states)
    need(contacts == (1, 1, 1, -1, -1, -1), "raw window")
    fringe = tuple(
        F(sum(contacts[(i+j+d) % 6] for i, j in product(range(2), repeat=2)), 4)
        for d in range(6)
    )
    # Preparing phase t and reading d uses relative phase d-t.
    vertices = tuple((fringe[-t % 6], fringe[(1-t) % 6]) for t in range(6))
    for t, h in enumerate(vertices):
        need(tuple(dot(h, u) for u in U6) == tuple(fringe[(d-t) % 6] for d in range(6)),
             "effect quotient not valid on the generated stock")
        need(h == (pair(U6[t], GRAM, U6[0]), pair(U6[t], GRAM, U6[1])), "gram chart")
    # Verify the full facet description rather than assuming a regular polygon.
    corners = set()
    for u, v in combinations(F6, 2):
        det = u[0]*v[1] - v[0]*u[1]
        if det:
            point = ((v[1]-u[1])/det, (u[0]-v[0])/det)
            if all(dot(n, point) <= 1 for n in F6):
                corners.add(point)
    need(corners == set(vertices), "wrong local state cone")
    for j, u in enumerate(U6):
        need(tuple((a+b)/2 for a,b in zip(F6[j], F6[(j+1) % 6])) == u,
             "generated effect is a mixture of adjacent full effects")
        need([h for h in vertices if dot(u, h) == 1] == [vertices[j]], "singleton face")
    return contacts, fringe, vertices


def shared_phase_control(contacts, fringe):
    # A native *local* join: one uniform raw phase, its antipode in the other
    # arm, actual terminal contacts. Comparable difference convention to fringe.
    corr = tuple(
        F(sum(contacts[t] * contacts[(t+3+d) % 6] for t in range(6)), 6)
        for d in range(6)
    )
    need(corr == (-1, F(-1, 3), F(1, 3), 1, F(1, 3), F(-1, 3)), "raw common cause")
    need(all(corr[d] == corr[-d % 6] == -corr[(d+3) % 6] for d in range(6)),
         "raw rotation/opposition/swap")
    need(abs(corr[1]+corr[0]+corr[-1]-corr[-2]) == 2, "raw common-cause CHSH")
    need(corr[2] != corr[1] - corr[0] and corr != mul(-1, fringe),
         "under conditioning, raw phase retains more information than the quotient")
    return corr


def terminal_effects(hexagon):
    """Recover the restricted effects even allowing arbitrary terminal readers.

    g[n] is any stochastic signed contrast of the terminal phase alone in a
    fixed frame (no record of the skipped word, initial preparation or mixture
    label). Preparation t exposes it to phases -t plus two fair skips. If the
    resulting effect is affine on the above hexagon its opposite-pair sums
    equal 2c. The 1,2,1 smoothing on the even sector of period three is
    invertible and fixes constants. Thus g[n]+g[n+3]=2c. Its odd residual
    obeys |g[n]-c|<=1-|c|, since BOTH c+residual and c-residual are in [-1,1].
    After rescaling, all residuals form a three-cube; it suffices to map its
    eight corners. This also covers mixtures of non-affine deterministic
    readers that become affine only after mixing.
    """
    def row(g):
        return tuple(F(g[-t % 6] + 2*g[(1-t) % 6] + g[(2-t) % 6],4) for t in range(6))

    need(det3((1,2,1), (1,1,2), (2,1,1)) == 4, "even-sector inverse missing")
    actual = {tuple(dot(u, h) for h in hexagon) for u in U6}
    projected = {row(q + mul(-1,q)) for q in product(SIGN, repeat=3)}
    need(projected == actual | {(0,)*6}, "raw readers extend the centered effects")
    for q in product(SIGN, repeat=6):
        r = row(q)
        paired = {r[i]+r[i+3] for i in range(3)}
        need((len(paired) == 1) == (len({q[i]+q[i+3] for i in range(3)}) == 1),
             "raw even-sector criterion")
    # First full-dual facet asks the same raw phase to return opposite signs.
    need(dot(F6[0], hexagon[0]) == 1 and dot(F6[0], hexagon[2]) == -1,
         "wrong facet endpoints")
    supports = [{(-t+a+b) % 6 for a,b in product(range(2), repeat=2)} for t in (0,2)]
    need(supports[0] & supports[1] == {0}, "facet contradiction lost")


def change_reader_control(contacts):
    # Do not silently promote "every quotient-affine terminal reader" into
    # "every F5 terminal reader". The direct first-wire contact distinguishes
    # mixtures which all six window dials identify. Same triple, frame, coins.
    direct = tuple(int(s[0] == 0) for s in cycle((0,1,0), Six))
    need(direct == (1,1,0,0,0,0), "unexpected instantaneous contact")
    p = tuple(F(sum(direct[(t+a+b) % 6] for a,b in product(range(2), repeat=2)),4)
              for t in range(6))
    center_reads = {(p[i] + p[i+3])/2 for i in range(3)}
    need(center_reads == {F(3,8), F(1,4)}, "center remained equivalent")
    # The middle wire's immediate equality to the SAME reference already
    # singles out phase 5, in every allowed affine frame. An AND of the two
    # previous first-wire visits also singles out a phase, but is unnecessary.
    # A positive assignment extending the affine identities to both slots now
    # supplies P(t,u)>=0 for the singleton products; their local sums are the
    # units. No simultaneous nondestructive device is needed for this algebraic
    # implication. Availability of the middle-wire reader in the candidate
    # two-arm experiment and joint extension are assumptions, not data.
    atom = (0,0,0,0,0,1)
    for a,b in product(range(5), repeat=2):
        if a != b:
            orbit = cycle((b,a,b), Six)
            need(tuple(int(x[1] == b) for x in orbit) == atom, "middle-wire singleton")
            need(tuple(int(x[0] == b) for x in orbit) == direct, "first-wire frame")
    need(sum(direct[t]*direct[(t-1) % 6] for t in range(6)) == 1, "alternate AND control")
    atoms = tuple(tuple(atom[(t-r) % 6] for t in range(6)) for r in range(6))
    need(all(sum(e) == 1 for e in atoms) and all(sum(col) == 1 for col in zip(*atoms)),
         "middle-wire singleton family")
    for i in range(6):
        bits = tuple(contacts[(t+i) % 6] for t in range(6))
        bright = [e for e in atoms if bits[e.index(1)] == 1]
        need(all(sum(e[t] for e in bright) == (bits[t]+1)//2 for t in range(6)),
             "original dial is not a phase coarse-graining")
    # Project a generic nonnegative P(t,u): convex mixtures cannot exceed the
    # largest score of one of its 36 deterministic phase-pair columns.
    raw_scores = {contacts[a]*(contacts[(b+1) % 6]+contacts[b])
                  + contacts[(a+2) % 6]*(contacts[(b+1) % 6]-contacts[b])
                  for a,b in product(range(6), repeat=2)}
    need(raw_scores == {-2,2}, "positive singleton products escaped Bell-locality")


def det3(a, b, c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0])
            + a[2]*(b[0]*c[1]-b[1]*c[0]))


def vertices4(normals, bound):
    """All vertices of |n.K| <= bound. Integer active-face arithmetic.

    Each bounded 4-polytope below has the origin strictly inside; every vertex
    has four independent active normals. Use cofactors only to solve those
    equalities, then check *all* halfspaces. No floating LP or tolerances.
    """
    normals = tuple(sorted(set(normals)))
    bound = F(bound)
    result = set()
    for rows in combinations(normals, 4):
        cof = []
        for i in range(4):
            other = rows[:i] + rows[i+1:]
            cof.append(tuple((-1)**(i+j) * det3(*(r[:j]+r[j+1:] for r in other))
                             for j in range(4)))
        determinant = dot(rows[0], cof[0])
        if not determinant:
            continue
        # Central symmetry: choosing the first sign positive covers each
        # antipodal pair exactly up to degeneracies of active constraints.
        for tail in product(SIGN, repeat=3):
            signs = (1,) + tail
            z = tuple(dot(signs, c) for c in zip(*cof))
            if all(abs(dot(n, z)) <= abs(determinant) for n in normals):
                vertex = tuple(bound * F(a, determinant) for a in z)
                result.update((vertex, mul(-1, vertex)))
    return result


def max_data(vertices):
    val = max(map(chsh, vertices))
    return val, {v for v in vertices if chsh(v) == val}


def check_centered_table(k, left, right):
    # P(a,b|u,v)=(1+a*b*E_uv)/4 at zero means. This identity follows from
    # binary counts; it is not an assumed Born rule. Summing checks both margins.
    for u, v in product(left, right):
        probs = {(a,b): (1+a*b*pair(u, k, v))*F(1, 4) for a,b in product(SIGN, repeat=2)}
        need(min(probs.values()) >= 0 and sum(probs.values()) == 1, "bad event table")
        for a in SIGN:
            need(sum(probs[a,b] for b in SIGN) == sum(probs[b,a] for b in SIGN) == F(1,2),
                 "non-flat marginal")


def conditional_join(contacts, orientation, offset):
    """An explicit one-way simulator of a proposed conditional preparation rule.

    Alice samples a fair sign and sends her dial and sign. Bob prepares the
    corresponding relabeled F5 vertex (the other sign selects its antipode)
    and applies the existing two-skip contact readout. The wire carrying
    Alice's choice is essential to THIS simulator. Exchangeability of the
    output distribution is not a Bell-local or spacelike implementation.
    """
    counts = {}
    for i, j in product(range(6), repeat=2):
        cell = {(a, b): 0 for a, b in product(SIGN, repeat=2)}
        for a, skip1, skip2 in product(SIGN, range(2), range(2)):
            remote = (offset + orientation*i + (3 if a == -1 else 0)) % 6
            b = contacts[(j-remote+skip1+skip2) % 6]
            cell[a, b] += 1
        need(sum(cell.values()) == 8, "incomplete conditional simulation")
        counts[i, j] = cell
    return counts


def check_dihedral_joins(contacts, steered):
    # These are automorphisms of the inferred operational hexagon; a reflection
    # has NOT thereby been shown to be a dynamically available F5 pulse.
    tables = {(s,r): conditional_join(contacts, s, r) for s,r in product(SIGN, range(6))}
    extremes = set()
    for (s, r), counts in tables.items():
        reverse = tables[s, (-s*r) % 6]
        def contrast(i, j):
            return F(sum(a*b*n for (a,b), n in counts[i,j].items()), 8)
        k = tuple(contrast(i,j) for i,j in product(range(2), repeat=2))
        extremes.add(k)
        for i,j in product(range(6), repeat=2):
            need(contrast(i,j) == pair(U6[i],k,U6[j]), "invalid joint effect extension")
            for a,b in product(SIGN, repeat=2):
                need(counts[i,j][a,b] == reverse[j,i][b,a], "reverse protocol differs")
                need(F(counts[i,j][a,b],8) == (1+a*b*pair(U6[i],k,U6[j]))/4,
                     "microscopic conditional simulator does not realize table")
    need(len(extremes) == 12 and extremes == steered, "dihedral hull incomplete")


def invariant_visibility(k):
    # Twirl by all simultaneous six-cycle rotations and reflections. The image
    # of a convex invariant family is its invariant slice; no search among only
    # the originally invariant vertices. Its amplitude is the mean diagonal.
    alpha = F(sum(pair(u,k,u) for u in U6), 6)
    for i,j in product(range(2), repeat=2):
        avg = F(sum(pair(U6[(s*i+r) % 6],k,U6[(s*j+r) % 6])
                    for s,r in product(SIGN, range(6))), 12)
        need(avg == alpha*GRAM[2*i+j], "invariant subspace not a line")
    return alpha


def symmetry_and_saturation(fringe, hexagon, observed, steered):
    # The target anti-correlated orientation is -GRAM. Never used to generate
    # the polyhedra: they came from local rows and the proposed joint rules.
    target = mul(-1, GRAM)
    row = tuple(pair(U6[0], target, u) for u in U6)
    need(row == mul(-1, fringe), "full target row")
    need(all(pair(u, target, v) == row[(j-i) % 6]
             for i,u in enumerate(U6) for j,v in enumerate(U6)), "all 36 pairs")
    check_centered_table(target, U6, U6)
    # Reversing the sign of Bob's bit is just outcome relabeling. Work with
    # positive same-dial correlations for the rest of the face checks.
    def perfect(k):
        return all(pair(u, k, u) == 1 for u in U)

    def rotation(k):
        return all(pair(u, k, v) == pair(U6[(i+1) % 6], k, U6[(j+1) % 6])
                   for i,u in enumerate(U6) for j,v in enumerate(U6))

    def exchange(k):
        return k[1] == k[2]

    obs_face = {v for v in observed if perfect(v)}
    skew = (1, 1, 0, 1)
    need(obs_face == {skew, (1, 0, 1, 1)} and all(rotation(v) for v in obs_face),
         "observed same-dial segment")
    # The affine hull on that segment has x=w=1, y+z=1, giving rotation
    # automatically. Arm exchange (or simultaneous reflection) imposes y=z.
    need(tuple((F(a)+b)/2 for a,b in zip(*obs_face)) == GRAM, "swap-selected midpoint")
    # Exchange + same-dial perfection here fix the correlations, NOT the means
    # of a merely positive observed table. Full shift covariance would fix the
    # means as well: a shift by three complements both local signs.
    bias = mul(F(1,5), hexagon[0])
    for u,v in product(U6,repeat=2):
        for a,b in product(SIGN,repeat=2):
            need(1+a*dot(u,bias)+b*dot(v,bias)+a*b*pair(u,GRAM,v) >= 0,
                 "biased positive-only counterexample failed")
    need({v for v in steered if perfect(v)} == {GRAM}, "perfect steering face")
    need(exchange(GRAM) and rotation(GRAM) and exchange((0,)*4) and rotation((0,)*4),
         "covariance alone does not prepare the source")
    # Full effects make the anti-source itself negative for one outcome.
    need(pair(F6[0], GRAM, F6[0]) == F(4,3)
         and (1+pair(F6[0], target, F6[0]))/4 == F(-1,12), "full-effect exclusion")
    # At |CHSH|=5/2 get E00=E11=1 after relabeling. Conditioning at each
    # makes the opposite signed state its unique exposed local vertex. Thus
    # m_B1=m_A0/2, m_B0=m_A0 and m_B0=m_A1/2, m_B1=m_A1.
    # The same-dial equalities imply m_B1=m_B0/2 and m_B0=m_B1/2.
    # Generate all four equations on (m_A0,m_A1,m_B0,m_B1) directly from
    # those local singleton faces. Zero-probability conditioning events do
    # not enter: their weights are zero in the unconditional marginal sum.
    eq = []
    for i,j in product(range(2), repeat=2):
        coeff = [0]*4
        coeff[i], coeff[2+j] = -hexagon[i][j], 1
        eq.append(coeff)
    determinant = sum((-1)**j * x * det3(*(r[:j]+r[j+1:] for r in eq[1:]))
                      for j,x in enumerate(eq[0]))
    need(abs(determinant) == F(3,4), "marginals not uniquely zero")
    return row


def run():
    contacts, fringe, hexagon = local_sector()
    terminal_effects(hexagon)
    change_reader_control(contacts)
    shared = shared_phase_control(contacts, fringe)
    # Eij = u_i K u_j^T requires the two local affine identities to survive
    # remote tests; the raw shared-phase control does NOT obey this premise.
    # For bilateral conditioning, BOTH affine extensions already follow from
    # the conditioned rows/columns below, rather than being additional axioms.
    # We are projecting measured correlations, not assuming there can be no
    # microscopic degrees of freedom invisible to these product tests.
    # For any biased state, correlation row E_i = sum_a p(a) a h_B|i,a
    # belongs to H when all conditionals do, by central symmetry/convexity.
    # Conversely every centered K satisfying the inequalities realizes them
    # with conditional signed states +/- E_i. Relabeling both arms at once and
    # mixing removes the means, keeping K and CHSH. Thus the projection onto
    # correlators below is exact; these are NOT counts of full biased states.
    measured = tuple(tensor(a,b) for a,b in product(U, repeat=2))
    forward = tuple(tensor(a,b) for a,b in product(U,N))
    backward = tuple(tensor(a,b) for a,b in product(N,U))
    steer = forward + backward
    polar = tuple(tensor(a,b) for a,b in product(N, repeat=2))
    observed = vertices4(measured, 1)
    steered = vertices4(steer, F(3, 2))
    full = vertices4(polar, F(9, 4))
    need(tuple(map(len, (observed, steered, full))) == (30, 12, 30), "vertex counts")
    products = {tensor(a,b) for a,b in product(hexagon, repeat=2)}
    local_bits = [a*b+a*y+x*b-x*y for a,x,b,y in product(SIGN, repeat=4)]
    need(set(local_bits) == {-2, 2}, "setting-independent predetermined bits escaped Bell bound")
    maxima = [max_data(vs) for vs in (products, observed, steered, full)]
    need([v for v, ws in maxima] == [F(7,4), 3, F(5,2), F(9,4)], "unexpected sharp bounds")
    need(maxima[1][1] == {(1,1,0,1)} and maxima[2][1] == {GRAM}
         and maxima[3][1] == {mul(F(3,4), (1,1,0,1))}, "unexpected exposed faces")
    # A single Bob dial's condition in the separately affine family is enough
    # for the 5/2 ceiling, not for uniqueness. Without separately affine
    # extension, conditioning at BOTH Bob dials actually used suffices for
    # this scalar bound: E01+E21=E11<=1 at B1, E00-E20=2x-z<=3/2 at B0.
    lone = (F(3,4), 1, 0, 1)
    need(all(abs(dot(n,lone)) <= 1 for n in measured)
         and all(abs(pair(n,lone,U[0])) <= F(3,2) for n in N)
         and lone != GRAM and chsh(lone) == F(5,2), "single-dial nonuniqueness")
    one_way = [vertices4(f,F(3,2)) for f in (forward,backward)]
    for vs in one_way:
        need(len(vs) == 30 and max_data(vs) == (F(5,2), {GRAM}), "one-way exposed face")
    need((1,F(1,2),1,F(1,2)) in one_way[0] - one_way[1], "one-way asymmetry")
    # Short dual certificates: |2x-z|<=3/2 is a first-column facet; |w|<=1.
    # For full effects use a,b,c,d in the first two full-observable coordinates.
    for k in steered:
        need(abs(2*k[0]-k[2]) <= F(3,2) and abs(k[3]) <= 1, "steering certificate")
    for k in full:
        a,b,c,d = (pair(i, k, j) for i,j in product(F6[:2], repeat=2))
        need((3*a+3*d+b+(a-c)+(d-c))/4 == chsh(k), "full certificate identity")
        need(max(map(abs,(a,d,b,a-c,d-c))) <= 1, "full certificate positivity")
    for vertices, left, right in ((steered,U6,F6), (steered,F6,U6), (full,F6,F6)):
        for k in vertices:
            check_centered_table(k,left,right)
    check_dihedral_joins(contacts, steered)
    visibilities = tuple(max(map(invariant_visibility, vs)) for vs in (products, observed, steered, full))
    need(visibilities == (F(1,2), 1, 1, F(3,4)), "D6-symmetric visibility limits")
    row = symmetry_and_saturation(fringe, hexagon, observed, steered)
    print("fixed dials A=(0,2), B=(1,0); actual local contrasts:", *fringe)
    print("all quotient-affine terminal raw-phase readers: exactly mixtures of six dials and constants")
    print("changing the reader: a single contact separates center mixtures (3/8 vs 1/4);")
    print("  middle-wire immediate contact 000001 in all 20 frames; positive singleton products imply |CHSH|<=2")
    print("shared opposite raw F5 phases:", *shared, "; |CHSH|=2 (not quotient-compatible)")
    print("sharp |CHSH|: local-stock products 7/4; general Bell-local <=2;")
    print("  positive measured events 3; bilateral hexagon conditioning 5/2; all affine effects 9/4")
    print("centered-correlator vertex counts (measured/conditioning/all effects):",
          len(observed), len(steered), len(full))
    print("12 conditioning vertices = 12 dihedral conditional joins; each has an explicit one-way simulator")
    print("one-way conditioning: 30 vertices each direction, unique +5/2 extremizer;")
    print("  one conditioned Bob dial + separate affinity: same bound, nonunique extremizer")
    print("simultaneous rotation/reflection |visibility| maxima (products/measured/conditioning/full):",
          *visibilities)
    print("at -5/2, unique full measured table: unbiased, first contrast row", *row)
    print("all-effect exclusion: same-facet correlation -4/3, one joint probability -1/12")
    print("joint extension, remote conditioning and source selection supplied; no spacelike or QM claim")


if __name__ == "__main__":
    run()
