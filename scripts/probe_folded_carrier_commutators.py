"""Conditional central order-bit extensions of the five recovered folded-carrier toggles.

Extra hypothesis: reversible words form a group projecting ONTO the regular
translation group V; its ENTIRE kernel is {1,z}, with z central of order two.
No binary phase, signed lift, commutator signal or readout comes from the
anonymous graph alone. Define [X,Y]=z^B(x,y), X^2=z^Q(x) for lifts.
Centrality makes [XY,Z]=[X,Z][Y,Z]; hence B is alternating bilinear on
V over F2. (XY)^2=X^2 Y^2 [Y,X] gives its quadratic refinement Q. Neither
quantity changes when lifts acquire central signs. For a fixed B, two Qs
differ by a linear function. Basis lifts, their squares, ordered swaps and
z determine every product by a unique ordered-word normal form, so these
Q classify extensions with the quotient and central bit fixed.

S5 is transitive on distinct direction pairs, so the invariant B is zero
or 1 on all such pairs. The latter descends since each direction meets four
others, and is nondegenerate in dimension four. The sole S5-invariant Q
then has Q(g_i)=0: their sum vanishes, the ten pair terms sum to zero, and
five equal squares must sum to zero. Changes of ROOT labels made together
with a mark do not change their relative translation. Using a nonneighbor
mark t to choose Q0+B(t,.) instead changes the lift law, not just labels
or the representative section. Under the smaller 3+2 stabilizer, zero and
rank-two commutators are also allowed. No symmetry demands the nonzero case.

An invariant sign LAW does not give five strictly permutable bare lifts.
Their ordered fivefold product lies in {1,z}. An odd permutation reverses
its sign when all distinct directions anticommute; no rephasing of a
single chosen lift per direction removes that obstruction. Normalize that
ordered product to 1, then compensate odd permutations by flipping ALL
five lift signs. Five is odd, so this cancels the order sign and the
corrections compose. Uncorrected even permutations survive in the relevant
stabilizer. This is transport of a signed model, not an uncorrected raw rewire.

Every example below acts by ordinary deterministic permutations on 32
classical states (v,bit). Forget the bit, or prepare it uniformly without
a retained comparison, and the two orders are indistinguishable on that
readout. If the bit is physically readable/labeled it is a classical tag;
a quantum global phase is NOT a directly readable binary register. No
joint instrument for compatible observables, contextuality, experimental
outcome, or quantum reconstruction is supplied.
"""

import json
from collections import Counter
from itertools import combinations, permutations, product

from scripts.probe_anonymous_folded_carrier import forced_completion, square_directions

V = tuple(range(16))
BASIS = (1, 2, 4, 8)
DIRECTIONS = (*BASIS, 15)
BIT = 16
EDGES = tuple(combinations(range(4), 2))


def need(test, why):
    if not test:
        raise AssertionError(why)


def linear(images):
    out = [0]
    for y in images:
        out += [x ^ y for x in out]
    return tuple(out)


def recover():
    a = forced_completion()
    _, classes = square_directions(a)
    ops = []
    for edges in classes:
        op = {x:y for u,v in edges for x,y in ((u,v),(v,u))}
        ops.append(tuple(op[x] for x in range(len(a))))
    ops.sort(key=lambda f: f[0])  # root and four basis names only for the finite calculation
    chart = [0]
    for f in ops[:4]:
        chart += [f[x] for x in chart]
    need(len(ops) == 5 and len(set(chart)) == 16 and
         all(f[chart[x]] == chart[x^d] for f,d in zip(ops,DIRECTIONS,strict=True) for x in V),
         "recovered operations do not have exactly the proposed relation")
    return {d:tuple(f) for d,f in zip(DIRECTIONS,ops,strict=True)}


def pairing(mask):
    def value(x,y):
        return sum(((x >> i & 1)*(y >> j & 1) ^ (x >> j & 1)*(y >> i & 1))
                   for k,(i,j) in enumerate(EDGES) if mask >> k & 1) % 2
    return tuple(tuple(value(x,y) for y in V) for x in V)


def rank_b(b):
    radical = sum(not any(row) for row in b)
    need(radical in (1,2,4,8,16), "not a subspace size")
    return 4-(radical.bit_length()-1)


def invariants(actions):
    out = []
    for mask in range(64):
        b = pairing(mask)
        if all(b[a[x]][a[y]] == b[x][y] for a in actions for x,y in combinations(BASIS,2)):
            out.append((mask,rank_b(b)))
    return out


def parity(p):
    return sum(p[i]>p[j] for i,j in combinations(range(len(p)),2)) % 2


class Extension:
    def __init__(self,b,twist,linear_squares=None):
        # Lower-triangular cocycle: basis lifts multiplied in increasing order
        # cost no sign. Diagonal terms implement the squares B(t,e_i).
        diag = tuple(b[twist][x] for x in BASIS) if linear_squares is None else linear_squares
        low = [[int(i>j)*b[x][y] if i != j else diag[i] for j,y in enumerate(BASIS)]
               for i,x in enumerate(BASIS)]
        c = [[sum(low[i][j] for i in range(4) if x >> i & 1 for j in range(4) if y >> j & 1)%2
              for y in V] for x in V]
        self.q = tuple(c[x][x] for x in V)
        self.mul = [[x^y^(BIT*c[x%16][y%16]) for y in range(32)] for x in range(32)]
        self.lifts = (*BASIS,15^BIT*self.q[15])  # normalize the fivefold ordered product to +1
        self.c = c
        self.b = b
        self.check()

    def word(self, letters):
        result = 0
        for letter in letters:
            result = self.mul[result][letter]
        return result

    def check(self):
        m, q = self.mul, self.q
        all_states = set(range(32))
        need(all(set(row) == all_states for row in m) and
             all(m[m[x][y]][z] == m[x][m[y][z]] for x,y,z in product(range(32),repeat=3)),
             "not a regular associative signed permutation model")
        need(self.word(self.lifts) == 0 and all(m[x][BIT] == m[BIT][x] == x^BIT for x in range(32)),
             "bad central bit or direction relation")
        need(all(m[x][y]^m[y][x] == BIT*self.b[x%16][y%16] and m[x][x] == BIT*q[x%16]
                 for x,y in product(range(32),repeat=2)), "commutator or square reported incorrectly")
        need(all(q[x^y] == q[x]^q[y]^self.b[x][y] for x,y in product(V,repeat=2)), "polar identity")


def transported(src, dst, p):
    """A true signed-lift isomorphism with a compensated action on normalized lifts."""
    sign = BIT*parity(p)
    basis_images = [(dst.lifts[p[i]] ^ sign) for i in range(4)]
    phi = [dst.word(g for i,g in enumerate(basis_images) if x >> i & 1) ^ (x & BIT) for x in range(32)]
    need(len(set(phi)) == 32 and all(phi[g] == dst.lifts[p[i]] ^ sign for i,g in enumerate(src.lifts)),
         "mapping did not compensate the relation on all five ports")
    # Test all left transitions by the generators and center, not only squares.
    need(all(phi[src.mul[g][x]] == dst.mul[phi[g]][phi[x]] for g in (*src.lifts,BIT) for x in range(32)),
         "signed map failed group/lift transport")
    return tuple(phi)


def prep_controls(model):
    a,b = model.lifts[:2]
    m = model.mul
    ab, ba = m[a][b], m[b][a]
    need(all(m[ab][s] == m[ba][s]^BIT for s in range(32)), "no retained order difference")
    need(all(sorted((m[ab][s],m[ab][s^BIT])) == sorted((m[ba][s],m[ba][s^BIT])) for s in V),
         "a fresh unknown uniform bit revealed the order")
    # Every normalized section change adds delta f(x,y). Single-vertex phase
    # functions span all 2^15 choices, so checking these proves the linear statement.
    for at in V[1:]:
        for x,y in product(V,repeat=2):
            df = (x==at)^(y==at)^((x^y)==at)
            dflip = (y==at)^(x==at)^((y^x)==at)
            need(df == dflip and (x!=y or not df), "section gauge changed a commutator or square")
    return {"rephase_span_dimension":15, "calibrated_bit_order_differences":32,
            "uniform_bit_output_distributions_distinct":False}


def probe():
    recover()
    perms = list(permutations(range(5)))
    actions = {p:linear([DIRECTIONS[p[i]] for i in range(4)]) for p in perms}
    marked = [p for p in perms if set(p[3:]) == {3,4}]
    full_forms = invariants(actions.values())
    marked_forms = invariants([actions[p] for p in marked])
    need(full_forms == [(0,0),(63,4)] and sorted(r for _,r in marked_forms) == [0,2,2,4],
         "invariant alternating form census")
    b = pairing(63)
    models = {t:Extension(b,t) for t in V}
    base = models[0]
    need(all(b[x][y] == int(x!=y) for x,y in product(DIRECTIONS,repeat=2)) and
         all(m.q[x] == base.q[x]^b[t][x] for t,m in models.items() for x in V), "nonzero pairing/twists")
    qset = {m.q:t for t,m in models.items()}
    need(len(qset) == 16, "missing quadratic refinement")
    s5_orbits = {frozenset(act[t] for act in actions.values()) for t in V}
    tmark = DIRECTIONS[3]^DIRECTIONS[4]
    fixed_marked = {t for t in V if all(actions[p][t] == t for p in marked)}
    need(fixed_marked == {0,tmark} and {t for t in V if all(a[t] == t for a in actions.values())} == {0},
         "marked/unmarked invariant refinements")
    representatives = {"root":0,"neighbor":DIRECTIONS[0],"nonneighbor":tmark}
    summaries = {}
    for label,t in representatives.items():
        q = models[t].q
        zeroes = q.count(0)
        involutions = sum(models[t].mul[x][x] == 0 for x in range(1,32))
        need(involutions == 2*zeroes-1, "order-two element count")
        summaries[label] = {"twists_in_direction_permutation_orbit":len(next(o for o in s5_orbits if t in o)),
                            "squares_on_five_ports":[q[g] for g in DIRECTIONS],
                            "zeroes_including_origin":zeroes,"arf":0 if zeroes==10 else 1,
                            "nonidentity_involutions_in_extension":involutions}
    need([summaries[k]["zeroes_including_origin"] for k in representatives] == [6,6,10] and
         [summaries[k]["squares_on_five_ports"] for k in representatives] ==
         [[0,0,0,0,0],[0,1,1,1,1],[0,0,0,1,1]], "signed refinement controls")
    # Compare by arbitrary symplectic linear changes as well as by graph directions.
    symplectic = []
    gl_count = 0
    for cols in permutations(V[1:],4):
        a = linear(cols)
        if len(set(a)) == 16:
            gl_count += 1
            if all(b[a[x]][a[y]] == b[x][y] for x,y in combinations(BASIS,2)):
                symplectic.append(a)
    all_q_orbits = {frozenset(qset[tuple(m.q[a[x]] for x in V)] for a in symplectic) for m in models.values()}
    need(gl_count == 20160 and len(symplectic) == 720 and sorted(map(len,all_q_orbits)) == [6,10],
         "unrestricted symplectic comparison changed")
    root_maps = {}
    unsigned, compensated = 0, 0
    for p,a in actions.items():
        sigma = parity(p)
        need(base.word(base.lifts[j] for j in p) == BIT*sigma, "fivefold order sign")
        unsigned += int(sigma == 0)
        for t,src in models.items():
            target = models[a[t]]
            phi = transported(src,target,p)
            need(all(phi[x]%16 == a[x%16] for x in range(32)), "wrong quotient action")
            compensated += 1
            if not t:
                root_maps[p] = phi
    for p,q in product(perms,repeat=2):
        pq = tuple(p[i] for i in q)
        need(all(root_maps[p][root_maps[q][x]] == root_maps[pq][x] for x in (*base.lifts,BIT)),
             "compensated S5 is not a genuine action")
    commuting = Extension(pairing(0),0)
    need(all(commuting.mul[x][y] == commuting.mul[y][x] for x,y in product(V,repeat=2)),
         "negative control on the exact same quotient")
    marked_commuting = Extension(pairing(0),0,tuple(b[tmark][x] for x in BASIS))
    need(all(marked_commuting.mul[x][y] == marked_commuting.mul[y][x] for x,y in product(V,repeat=2)) and
         [marked_commuting.q[g] for g in DIRECTIONS] == [0,0,0,1,1],
         "squared marked lifts alone should not imply order sensitivity")
    return {"scope":"supplied central binary group extension; classical signed permutations, no joint readout",
            "invariant_alternating_forms_by_row_bits_and_rank":{"S5":full_forms,"marked_S3xS2":marked_forms},
            "all_refinements":len(qset),"fixed_quotient_distinct_classes":16,
            "direction_orbit_representatives":summaries,
            "unrestricted_symplectic_refinement_orbit_sizes":sorted(map(len,all_q_orbits)),
            "quadratic_zero_count_histogram":dict(sorted(Counter(m.q.count(0) for m in models.values()).items())),
            "root_normalized_bare_port_relabels":unsigned,"root_compensated_port_relabels":len(root_maps),
            "all_refinement_signed_transports_checked":compensated,
            "word_controls":prep_controls(base),"trivial_pairing_classical_control":True,
            "commuting_marked_control_with_same_five_generator_squares":True}


if __name__ == "__main__":
    print(json.dumps(probe(),separators=(",",":")))
