"""A finite five-mode obstruction to the specific four-mode residue model.

Assume an additional equivalent accessible mode, the same equal three- and
four-arm junctions on selected arms, and the native signed Pauli operations
on selectable quartets (including double transpositions and even sign
flips). Supply a sharp axis preparation and one five-outcome axis readout.
Rank-one probabilities are identified under simultaneous reversible native
changes of preparation and effect, and depend on their rays, not the route
used to implement them. A four-mode preparation and effect with an unused
fifth arm retain the four-mode probabilities. The two readouts on the span
of arms i,j -- axes versus (e_i +/- e_j)/sqrt(2) -- give the SAME summed
probability. Both refinements occur in the native Pauli frames with a bypass;
the square root normalizes a ray, not an additional mixing gate.

The five-way contradiction needs neither continuity, arbitrary rational
rotations, universal covariance by angle, selection of a quadratic law, nor
sequential measurement updates. Each actual probability identification has
a checked native word. This is not an exclusion of all non-Born models, a
physical five-port measurement, or a derivation of quantum mechanics.
"""

import json
from collections import deque
from fractions import Fraction as F
from itertools import combinations, product

from scripts.probe_dense_readout_residue_countermodel import (
    native_frames,
    ray,
    weights4,
)
from scripts.probe_folded_carrier_parity_contexts import PAULIS, p_sign, word


def need(test, message):
    if not test:
        raise ArithmeticError(message)


def axes(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


I = axes(5)
E = I[4]
IDENT = tuple(range(5))


def star(*ix):
    return "star", ix


def flip(*ix):
    return "flip", ix


def route(v, circuit):
    for kind, ix in circuit:
        if kind == "star":
            need(len(ix) in (3,4), "not a native junction")
            common = F(2,len(ix))*sum(v[i] for i in ix)
            v = tuple(common-x if i in ix else x for i,x in enumerate(v))
        elif kind == "flip":
            need(len(ix) == 2, "expected native two-sign flip")
            v = tuple(-x if i in ix else x for i,x in enumerate(v))
        elif kind == "double_swap":
            a,b,c,d = ix
            need(len(set(ix)) == 4, "not a two-pair Pauli wire permutation")
            w = list(v)
            w[a], w[b], w[c], w[d] = v[b],v[a],v[d],v[c]
            v = tuple(w)
        else:
            raise ValueError("unknown gate")
    return v


def same_ray(a,b):
    # All comparisons here have the same vector norm on the two sides.
    return a == b or a == tuple(-x for x in b)


def effect(i,j=None,sign=1):
    return tuple(int(k == i)+sign*int(k == j) for k in range(5))


def wire_routes():
    # Confirm these local controls exist in this specific signed Pauli
    # group, not just in an abstract freely permutable five-wire model.
    native = {p_sign(word(w,PAULIS),s) for w in range(16) for s in range(2)}
    for a,b in combinations(range(4),2):
        need(tuple((-1 if i in (a,b) else 1)*(i+1) for i in range(4)) in native,
             "a local two-sign flip is absent")
    local = tuple(range(4))
    for g in ((0,1,2,3),(0,2,1,3),(0,3,1,2)):
        need(tuple(x+1 for x in route(local,(("double_swap",g),))) in native,
             "a local double transposition is absent")
    gens = []
    for a,b,c,d in combinations(IDENT,4):
        gens.extend(("double_swap",ix) for ix in ((a,b,c,d),(a,c,b,d),(a,d,b,c)))
    todo, found = deque([IDENT]), {IDENT:()}
    while todo:
        p = todo.popleft()
        for gate in gens:
            q = route(p,(gate,))
            if q not in found:
                found[q] = (*found[p],gate)
                todo.append(q)
    need(len(found) == 60, "selectable double swaps should generate all even wire permutations")
    fix = {p:w for p,w in found.items() if p[4] == 4}
    need(len(fix) == 12, "even wire permutations fixing source arm")
    return fix


def signed_match(u,v,fix):
    for p,circuit in fix.items():
        up = tuple(u[i] for i in p)
        if tuple(map(abs,up)) != tuple(map(abs,v)):
            continue
        for s in (1,-1):
            changes = tuple(i for i in IDENT if up[i] != s*v[i])
            if len(changes)%2:
                continue
            flips = tuple(flip(*changes[i:i+2]) for i in range(0,len(changes),2))
            word = (*circuit,*flips)
            if same_ray(route(u,word),v):
                return word
        # A zero slot can balance a sign flip without changing this vector.
        z = next((i for i in IDENT if up[i] == 0),None)
        if z is not None:
            changes = [i for i in IDENT if up[i] != v[i]]
            if len(changes)%2:
                changes.append(z)
            word = (*circuit,*(flip(*changes[i:i+2]) for i in range(0,len(changes),2)))
            if same_ray(route(u,word),v):
                return word
    return None


def event_alignment(u,v,fix):
    """An explicit word mapping both source axis and effect ray as required."""
    w = signed_match(u,v,fix)
    if w is not None:
        return w
    # Candidate extra junctions act only on the four source-orthogonal
    # wires. A necessary odd sign adjustment can also reverse the source
    # axis: the physical input ray, not its coordinate sign, is fixed.
    for ns in (0,2,4):
        for ix in combinations(IDENT,ns):
            changed = tuple(flip(*ix[i:i+2]) for i in range(0,ns,2))
            for t in combinations(range(4),3):
                left = (*changed,star(*t))
                w = signed_match(route(u,left),v,fix)
                if w is not None:
                    return (*left,*w)
    raise ArithmeticError(f"no native stabilizer route for {u} and {v}")


def preparations():
    a = (star(1,2,3,4),flip(0,4))
    b = (*a,star(0,1,2,3))
    c = (*b,flip(1,2),star(1,2,3))
    d = (*a,flip(0,1),star(1,2,3))
    k = (star(2,3,4),)
    ws = {"A":a,"B":b,"C":c,"D":d,"K":k,"T":()}
    data = {"A":(2,(0,1,1,1,1)), "B":(4,(3,1,1,1,2)),
            "C":(12,(9,1,1,-5,6)), "D":(6,(0,5,-1,-1,3)), "K":(3,(0,0,2,2,-1))}
    for name,(den,nums) in data.items():
        need(route(E,ws[name]) == tuple(F(x,den) for x in nums), "preparation word")
    return ws


def shared_pair_frames():
    # For every used pair choose a quartet containing it. Verify both
    # refinements occur as subsets of actual complete four-mode frames;
    # the two other outputs need not be the same in those frames.
    frames = native_frames()
    for i,j in combinations(range(4),2):
        old = axes(4)
        plus = tuple(int(k==i)+int(k==j) for k in range(4))
        minus = tuple(int(k==i)-int(k==j) for k in range(4))
        need(any(old[i] in f and old[j] in f for f in frames)
             and any(plus in f and minus in f for f in frames), "unavailable native pair refinement")
        need(all(2*(old[i][r]*old[i][c]+old[j][r]*old[j][c]) ==
                 plus[r]*plus[c]+minus[r]*minus[c] for r,c in product(range(4),repeat=2)),
             "either basis must give the same rank-two projector")


def residue_kernel(p,q):
    need(sum(any(x) for x in zip(p,q,strict=True)) <= 4, "unavailable spectator calibration")
    prob = F(sum(x*y for x,y in zip(p,q,strict=True))**2,
             sum(x*x for x in p)*sum(y*y for y in q))
    scaled = 4*prob
    need(scaled.denominator%2 == 1, "these are not four-mode calibrated rays")
    value = (scaled.numerator*pow(scaled.denominator,-1,8))%8
    need(value in (0,1,2,4), "not a calibrated four-mode residue value")
    return F(value,4)


def certificate():
    ws, fix = preparations(), wire_routes()
    shared_pair_frames()
    # Pulling back by the inverse of each preparation makes every source
    # the fixed e_4. All gates used here are involutions.
    def pulled(row,q):
        return route(q,reversed(ws[row]))

    paths = {}

    def identify(name,row,q,other,ref):
        u,v = pulled(row,q),pulled(other,ref)
        w = event_alignment(u,v,fix)
        need(same_ray(route(E,w),E) and same_ray(route(u,w),v), "invalid physical event identification")
        paths[name] = w

    def four(row,q):
        return residue_kernel(route(E,ws[row]),q)

    fhalf = four("A",effect(1))
    fsixth = four("D",effect(2))
    gthird = four("K",effect(3,4))
    zero = four("T",effect(0,1))
    need((fhalf,fsixth,gthird,zero) == (F(1,4),F(1,4),F(1,2),0)
         and four("T",effect(0)) == 0, "four-mode seed data")
    # Independent calibration from the ORIGINAL static axis-prepared model:
    # even the symmetric pure-preparation kernel need not be assumed here.
    # Each pulled-back effect is generated inside an actual quartet from
    # a native coordinate or balanced-pair ray; the source is simply e_4.
    for row,q,local_word,omit,expected in (
        ("A",effect(1),(star(1,2,3,4),),0,fhalf),
        ("D",effect(2),(star(1,2,3),flip(1,4),star(1,2,3,4)),0,fsixth),
        ("K",effect(3,4),(star(2,3,4),),0,gthird),
        ("T",effect(0,1),(),2,zero),
    ):
        old = route(q,local_word)
        need(same_ray(old,pulled(row,q)) and all(omit not in ix for _,ix in local_word)
             and old[omit] == E[omit] == q[omit] == 0, "old calibration used its omitted wire")
        compact = ray(tuple(z for i,z in enumerate(old) if i != omit))
        need(F(weights4(compact)[3],4) == expected, "native calibrated static response")
    # D and A have four occupied arms; the omitted e_0 output is zero by
    # the bypass contract (or pulling e_0 back to a distinct original axis).
    # Its union with their preparations can use five arms, so verify that
    # separate zero by source-axis pullback, not by four-mode support.
    identify("A zero axis","A",effect(0),"T",effect(0))
    identify("D zero axis","D",effect(0),"T",effect(0))
    identify("A half pair two signs","A",effect(0,1,-1),"A",effect(0,1))
    identify("D sixth pair two signs","D",effect(0,2,-1),"D",effect(0,2))
    ghalf,gsixth = fhalf/2,fsixth/2

    for row,i,j,sg,val in [
        *(("B",i,j,sg,t) for i,j in combinations((1,2,3),2) for sg,t in ((1,"half"),(-1,"zero"))),
        ("C",1,2,1,"sixth"),("C",1,2,-1,"zero"),
        *(("C",i,3,sg,t) for i in (1,2) for sg,t in ((1,"third"),(-1,"half"))),
    ]:
        source,ref = {"half":("A",effect(0,1)), "sixth":("D",effect(0,2)),
                      "third":("K",effect(3,4)), "zero":("T",effect(0,1))}[val]
        identify(f"{row} pair {i} {j} sign {sg}",row,effect(i,j,sg),source,ref)
    identify("B untouched half","B",effect(4),"A",effect(1))
    identify("C untouched half","C",effect(4),"A",effect(1))
    identify("C untouched three quarters","C",effect(0),"B",effect(0))

    # In B each of the three pair sums is ghalf+zero=1/8. Solving the
    # three simultaneous equalities forces the individual 1/16, without
    # assuming an angle/radial formula for different coordinates.
    b_small = (ghalf+zero)/2
    b_first = 1-3*b_small-fhalf
    # In C the (1,2) sum is gsixth+zero and the (1,3), (2,3) sums both
    # equal gthird+ghalf. The latter two equalities force slots 1 and 2
    # equal; neither equality presupposes symmetry of an unknown response.
    c_small = (gsixth+zero)/2
    c_third = gthird+ghalf-c_small
    forced = (b_first,c_small,c_small,c_third,fhalf)
    need(forced == tuple(map(F,("9/16","1/16","1/16","9/16","1/4")))
         and sum(forced) == F(3,2), "five-way obstruction")
    # With the calibrated orthogonal zeros, eliminating all intermediates
    # gives the scalar necessity 4*gthird + fsixth - fhalf = 0.
    # The geometric names describe overlaps, not a radiality assumption.
    residual = 4*gthird+fsixth-fhalf
    need(residual == 4*(sum(forced)-1) == 2, "eliminated certificate")
    # Ordinary squared-overlap probabilities supply a non-vacuity control
    # for precisely these same circuits, identifications and refinements.
    def born(row,q):
        u = pulled(row,q)
        return F(u[4]**2,sum(y*y for y in u))

    born_inputs = (born("A",effect(1)),born("D",effect(2)),born("K",effect(3,4)))
    ba,bd,bk = born_inputs
    born_axis = tuple(born("C",ei) for ei in I)
    need(born_inputs == (F(1,4),F(1,36),F(1,18)) and 4*bk+bd-ba == 0
         and sum(born_axis) == 1, "ordinary squared-overlap control should survive")
    return {"preparation_words":ws,"event_alignment_words_after_preparation_pullback":paths,
            "forced_axis_weights_on_C":list(map(str,forced)), "sum":str(sum(forced)),
            "required_sum":"1","extra_mode_count":1,"native_alignment_count":len(paths),
            "eliminated_necessary_equation_with_orthogonal_zeros":"4*gthird+fsixth-fhalf=0",
            "residue_left_hand_side":str(residual),"Born_control_left_hand_side":"0",
            "Born_control_axis_weights_on_C":list(map(str,born_axis))}


def unit_basis_control():
    # For measurement axes and rational unit preparations only, a radial
    # extension to five slots EXISTS. For primitive a/t with norm one,
    # odd t implies exactly one odd coordinate (five odd would give 5
    # modulo 8). For v2(t)=1 four are odd and the fifth is divisible by 4.
    # For m=v2(t)>=2 four are odd and the fifth is 2 modulo 4. Thus the
    # required weights by denominator depth obey 4F_m + F_(m-1) = 1.
    # This is NOT an extension to the mixed pair refinements above.
    weights = {0:F(1),1:F(1,4)}
    for m in range(2,16):
        weights[m] = (1-weights[m-1])/4
    need(all(0 <= w <= 1 for w in weights.values())
         and weights[2] == F(3,16) and weights[3] == F(13,64), "axis-only benchmark")
    return {"value_even_numerator_odd_denominator":"0","value_odd_over_odd":"1",
            "value_odd_over_twice_odd":"1/4","deeper_recurrence":"F_m=(1-F_(m-1))/4 for m>=2",
            "next_two_values":[str(weights[2]),str(weights[3])],
            "scope":"rational unit-coordinate readout alone; no mixed pair basis"}


def probe():
    return {"scope":"five equivalent modes with the stated spectator, event and shared-effect contracts",
            "specific_four_mode_family_extension":certificate(),"unit_basis_only_control":unit_basis_control(),
            "boundary":"The certificate excludes this residue extension, not all non-Born models. "
                       "Mode equivalence, spectator independence, preparation and shared readout are assumptions."}


if __name__ == "__main__":
    print(json.dumps(probe(),sort_keys=True))
