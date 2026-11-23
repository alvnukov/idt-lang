"""Compile a rational reflection with equal-arm junctions and explicit signs.

A d-arm real reciprocal junction is S_d=2J/d-I. Selectable groups of arms,
coherent real addition, a clocked route, and blank work ports are supplied.
To copy one mode to m^2 equal leaves, S_(2k) takes a single heavy input h
and 2k-1 blanks to -(k-1)h/k on the original wire and h/k elsewhere.
Reverse the heavy sign and continue there for k=m,m-1,...,2. All m^2
outputs now equal the original input divided by m; no amplitude is cloned.

For integer w != 0 encode data x_i into w_i^2 leaves equal to x_i/w_i
when w_i != 0. The N=sum w_i^2 leaves have total w dot x. S_N returns
2(w dot x)/N - x_i/w_i at every leaf in block i. The resulting block
constants are in the same encoded subspace, so the EXACT reverse encoder
cleans the work ports and returns (2ww^t/N-I)x. Zero-coefficient inputs
must be negated separately. The selected wires do not depend on x.

Two implementations of the sign contract are tested. Single-rail data
use supplied even sign flips with a blank spare. Unsigned equal junctions
and permutations by themselves preserve the sum and cannot implement every
single-rail reflection with clean work. In a supplied differential encoding
(x,-x), duplicate each junction on both rails and swap a rail pair with S_2
for a logical minus. This second circuit uses only equal junctions; it
does not generate the opposite inputs from a raw x plus blank. No fixed
finite set of allowed valences, timeless scattering network, detector law,
probability assignment or physical implementation is inferred.

For r nonzero coefficients in n modes, width is N+n-r before signs or
rail doubling, and the splitter forward/backward uses 2*(sum |w_i|-r)
junctions. The total input incidences of these junctions are
2*(N+sum |w_i|-2r), plus N at the center if N>1. Thus storage and
wire incidences per reflection are O(N+n), not logarithmic in the
coefficient heights. A fixed finite rational alphabet has a genuine
denominator obstruction even with arbitrarily many clean auxiliaries.
"""

import json
from dataclasses import dataclass
from fractions import Fraction as F
from math import gcd, lcm


def need(test, message):
    if not test:
        raise ArithmeticError(message)


def dots(x,y):
    return sum(a*b for a,b in zip(x,y,strict=True))


def identity(n):
    return tuple(tuple(int(i==j) for j in range(n)) for i in range(n))


def mv(a,x):
    return tuple(dots(row,x) for row in a)


def canonical(v):
    den = lcm(*(F(t).denominator for t in v))
    a = tuple(int(t*den) for t in v)
    g = gcd(*a)
    need(g != 0, "zero Householder normal")
    sg = 1 if next(t for t in a if t) > 0 else -1
    return tuple(sg*t//g for t in a)


def line_reflection(w,x):
    s = F(2*dots(w,x),dots(w,w))
    return tuple(s*a-t for a,t in zip(w,x,strict=True))


def plane_reflection(w,x):
    return tuple(-t for t in line_reflection(w,x))


@dataclass(frozen=True)
class Circuit:
    data: int
    width: int
    gates: tuple


def star(slots):
    return "star",tuple(slots)


def minus(i):
    return "minus",(i,)


def compile_line(w):
    """Return physical-independent logical routing for the exact supplied w."""
    need(all(type(i) is int for i in w) and any(w), "nonzero integer normal required")
    n = len(w)
    next_wire = n
    forward,blocks = [],[]
    for i,a in enumerate(w):
        if not a:
            continue
        leaves = [i]
        if a < 0:
            forward.append(minus(i))
        for k in range(abs(a),1,-1):
            new = tuple(range(next_wire,next_wire+2*k-1))
            next_wire += len(new)
            forward.extend((star((i,*new)),minus(i)))
            leaves.extend(new)
        need(len(leaves) == a*a, "wrong number of unit leaves")
        blocks.append((i,tuple(leaves)))
    all_leaves = tuple(j for _,block in blocks for j in block)
    norm, occupied = dots(w,w),len(blocks)
    m = sum(map(abs,w))-occupied
    mid = (star(all_leaves),) if norm > 1 else ()
    reverse = tuple(reversed(forward))
    zeros = tuple(minus(i) for i,a in enumerate(w) if not a)
    gates = (*forward,*mid,*reverse,*zeros)
    need(len(set(all_leaves)) == len(all_leaves) == norm and next_wire == n+norm-occupied,
         "raw-site census")
    need(sum(k=="star" for k,_ in gates) == 2*m+int(norm>1)
         and sum(len(ix) for k,ix in gates if k=="star")
         == 2*(norm+sum(map(abs,w))-2*occupied)+(norm if norm>1 else 0), "junction incidence census")
    return Circuit(n,next_wire,gates), tuple(forward),all_leaves


def physical(c, *, dual):
    gates = []
    if dual:
        for kind,ix in c.gates:
            if kind == "star":
                gates.extend(star(2*i+s for i in ix) for s in (0,1))
            else:
                need(kind == "minus" and len(ix) == 1, "unknown logical operation")
                gates.append(star((2*ix[0],2*ix[0]+1)))
        return Circuit(2*c.data,2*c.width,tuple(gates))
    # Logical signs on data or work are actual TWO-wire sign changes.
    # Keep at least four available wires if that sign element is supplied
    # as a signed Pauli operation on a selected quartet.
    spare = c.width
    for kind,ix in c.gates:
        if kind == "star":
            gates.append(star(ix))
        else:
            need(kind == "minus" and len(ix) == 1, "unknown logical operation")
            gates.append(("flip_two",(ix[0],spare)))
    return Circuit(c.data,max(c.width+1,4),tuple(gates))


def execute(gates, state):
    out = list(state)
    for kind,ix in gates:
        need(len(ix)==len(set(ix)) and all(0 <= i < len(out) for i in ix), "invalid physical gate")
        if kind == "star":
            need(len(ix)>=2, "identity junction should have been omitted")
            common = F(2,len(ix))*sum(out[i] for i in ix)
            for i in ix:
                out[i] = common-out[i]
        elif kind == "flip_two":
            need(len(ix)==2, "single-rail sign not paired")
            for i in ix:
                out[i] = -out[i]
        else:
            raise ValueError("unknown physical operation")
    return tuple(out)


def run(c,x,*,dual):
    u = physical(c,dual=dual)
    data = tuple(s*t for t in x for s in (1,-1)) if dual else tuple(x)
    need(len(data)==u.data,"unexpected input dimension")
    out = execute(u.gates,(*data,*(0,)*(u.width-u.data)))
    need(not any(out[u.data:]), "an initially blank work wire leaked")
    if dual:
        need(all(out[2*i] == -out[2*i+1] for i in range(c.data)), "broken differential encoding")
        return out[:u.data:2]
    return out[:u.data]


def factor(u):
    """At c!=e_j, 2(c-e_j).c = ||c-e_j||^2, so H_(c-e_j)c=e_j.

    Earlier aligned columns are untouched: orthogonality gives zeros in
    those slots of the new normal. One reflection per nonaligned column
    suffices, and the inverse of the left reduction executes U.
    """
    n = len(u)
    need(n >= 1 and all(len(r)==n for r in u), "nonempty square transform required")
    cols = tuple(zip(*u,strict=True))
    eye = identity(n)
    need(all(dots(v,w)==eye[i][j] for i,v in enumerate(cols) for j,w in enumerate(cols)),
         "target not orthogonal")
    normals = []
    for j in range(n):
        x = cols[j]
        if x == eye[j]:
            continue
        w = canonical(tuple(a-b for a,b in zip(x,eye[j],strict=True)))
        need(not any(w[:j]), "column alignment disturbed earlier fixed axes")
        cols = tuple(plane_reflection(w,v) for v in cols)
        need(cols[j] == eye[j], "failed column alignment")
        normals.append(w)
    need(cols == eye and len(normals)<=n, "orthogonal factorization")
    return tuple(reversed(normals))


def compile_orthogonal(u):
    normals = factor(u)
    n = len(u)
    width, gates = n,[]
    for w in normals:
        c,_,_ = compile_line(w)
        gates.extend(c.gates)
        width = max(width,c.width)
    if len(normals)%2:
        # Ordinary H_w=I-2P is MINUS the compiled line reflection. This
        # correction is essential for exact amplitudes, not just ray names.
        gates.extend(minus(i) for i in range(n))
    return Circuit(n,width,tuple(gates)),normals


def audit(c, transform):
    # Linearity means the complete coordinate columns verify the actual
    # circuit on every input. An additional mixed rational input and the
    # reverse gate order are useful independent wiring/cleanup controls.
    checks = (*identity(c.data), tuple(F((-1)**j*(j+2),j+1) for j in range(c.data)))
    for dual in (False,True):
        inv = Circuit(c.data,c.width,tuple(reversed(c.gates)))
        for x in checks:
            y = run(c,x,dual=dual)
            need(y == transform(x) and run(inv,y,dual=dual) == x, "basis, mixed input or inverse mismatch")


def audit_encoder(w,c,forward,leaves):
    encoder = physical(Circuit(c.data,c.width,forward),dual=False)
    for x in (w,tuple(F(1-i,2+i) for i in range(len(w)))):
        out = execute(encoder.gates,(*x,*(0,)*(encoder.width-c.data)))
        expected = tuple(F(x[i],a) for i,a in enumerate(w) if a for _ in range(a*a))
        need(tuple(out[i] for i in leaves) == expected and
             all(out[i]==x[i] for i,a in enumerate(w) if not a) and
             not any(out[c.width:]) and dots(out,out) == dots(x,x), "encoded leaf values or norm")


def complement_alignment(x,y,j):
    need(len(x)==len(y) and 0<=j<len(x) and x[j]==y[j] and dots(x,x)==dots(y,y),
         "equal named entry and equal total norm required")
    slots = tuple(i for i in range(len(x)) if i != j and x[i]!=y[i])
    if not slots:
        return {"touched_data_slots":[],"squared_integer_normal_norm":0}
    # Restrict to differing coordinates BEFORE compiling, so the named
    # arm j is not even temporarily flipped or used as a sign spare.
    w = canonical(tuple(x[i]-y[i] for i in slots))
    c,_,_ = compile_line(w)
    c = Circuit(c.data,c.width,(*c.gates,*(minus(i) for i in range(c.data))))
    for dual in (False,True):
        p = physical(c,dual=dual)
        q = 2 if dual else 1
        nraw = q*len(x)
        active = tuple(q*i+k for i in slots for k in range(q))
        embedded = (*active,*range(nraw,nraw+p.width-p.data))
        word = tuple((kind,tuple(embedded[i] for i in ix)) for kind,ix in p.gates)
        protected_rails = {q*j+k for k in range(q)}
        need(all(protected_rails.isdisjoint(ix) for _,ix in word), "comparison used the named port")
        initial = tuple(s*t for t in x for s in (1,-1)) if dual else tuple(x)
        target = tuple(s*t for t in y for s in (1,-1)) if dual else tuple(y)
        out = execute(word,(*initial,*(0,)*(p.width-p.data)))
        need(out[:nraw] == target and not any(out[nraw:]), "native complement alignment")
    return {"touched_data_slots":slots,"squared_integer_normal_norm":dots(w,w)}


def negative_controls():
    w,x = (2,1),(1,0)
    c,forward,leaves = compile_line(w)
    # One unplanned blank on S_(N+1) receives a real signal. Keep the
    # sign spare separate so it cannot account for that extra output.
    plus = c.width
    wrong = Circuit(2,c.width+1,(*forward,star((*leaves,plus)),*reversed(forward)))
    net = physical(wrong,dual=False)
    out = execute(net.gates,(*x,*(0,)*(net.width-2)))
    need(out[plus] == F(2,3), "wrong-valence control")
    # Dirty work is not erased. In this exact construction the logical
    # space is invariant; by orthogonality its complement is invariant too.
    net = physical(c,dual=False)
    bad = [0]*net.width
    bad[:2] = x
    bad[2] = 1
    out = execute(net.gates,bad)
    need(out[:2] == line_reflection(w,x) and out[2] == -1, "dirty work was not preserved in norm")
    # Omitting the orientation of a mixed-sign coefficient realizes the
    # wrong line reflection, even if an ideal circuit still cleans up.
    good = line_reflection((-2,1),x)
    unsigned = run(c,x,dual=False)
    need(good[1] == F(-4,5) and unsigned[1] == F(4,5), "mixed-sign witness")
    # On raw data the uncorrected zero-coefficient bypass would wrongly
    # return +1. This also proves a limitation of *all* unsigned clean
    # single-rail S_d/permutation circuits, which preserve the total sum.
    z = line_reflection((1,0),(0,1))
    need(z == (0,-1) and sum(z) != 1, "bare unsigned total-sum obstruction")
    return {"extra_central_blank_output":"2/3","dirty_internal_one_returns":"-1",
            "wrong_coefficient_sign_changes_second_output":["-4/5","4/5"],
            "unsigned_raw_junctions_and_swaps_alone_cannot_realize_every_reflection":True}


def finite_alphabet_control(denominators):
    # For any nonempty finite list of rational gate-entry denominators,
    # m can be even and divisible by all of them. A product of such gates
    # remains in the ring inverting their primes; clean workspace or wire
    # signs do not change that. A 2D rational rotation escapes this ring.
    need(all(type(d) is int and d >= 1 for d in denominators), "invalid gate denominator")
    m = lcm(2,*denominators)
    d = 1+m*m
    a,b = F(1-m*m,d),F(2*m,d)
    need(a*a+b*b == 1 and b.denominator == d > 1 and gcd(d,m) == 1,
         "new rotation denominator not separated")
    return {"chosen_gate_entry_denominators":denominators, "rotation_entries":[str(a),str(b)],
            "denominator_coprime_to_all_supplied_denominators":d}


def probe():
    lines = []
    for w in ((1,),(-1,0),(1,-1),(-2,1,0),(3,-2,1),(0,-2,-4,0)):
        c,forward,leaves = compile_line(w)
        audit_encoder(w,c,forward,leaves)
        audit(c,lambda x,w=w:line_reflection(w,x))
        lines.append({"normal":w,"central_arity":dots(w,w),"logical_width":c.width,
                      "single_rail_physical_gates":len(physical(c,dual=False).gates),
                      "differential_junctions":len(physical(c,dual=True).gates)})
    # Explicit ordered product of three noncommuting rational reflections.
    # The mixed-denominator example exercises column order and sign parity.
    u3 = tuple(tuple(F(i,9) for i in row) for row in ((-4,-4,-7),(-1,8,-4),(-8,1,4)))
    u5 = ((F(3,5),-F(4,5)),(F(4,5),F(3,5)))
    transforms = []
    for u in (identity(3),((-1,),),u5,u3):
        c,ws = compile_orthogonal(u)
        audit(c,lambda x,u=u:mv(u,x))
        transforms.append({"dimension":len(u),"ordinary_reflections":len(ws),
                           "normal_norms_in_execution_order":[dots(w,w) for w in ws]})
    x = tuple(F(i,6) for i in (2,3,3,7,1))
    y = tuple(F(i,6) for i in (1,3,5,6,1))
    alignment = complement_alignment(x,y,4)
    need(complement_alignment(x,x,4)["touched_data_slots"] == [], "identity alignment")
    return {"scope":"compiled rational real-linear routes with supplied port and encoding resources",
            "line_tests":lines,"orthogonal_tests":transforms,"protected_complement_test":alignment,
            "negative_controls":negative_controls(),"data_dependence":"none after target compilation",
            "fixed_finite_alphabet_obstruction_example":finite_alphabet_control((2,3,5)),
            "boundary":"At fixed total norm, a coefficient-only marginal additionally needs state sufficiency, "
                       "spectator consistency and invariance to disjoint-port operations, not just a compiler."}


if __name__ == "__main__":
    print(json.dumps(probe(),sort_keys=True))
