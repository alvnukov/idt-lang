"""Can the reciprocal four-arm map carry one squared-amplitude ticket?

For an integer field x with even total, Sx=(sum(x)/2)1-x is integral
and involutive. At port i put |x_i|^2 tickets, with ordered internal
addresses 0<=u,v<|x_i|; relabeling ports does NOT relabel the addresses.
Equal totals give some bijection, not necessarily one respecting port
symmetry. A lift acts on (field, ticket, reference), commutes with S4, and
is its own inverse. The independent finite S4-set R must be usable at EVERY
input reference value, not a field-dependent initialization or output sink.

Take x=(2,0,0,0), Sx=(-1,1,1,1), H=S3 fixing port 0. Every h in H fixes
all four incoming tickets, but a nonidentity h fixes fewer than four
outgoing tickets. A bijection after multiplying by R forces R^h empty
for each such h by comparing fixed-point counts. H acts freely on R;
its size is a positive multiple of six. A mark, a trivial six-state
register, or a symmetric blank is not enough. In particular, starting
from this field and a bare ticket fixed by H cannot equivariantly prepare
any of the needed reference states from an otherwise symmetric blank.
An oriented cyclic order
has six choices; its stabilizer C4 acts freely on ports. Hence the joint
ticket/reference action is free. An equivariant involution then exists
if the ring may CHANGE: disjoint field orbits can be paired via free
stabilizer orbits; if Sx is a port permutation of x, an involutive port
permutation realizes it, matching equal numbers of a and sum(x)/2-a.
Even the underlying undirected square can stay fixed if its arrow may
reverse. Within its dihedral group, only quarter turns are not involutions.
If Sx is a quarter turn of x, then x is fixed by its square; x alternates
on the four arms and a reflection across opposite edges also transports it.

Keeping that oriented ring FIXED is strictly stronger, and fails on the
alternating (1,0,1,0) example below. Another six-state reference DOES
work unchanged: order the three perfect matchings of four ports. Its
stabilizer is the regular Klein four group. Every stabilizer element is
already involutive, so the same orbit construction works within EACH
fixed reference, then transports to all reference values. These arguments
apply to arbitrary integral admissible fields; the explicit finite table
is a cross-check, not a local online rule, a detector, an initial uniform
ticket source, or a convergence law. The earlier unsigned-pair ticket
probe has extra identifiable edge-packet histories that these tickets lack.

Global field-sign reversal can also commute with the lift. Scatter keeps
the sum, so copy positive-sum choices to their negatives. At zero sum
Sx=-x and carry the ticket/reference unchanged. Algebraic replay on a
signed output and retained microstate is not physical time reversal of
an apparatus. The choices of orbit matches are generally not unique.
"""

import json
from dataclasses import dataclass
from functools import cache
from itertools import combinations, permutations, product

I = tuple(range(4))
G = tuple(permutations(I))
GENERATORS = ((1,0,2,3),(0,2,1,3),(0,1,3,2))


def need(test, msg):
    if not test:
        raise ArithmeticError(msg)


def comp(p,q):
    return tuple(p[q[i]] for i in I)


@cache
def field_action(p,x):
    new = [0]*4
    for i in I:
        new[p[i]] = x[i]
    return tuple(new)


@cache
def scatter(x):
    s = sum(x)
    need(s%2 == 0, "nonintegral output is outside the ticket contract")
    return tuple(s//2-i for i in x)


@cache
def tickets(x):
    return tuple((i,u,v) for i in I for u in range(abs(x[i])) for v in range(abs(x[i])))


@dataclass
class Reference:
    states: tuple
    image: dict

    @classmethod
    def orbit(cls,base,act):
        states = tuple(sorted({act(p,base) for p in G}))
        return cls(states,{p:tuple(states.index(act(p,r)) for r in states) for p in G})


def ring_act(p,r):
    word = tuple(p[j] for j in r)
    return min(word[k:]+word[:k] for k in I)


def matching_act(p,r):
    return tuple(tuple(sorted(tuple(sorted((p[i],p[j]))) for i,j in m)) for m in r)


def move(p,s,ref):
    x,i,u,v,r = s
    return field_action(p,x),p[i],u,v,ref.image[p][r]


@cache
def neg(x):
    return tuple(-j for j in x)


def reverse_field(s):
    x,i,u,v,r = s
    return neg(x),i,u,v,r


def fiber_reps(x,syms,rs,ref):
    # The subgroup below fixes x; freeness on (ticket port,reference)
    # makes every orbit have the same size, including repeated amplitudes.
    left = {(x,*t,r) for t in tickets(x) for r in rs}
    reps = []
    while left:
        a = min(left)
        orbit = {move(p,a,ref) for p in syms}
        need(len(orbit)==len(syms) and orbit<=left, "ticket/reference action is not free")
        left -= orbit
        reps.append(a)
    return reps


def construct(fields,syms,rs,ref):
    table = {}
    unseen = set(fields)
    while unseen:
        x = min(unseen)
        y = scatter(x)
        ox = {field_action(p,x) for p in syms}
        oy = {field_action(p,y) for p in syms}
        need(ox|oy <= unseen and (ox==oy or ox.isdisjoint(oy)), "partial field orbit")
        unseen -= ox|oy
        if y==x:
            for z in ox:
                for t,r in product(tickets(z),rs):
                    a = (z,*t,r)
                    table[a] = a
            continue
        h = tuple(p for p in syms if field_action(p,x)==x)
        need(all((field_action(p,x)==x)==(field_action(p,y)==y) for p in syms),
             "scatter changed stabilizer")
        aa = fiber_reps(x,h,rs,ref)
        if ox == oy:
            pi = next((p for p in syms if field_action(p,x)==y and comp(p,p)==I),None)
            need(pi is not None, "required involutive field transporter absent")
            bb = [move(pi,a,ref) for a in aa]
        else:
            bb = fiber_reps(y,h,rs,ref)
        for a,b in zip(aa,bb,strict=True):
            for p in syms:
                src,dst = move(p,a,ref),move(p,b,ref)
                need(table.get(src,dst)==dst and table.get(dst,src)==src,"inconsistent paired lift")
                table[src],table[dst] = dst,src
    for a in table:
        total = sum(a[0])
        if total==0:
            table[a] = reverse_field(a)
        elif total<0:
            table[a] = reverse_field(table[reverse_field(a)])
    return table


def static_table(fields,ref):
    # No reference bits may change on application. A single slice must
    # respect the stabilizer of that reference; then extend by relabeling.
    h = tuple(p for p in G if ref.image[p][0]==0)
    need(all(comp(p,p)==I for p in h), "this static construction needs exponent at most two")
    base = construct(fields,h,(0,),ref)
    full = {}
    for r in range(len(ref.states)):
        p = next(p for p in G if ref.image[p][0]==r)
        full.update((move(p,a,ref),move(p,b,ref)) for a,b in base.items())
    return full


def ring_table(fields,ring):
    """Mutable orientation on fixed wiring, transported to all three wirings."""
    reverse = tuple(ring.states.index(ring_act(I,tuple(reversed(r)))) for r in ring.states)
    wirings = {tuple(sorted((r,reverse[r]))) for r in range(6)}
    base_wiring = min(wirings)
    h = tuple(p for p in G if tuple(sorted(ring.image[p][r] for r in base_wiring))==base_wiring)
    need(len(wirings)==3 and len(h)==8, "unoriented-square stabilizer")
    base = construct(fields,h,base_wiring,ring)
    full = {}
    for wire in wirings:
        p = next(p for p in G if tuple(sorted(ring.image[p][r] for r in base_wiring))==wire)
        full.update((move(p,a,ring),move(p,b,ring)) for a,b in base.items())
    need(all(z[-1] in (a[-1],reverse[a[-1]]) for a,z in full.items()),"changed undirected wiring")
    return full


def audit(table,fields,ref,static):
    n = sum(len(tickets(x)) for x in fields)*len(ref.states)
    need(n==len(table), "incomplete table")
    changes = 0
    for a,b in table.items():
        x,i,u,v,r = a
        y,j,s,t,k = b
        need(x in fields and y==scatter(x) and 0<=u<abs(x[i]) and 0<=v<abs(x[i])
             and 0<=s<abs(y[j]) and 0<=t<abs(y[j]) and table[b]==a, "ticket or inverse invalid")
        need(table[reverse_field(a)]==reverse_field(b),"global sign reversal altered ticket transport")
        for p in GENERATORS:
            need(table[move(p,a,ref)]==move(p,b,ref), "lift does not commute with port relabeling")
        changes += r!=k
    need((changes==0)==static, "reference update contract not witnessed")
    return {"ticket_reference_states":n,"involution_checked":True,"field_sign_covariant":True,
            "changed_reference_states_in_this_table_not_an_optimum":changes,
            "adjacent_transposition_checks":n*len(GENERATORS)}


def fixed_point_wall(ref):
    x,y = (2,0,0,0),(-1,1,1,1)
    need(y==scatter(x),"test pair")
    result = []
    for p in ((0,2,1,3),(0,2,3,1)):
        nr = sum(i==j for i,j in enumerate(ref.image[p]))
        result.append(tuple(nr*sum(p[i]==i for i,_,_ in tickets(a)) for a in (x,y)))
    return result


def static_ring_wall(ring):
    x,y = (1,0,1,0),(0,1,0,1)
    r = ring.states.index(I)
    p = (1,2,3,0)
    need(scatter(x)==y and ring.image[p][r]==r,"alternating ring fixture")
    a = (x,0,0,0,r)
    orbit = [a]
    for _ in range(3):
        orbit.append(move(p,orbit[-1],ring))
    need(move(p,orbit[-1],ring)==a and len(set(orbit))==4 and
         set(orbit)=={(z,*t,r) for z in (x,y) for t in tickets(z)}, "not a single regular C4 orbit")
    # A commuting function on a single cyclic orbit is determined by its
    # offset. The only offsets covering scatter are 1,3; neither squares
    # to the identity. An explicitly DIFFERENT inverse would work here.
    scatter_offsets = [i for i,v in enumerate(orbit) if v[0]==y]
    inverse_offsets = [i for i in I if 2*i%4==0]
    need(scatter_offsets==[1,3] and inverse_offsets==[0,2], "fixed-ring obstruction")
    return {"scatter_offsets":scatter_offsets,"self_inverse_offsets":inverse_offsets}


def minimal_reference_types():
    # At |R|=6 the S3 at a port acts regularly, so R is transitive under
    # S4 with a stabilizer of order four acting freely on ALL four ports.
    derangements = tuple(p for p in G if all(p[i]!=i for i in I))
    cyclic,klein = 0,0
    for rest in combinations(derangements,3):
        h = {I,*rest}
        if all(comp(p,q) in h for p,q in product(h,repeat=2)):
            if any(comp(p,p)!=I for p in h):
                cyclic+=1
            else:
                klein+=1
    need((cyclic,klein)==(3,1),"minimal reference stabilizer census")
    return {"cyclic_subgroups":cyclic,"klein_subgroups":klein}


def probe():
    box = {x for x in product(range(-2,3),repeat=4) if sum(x)%2==0}
    fields = box|{scatter(x) for x in box}
    need(len(box)==313 and len(fields)==401 and all(scatter(scatter(x))==x and
         len(tickets(scatter(x)))==len(tickets(x)) for x in fields), "scatter-closed cross-control")
    generated = {I}
    while (more:={comp(p,q) for p in generated for q in GENERATORS}-generated):
        generated |= more
    need(generated==set(G), "equivariance tests must generate all of S4")
    trivial = Reference.orbit(0,lambda p,r:r)
    marked = Reference.orbit(0,lambda p,r:p[r])
    ring = Reference.orbit(I,ring_act)
    base_match = (((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2)))
    match = Reference.orbit(base_match,matching_act)
    frame = Reference.orbit(I,lambda p,r:tuple(p[i] for i in r))
    need([len(r.states) for r in (trivial,marked,ring,match,frame)]==[1,4,6,6,24],"reference census")
    wall = {k:fixed_point_wall(r) for k,r in (("none",trivial),("one_mark",marked),("ring",ring))}
    need(wall["none"]==[(4,2),(4,1)] and wall["one_mark"]==[(8,4),(4,1)]
         and wall["ring"]==[(0,0),(0,0)],"fixed point wall")
    mutable = ring_table(fields,ring)
    m = audit(mutable,fields,ring,False)
    k = audit(static_table(fields,match),fields,match,True)
    f = audit(static_table(fields,frame),fields,frame,True)
    # Uniform distribution ON THE ENTIRE finite incoming fiber is
    # preserved onto the outgoing fiber by bijectivity. Uniformity of
    # a hidden orientation alone need not make a fixed ticket uniform.
    x = (2,0,0,0)
    population = [mutable[(x,*t,r)] for t,r in product(tickets(x),range(6))]
    need([sum(z[1]==i for z in population) for i in I]==[6]*4, "uniform fiber count")
    # Conditional on a single bare input ticket, even a uniformly random
    # ring follows just ONE S3 orbit. It always yields the distinguished
    # output or never does -- it is not a sampler of four uniform tickets.
    fixed_ticket_counts = []
    for t in tickets(x):
        ports = [mutable[x,*t,r][1] for r in range(6)]
        fixed_ticket_counts.append(tuple(ports.count(i) for i in I))
    need(sorted(fixed_ticket_counts)==[(0,2,2,2)]*3+[(6,0,0,0)],
         "uniform orientation alone should not generate squared probabilities")
    # Independent uniform resampling on each application is equivariant
    # even without a remembered frame. At x -> Sx -> x it returns the
    # SAME one of these four tickets with probability 1/4, not one.
    return {"finite_input_box_admissible":len(box),"scatter_closed_fields":len(fields),
            "bare_tickets_in_domain":sum(len(tickets(x)) for x in fields),"fixed_point_counts":wall,
            "minimal_reference_types":minimal_reference_types(),"unchanged_ring_wall":static_ring_wall(ring),
            "mutable_oriented_ring_fixed_undirected_wiring":m,"unchanged_ordered_matchings":k,
            "unchanged_full_frame":f,"uniform_ring_port_counts_for_each_fixed_input_ticket":fixed_ticket_counts,
            "independent_uniform_resampling_return_probability_for_one_of_four":"1/4",
            "scope":"Global lookup with supplied ticket addresses and reference, not a local dynamics or sampler.",
            "boundary":"Uniform initial tickets (and uniform mutable reference for the joint-fiber argument) "
                       "are additional assumptions. Iterating this involution has periods at most two, "
                       "not convergence to squared-frequency probabilities."}


if __name__=="__main__":
    print(json.dumps(probe(),sort_keys=True))
