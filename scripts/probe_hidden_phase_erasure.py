"""How much of the six-dial fringe survives a positive erasure?

Replay: python3 -B -O -m scripts.probe_hidden_phase_erasure

Target binary probabilities are (1+v*cos((n-j)*pi/3))/2. The six settings
are three opposite pairs; no joint measurability or measurement
noncontextuality premise is needed. Model A requires the three equiprobable
antipodal preparation mixtures to have one common hidden distribution.
This is NOT full preparation noncontextuality on the affine hexagon: that
additionally identifies the uniform even and odd preparation triads.
Model B passes the actual four-ticket raw phase through a single stochastic
channel, independent of preparation, setting and skip history. Every output
test, not just the six dials, is available when comparing distributions.

Let p_i^+,p_i^- be the hidden laws of phases i,i+3 for i in (0,2,4);
m_i=(p_i^++p_i^-)/2, h_i=(p_i^+-p_i^-)/2. Let delta=max TV(m_i,m_j).
In particular |h_i(y)| <= m_i(y). For a possibly stochastic binary reader
with signed response b_j(y) in [-1,1], C_ij=sum_y h_i(y)b_j(y).
On target C_ii=v, C_ij=-v/2 off diagonal. These arguments apply to
general hidden spaces using densities under the sum of their six laws.

A: C00-C02-C10-C12 (using slot indices 0,1,2) is 5v/2. Its integrand
h0*(b0-b2)-h1*(b0+b2) is at most 2*max(m0,m1), since
|b0-b2|+|b0+b2| <= 2. Its integral is at most 2*(1+delta).
Hence v <= (4/5)*(1+delta), not necessarily 2/3.

B: the even/odd triads already have identical raw laws. Thus sum_i h_i=0
pointwise after ANY fixed channel. For three reals summing to zero,
sum_i |h_i|=2*max_i |h_i| <= 2*max_i m_i. The integral of max_i m_i
is <= 1+2*delta (bound the excess over m0 by the two positive parts).
Hence sum_i C_ii <= 2+4*delta, so v <= (2+4*delta)/3. This also bounds
full affine preparation noncontextuality at delta=0. Opposite-pair
equalities and triad equality exhaust the three independent affine
relations of the six planar hexagon vertices. No assumption about
unmeasured lab equivalences follows from verifying simulated stocks.

For error e in each named binary probability, |C_ij-target_ij|<=2e:
replace 5v/2 by 5v/2-8e and 3v by 3v-6e in the respective inequalities.
Both zero-error bounds are sharp on [0,1/4]. Allowing a larger leakage
budget adds no visibility; in B, data processing already forces delta<=1/4.

Even if the triad equivalence is only approximate, eta=TV(even,odd) exacts
a sharp price: 3v<=2+4*delta+eta. Thus hitting 4/5 at delta=0 requires
eta>=2/5. See joint_certificate() for the pointwise dual and simplex of
witnesses. With probability error e this joint inequality loses at most
10e on its left (the absolute sum of its nine coefficients is 5).
All counts are exact model probabilities, not observations or error bars.
"""

from fractions import Fraction as F
from itertools import product

from scripts.probe_affine_contact_fringe import Six, act, cycle, detector, need


PHASES = range(6)
TRINE = (0, 2, 4)
COS = (1, F(1, 2), -F(1, 2), -1, -F(1, 2), F(1, 2))


def mix(p, q, u):
    return tuple((1-u)*x + u*y for x, y in zip(p, q, strict=True))


def tv(p, q):
    return sum(abs(x-y) for x, y in zip(p, q, strict=True))/2


def apply_channel(source, channel):
    need(all(len(p) == len(channel) for p in source), "channel input dimension")
    return tuple(tuple(sum(x*y for x, y in zip(p, col, strict=True))
                       for col in zip(*channel, strict=True)) for p in source)


def opposite_mixtures(laws):
    return tuple(mix(laws[i], laws[(i+3) % 6], F(1, 2)) for i in TRINE)


def triad_distance(laws):
    def avg(indices):
        return tuple(sum(col)/3 for col in zip(*(laws[i] for i in indices), strict=True))
    return tv(avg(TRINE), avg((1, 3, 5)))


def check_table(laws, readers, v):
    """Check all 36 event probabilities, all hidden columns and both witnesses."""
    for p in laws:
        need(min(p) >= 0 and sum(p) == 1, "not a probability law")
    for b in readers:
        need(all(-1 <= x <= 1 for x in b), "not a signed binary response")
    contrasts = tuple(tuple(sum(x*y for x, y in zip(p, b, strict=True)) for b in readers)
                      for p in laws)
    need(all(contrasts[n][j] == v*COS[(n-j) % 6] for n,j in product(PHASES, repeat=2)),
         "wrong attenuated fringe")
    means = opposite_mixtures(laws)
    delta = max(tv(p, q) for p, q in product(means, repeat=2))
    c = tuple(tuple((contrasts[n][j]-contrasts[(n+3) % 6][j])/2 for j in TRINE)
              for n in TRINE)
    need(c[0][0]-c[0][2]-c[1][0]-c[1][2] == 5*v/2 <= 2*(1+delta), "A certificate")
    eta = triad_distance(laws)
    need(sum(map(sum,c)) == 0 and 3*v <= 2+4*delta+eta, "approximate triad certificate")
    if eta == 0:
        need(sum(c[i][i] for i in range(3)) == 3*v <= 2+4*delta, "B certificate")
    return delta


def abstract_model():
    """A saturator; the sign triple records deterministic responses at 0,2,4."""
    labels = tuple(product((-1, 1), repeat=3))
    weight = tuple(F(1, 20) if len(set(b)) == 1 else F(3, 20) for b in labels)
    def trine_slot(n):
        return TRINE.index(n if n in TRINE else (n+3) % 6), (1 if n in TRINE else -1)
    readers, laws = [], []
    for n in PHASES:
        slot, sign = trine_slot(n)
        readers.append(tuple(sign*b[slot] for b in labels))
        laws.append(tuple(w*(1 + sign*b[slot]*(-1 if len(set(b)) == 1 else 1))
                          for w, b in zip(weight, labels, strict=True)))
    return tuple(laws), tuple(readers)


def shift_channel(shifts):
    """Random W powers; no copy of the chosen shift in the exposed output."""
    return tuple(tuple(F(sum((t+s) % 6 == y for s in shifts), len(shifts)) for y in PHASES)
                 for t in PHASES)


def raw_pair_identity(channel, output):
    # Q_j is the raw antipodal pair through the channel, before skip smoothing.
    # For the actual 1,2,1 tickets M_n=(Q_0+Q_1+Q_2+Q_{n+1 mod 3})/4.
    # So equality of the three M_n is equivalent coordinatewise to equality
    # of the Q_j, including labels not read by any of the original dials.
    qs = tuple(mix(channel[j], channel[j+3], F(1,2)) for j in range(3))
    ms = opposite_mixtures(output)
    for slot, n in enumerate(TRINE):
        need(ms[slot] == tuple((sum(col)+col[(n+1) % 3])/4 for col in zip(*qs, strict=True)),
             "wrong raw-pair reduction")
    need(4*max(tv(p,q) for p,q in product(ms, repeat=2)) ==
         max(tv(p,q) for p,q in product(qs, repeat=2)), "wrong contraction")


def physical_frames():
    """Read the actual F5 words in every ordered (defect, background) frame."""
    for a,b in product(range(5), repeat=2):
        if a == b:
            continue
        orbit = cycle((b,a,b), Six)
        need(len(orbit) == 6, "raw carrier period")
        for t,u in product(PHASES, (-1,0,1)):
            need(act(orbit[t], Six*(u % 6)) == orbit[(t+u) % 6], "word schedule")
        contacts = tuple(2*int(detector(s,b))-1 for s in orbit)
        need(contacts == (1,1,1,-1,-1,-1), "terminal reader")
        need(tuple(int(s[1] == b) for s in orbit) == (0,0,0,0,0,1), "singleton control")
    return tuple(tuple(contacts[(t-j) % 6] for t in PHASES) for j in PHASES)


def deterministic_control():
    # Exact erasure then requires the SAME unordered pair of outputs at every
    # raw antipodal pair. There are at most two used symbols; binary-output
    # signed differences span dimension <=1. The target 2x2 trine minor has
    # determinant 3*v^2/4, so a single deterministic eraser cannot keep v>0.
    # Every deterministic function on six inputs uses at most six symbols.
    count = 0
    for f in product(PHASES, repeat=6):
        if len({tuple(sorted((f[i],f[i+3]))) for i in range(3)}) == 1:
            need(len(set(f)) <= 2, "deterministic output rank")
            count += 1
    need(count == 6 + 15*8 and COS[0]**2-COS[2]**2 == F(3,4), "rank certificate")


def fair_bit_schedules(raw, readers, erase, identity):
    # No output trial is discarded. Up to m pairs of independent fair bits
    # are used BEFORE the read. Three coin outcomes pick the three words;
    # on 11 retry. Use I if all m pairs were 11. For exact uniform words
    # leave the schedule uncapped: a.s. termination and mean 2/(1-1/4) bits.
    for m in range(5):
        shifts = tuple(next((r-1 for r in ticket if r != 3), 0)
                       for ticket in product(range(4), repeat=m))
        channel = shift_channel(shifts)
        u = F(1,4)**m
        need(channel == tuple(mix(p,q,u) for p,q in zip(erase,identity, strict=True)),
             "capped fair-bit schedule")
        need(check_table(apply_channel(raw, channel), readers, (2+u)/3) == u/4,
             "fair-bit leakage/visibility")
    # A bounded number of fair coins, dyadic source and otherwise deterministic
    # operations can produce only dyadic probabilities. This peak is not one.
    need((1+F(2,3))/2 == F(5,6) and F(5,6).denominator % 3 == 0, "finite-coin wall")


def joint_certificate(raw, readers, erased, abstract, bits):
    # Pointwise, set m=max_i m_i, a_i=h_i/m (m=0 contributes nothing).
    # Prove a.b - (2/3)sum(a)sum(b) <= 2 + abs(sum(a))/3. For fixed b,
    # this is affine on each half-cube cut by sum(a)=0. The vertices are
    # the old corners and intersections of the cutting plane with cube
    # edges, i.e. permutations of (-1,0,1). For fixed a it is affine in b.
    # Upon integrating, sum_ij C_ij=0 on target, integral of m<=1+2delta
    # and integral |sum(h)|=3eta. Hence 3v<=2+4delta+eta.
    corners = tuple(product((-1,1), repeat=3))
    cut = tuple(x for x in product((-1,0,1), repeat=3) if set(x) == {-1,0,1})
    for a,b in product(corners+cut, corners):
        ab = sum(x*y for x,y in zip(a,b, strict=True))
        need(3*ab-2*sum(a)*sum(b) <= 6+abs(sum(a)), "half-cube dual")
    # For leakage BUDGETS (delta,eta), optimal v is the minimum of 1,
    # (4/5)(1+delta), and (2+4delta+eta)/3. If delta>=1/4 use raw alone.
    # Otherwise when eta<=2(1-4delta)/5, mix the following laws on DISJOINT
    # labels with weights r=4delta, a=5eta/2, s=1-r-a. Only raw contributes
    # to pair differences, only abstract to triad differences. Outside this
    # triangle, saturate the A bound on the s=0 edge within the given budget.
    all_readers = tuple(p+q+p for p,q in zip(readers,bits, strict=True))
    for ir in range(6):
        for ia in range(6-ir):
            r,a = F(ir,5),F(ia,5)
            s = 1-r-a
            laws = tuple(tuple(r*x for x in p) + tuple(a*x for x in q) + tuple(s*x for x in z)
                         for p,q,z in zip(raw,abstract,erased, strict=True))
            v = r + F(4,5)*a + F(2,3)*s
            delta,eta = check_table(laws,all_readers,v), triad_distance(laws)
            need((delta,eta) == (r/4,F(2,5)*a) and 3*v == 2+4*delta+eta,
                 "joint frontier positive witness")


def main():
    readers = physical_frames()
    raw = shift_channel((0,1,1,2))
    identity, erase = shift_channel((0,)), shift_channel((-1,0,1))
    abstract, bits = abstract_model()
    need(check_table(abstract, bits, F(4,5)) == 0 and triad_distance(abstract) == F(2,5),
         "A saturator or its triad countercontrol")
    need(check_table(raw, readers, F(1)) == F(1,4) and triad_distance(raw) == 0,
         "raw reference")
    # Both witnesses are affine in u; exact endpoints prove the interpolation
    # for every real u in [0,1]. In A the two components have disjoint labels.
    # In B the erased mixture rows coincide, so all differences scale by u.
    for u in (F(0), F(1,7), F(1,2), F(5,6), F(1)):
        channel = tuple(mix(p,q,u) for p,q in zip(erase, identity, strict=True))
        out = apply_channel(raw, channel)
        raw_pair_identity(channel, out)
        need(triad_distance(out) == 0 and check_table(out, readers, (2+u)/3) == u/4,
             "B sharp tradeoff with native reader")
        a = tuple(tuple((1-u)*x for x in p) + tuple(u*x for x in q)
                  for p,q in zip(abstract,raw, strict=True))
        ab = tuple(p+q for p,q in zip(bits,readers, strict=True))
        need(check_table(a, ab, (4+u)/5) == u/4, "A sharp tradeoff")
    deterministic_control()
    fair_bit_schedules(raw, readers, erase, identity)
    joint_certificate(raw, readers, apply_channel(raw, erase), abstract, bits)
    # Negative control: keeping the shift ticket and output lets a downstream
    # test undo the rotation. Even the optimum schedule then has raw leakage.
    recorded = tuple(tuple(F((t+s) % 6 == y, 3) for s,y in product((-1,0,1),PHASES))
                     for t in PHASES)
    recorded_readers = tuple(tuple(r[y] for _,y in product((-1,0,1),PHASES)) for r in readers)
    need(check_table(apply_channel(raw, recorded), recorded_readers, F(2,3)) == F(1,4),
         "accessible schedule record does not erase")
    print("A, only antipodal hidden equality: sharp v=4/5; witness even/odd triad TV=2/5.")
    print("B, common post-ticket channel: sharp v=2/3; also sharp with full affine prep equality.")
    print("Native schedule: uniformly apply W^5, I, W without retaining the trit; keep old reader.")
    print("All 20 frames; output singleton still reads noisy phase, not the original phase.")
    print("delta=max pairwise antipodal-mixture TV: A 5v/2<=2+2delta; B 3v<=2+4delta.")
    print("eta=even/odd triad TV: sharp joint-budget cap min(1,4(1+delta)/5,(2+4delta+eta)/3).")
    print("Both frontiers sharp up to original v=1, delta=1/4; recorded shift restores delta=1/4.")
    print("Fair-bit cap m pairs (I on timeout): u=4^-m, v=(2+u)/3, delta=u/4;")
    print("  m=1: 3/4,1/16; m=2: 11/16,1/64; uncapped exact trit: 8/3 bits on average.")
    print("Deterministic exact erasers use <=2 symbols: no six-dial v>0; phase-blind K gives v=0.")
    print("Randomness, ticket disposal and terminal tests supplied; no lab equivalence or Bell claim.")


if __name__ == "__main__":
    main()
