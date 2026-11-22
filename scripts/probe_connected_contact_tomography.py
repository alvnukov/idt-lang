"""Can connected, calibrated swaps read a hidden real register?

Supply a connected graph of named rails, signed sum/difference contacts
I+P and I-P for its edges, quadratic stock, reproducible preparations,
and both outcomes retained (not coherent re-pooling). No global rail
permutation, amplitude meter or direct nonedge contact is supplied. On a
pure input z one minus fraction is (z_i-z_j)^2/(2 sum z_a^2).

Summing both flags of an earlier contact sends a moment matrix R to
(R+P R P^T)/2 after dividing by the common total gain. This follows by
expanding the two real branches; R is a convenient description of the
readings, NOT an extra operation available to the apparatus. Along a
simple path v0,...,vk, the last device reads (v0,v1); in reverse path
order, the earlier contacts are (v_{k-1},v_k),...,(v1,v2). Let h_j be
the minus fraction for the prefix path through v_j, and l_j the desired
(v0,v_j) minus fraction. In the pullback of the readout, an endpoint
can walk outwards with probability 1/2 at each edge; the first failed
step stops the walk. Thus h_1=l_1 and
  l_j = l_{j-1} + 2^(j-1) (h_j-h_{j-1}).
This is classical postprocessing, not physical negative counts. To need
only one program per unordered pair, process pairs by shortest distance:
subtract the known contributions from each shorter pair on its path.
Thus there are exactly n(n-1)/2 settings/programs on any connected graph. The
longest program has length at most the diameter; noise is amplified at
long distance. The distance table D_ij=2*l_ij equals R_ii+R_jj-2R_ij.
Double-centering gives R=-J D J/2 for neutral preparations (J subtracts
the constant component). This identifies the trace-one real symmetric
second moment, not a particular ensemble, complex phases, or graph topology.

Uncalibrated plus contacts can preserve every one-step stock while spoiling
the inversion. A two-step test catches one such hidden spectator permutation.
Unknown gain, missing events, state drift or non-neutrality also break the
contract. Nothing here demonstrates that actual physical detectors realize it.
"""

from collections import deque
from fractions import Fraction as F
from itertools import combinations, product

from scripts.probe_associative_stock_merge import q, split


def need(condition, label):
    if not condition:
        raise AssertionError(label)


def branch_fraction(ensemble, path, twisted=False):
    # Nonnegative integer multiplicities over unnormalized currents; normalize
    # only at the end. Null branches stay present and never acquire a weight.
    rows = list(ensemble)
    for j in range(len(path) - 1, 1, -1):
        u, v = path[j-1:j+1]
        rows = [(multiplicity, child) for multiplicity, current in rows
                for child in split(current, u, v, twist=twisted)]
    nums = den = 0
    for multiplicity, current in rows:
        plus, minus = split(current, *path[:2], twist=twisted)
        nums += multiplicity * q(minus)
        den += multiplicity * (q(minus) + q(plus))
    return F(nums, den)


def path_between(graph, start, end):
    queue = deque([(start,)])
    seen = {start}
    while queue:
        path = queue.popleft()
        if path[-1] == end:
            return path
        for nxt in graph[path[-1]]:
            if nxt not in seen:
                seen.add(nxt)
                queue.append((*path, nxt))
    raise ValueError("unreachable rail pair")


def reconstruct(ensemble, graph, twisted=False):
    n = len(graph)
    d = [[F() for _ in graph] for _ in graph]
    paths = sorted((path_between(graph, a, b) for a, b in combinations(range(n), 2)), key=len)
    for path in paths:
        a, b = path[0], path[-1]
        steps = len(path)-2
        measured = branch_fraction(ensemble, path, twisted)
        # An endpoint that stops on internal rail v_r contributes l_r/2^r.
        stopped = sum(d[a][path[r]] / (2**(r+1)) for r in range(1, steps+1))
        value = 2**steps * (measured-stopped)
        d[a][b] = d[b][a] = 2*value
    rows = [sum(row)/n for row in d]
    mean = sum(rows)/n
    return tuple(tuple(-(d[i][j]-rows[i]-rows[j]+mean)/2 for j in range(n))
                 for i in range(n)), len(paths)


def known_moment(ensemble):
    n = len(ensemble[0][1])
    denom = sum(w*2*q(v) for w, v in ensemble)
    return tuple(tuple(F(sum(w*v[i]*v[j] for w, v in ensemble), denom)
                       for j in range(n)) for i in range(n))


def connected(n, edges):
    ns = [set() for _ in range(n)]
    for a, b in edges:
        ns[a].add(b)
        ns[b].add(a)
    return tuple(tuple(sorted(neighbors)) for neighbors in ns)


def signed_mixture(parts):
    # A classical description of stocks on reproducibly pooled preparations.
    # Relative source intensity matters for currents of different lengths.
    return tuple((i+1, v) for i, v in enumerate(parts))


def controls():
    line = connected(4, ((0, 1), (1, 2), (2, 3)))
    # Two rays agree for all three direct neighbor contacts and have equal
    # absolute stock, but the second contact history separates them.
    vs = [abc+(-sum(abc),) for abc in product(range(-2, 3), repeat=3)
          if any(abc)]
    catalog = {}
    twin = None
    for v in vs:
        ens = ((1, v),)
        key = (q(v), *(branch_fraction(ens, (i, i+1)) for i in range(3)))
        if key in catalog and v not in (catalog[key], tuple(-t for t in catalog[key])):
            peer = catalog[key]
            if branch_fraction(ens, (0, 1, 2)) != branch_fraction(((1, peer),), (0, 1, 2)):
                twin = peer, v
                break
        else:
            catalog[key] = v
    need(twin is not None, "one-step alias not found")
    x = (1, 0, -1, 0)
    second = []
    for twist in (False, True):
        a, b = split(x, 0, 1, twist=twist)
        need((q(a), q(b)) == (3, 1), "first contact should be indistinguishable")
        second.append(branch_fraction(((1, a),), (1, 2), twist))
    need(second == [F(3, 4), F(1, 12)], "spectator wire should be visible at depth two")
    need(reconstruct(((1, x),), line, True)[0] != known_moment(((1, x),)),
         "uncalibrated plus operation unexpectedly looked canonical")
    # Two complex conjugate preparations have opposite imaginary cross
    # moment and identical stocks for every real matrix, including paths
    # of real contacts. Check real and imaginary parts without float/complex.
    u, v = (1, -1, 0, 0), (0, 0, 1, -1)
    need(u[0]*v[2]-v[0]*u[2] != 0, "conjugate preparations collapse")
    plus_i, minus_i = ((1, u), (1, v)), ((1, u), (1, tuple(-a for a in v)))
    for a, b in combinations(range(4), 2):
        path = path_between(line, a, b)
        need(branch_fraction(plus_i, path) == branch_fraction(minus_i, path),
             "real analyzer leaked imaginary sign")
    return twin, tuple(map(str, second))


def main():
    runs = 0
    for n in range(3, 8):
        line = connected(n, ((i, i+1) for i in range(n-1)))
        star = connected(n, ((0, i) for i in range(1, n)))
        for k in range(1, 7):
            a = tuple((i*k+1) % 5 - 2 for i in range(n-1))
            a += (-sum(a),)
            if not any(a):
                continue
            b = a[-1:]+a[:-1]
            for ens in (((1, a),), signed_mixture((a, b))):
                for shape in (line, star):
                    observed, n_programs = reconstruct(ens, shape)
                    need(observed == known_moment(ens), "moment tomography failed")
                    need(n_programs == n*(n-1)//2, "unexpected program count")
                    runs += 1
    twin, fractions = controls()
    print(f"{runs} exact real pure/ensemble reconstructions on lines and stars, n=3..7.")
    print(f"Direct path-contact twins: {twin}. Spectator minus fractions: {fractions}.")
    print("Imaginary sign, ensemble decomposition, topology and uncalibrated devices are not reconstructed.")


if __name__ == "__main__":
    main()
