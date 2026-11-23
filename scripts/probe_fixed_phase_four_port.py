"""Compare literal four-arm first hits with a supplied fixed-phase two-stage model.

Rows name input corridors, columns name outputs; the literal link uses the same
corridor IDs at both ends. No amplitudes or phase mixtures occur in the raw rule.

Normal form. Scale each hypothetical single-mode lossless amplitude by sqrt(3).
P fixes its diagonal to zero and every other entry to unit modulus. Row/column
rephasings make row zero all +1 and column zero all -1 off the diagonal.
Orthogonality to row zero makes the two remaining entries in each lower row
opposites; orthogonality to column zero does the same in each lower column.
Thus the lower 3x3 block is exactly a times the corresponding block of C,
|a|=1. Multiplying all lower rows by conjugate(a) and column zero by a
preserves the border (C[0,0]=0) and gives C. Conversely C C^T=3I. For two
possibly different stages, outer phases cancel in probabilities, leaving
C diag(z) C / 3 for some four fixed unit complex numbers. In an offdiagonal
cell i,j the two surviving terms have opposite signs and complementary
indices k,l; the squared modulus is (2-2 Re(z_k conjugate(z_l)))/9.
A diagonal cell instead uses the squared modulus of three same-sign terms.

Run: python3 -m scripts.probe_fixed_phase_four_port
"""

import json
from fractions import Fraction as F
from itertools import combinations, permutations

if __package__:
    from . import probe_raw_bond_junction_rates as raw
else:
    import probe_raw_bond_junction_rates as raw


N = range(4)
C = ((0, 1, 1, 1), (-1, 0, 1, -1), (-1, -1, 0, 1), (-1, 1, -1, 0))
REAL_C = tuple(tuple((x, 0) for x in row) for row in C)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def native_tables(native):
    """Validate actual complete first-hit measures, retaining the passive joint record."""
    require(
        tuple(native["outcomes"]) == raw.OUTCOMES
        and tuple(map(tuple, native["arm_order"])) == raw.ARMS,
        "unexpected raw table orientation",
    )
    isolated = [
        r for r in native["isolated"] if r["law"] == "free" and r["offset"] % 2 == 0
    ]
    literal = [
        r
        for r in native["literal"]
        if r["law"] == "free" and r["length"] == 14 and r["offset"] % 2 == 0
    ]
    expected_single = {(s, 6, i) for s in ((19, 23), (20, 22)) for i in N}
    require(
        len(isolated) == 8
        and {(tuple(r["sizes"]), r["offset"], r["input"]) for r in isolated}
        == expected_single,
        "incomplete single-junction coverage",
    )
    require(
        len(literal) == 4
        and {(r["offset"], r["input"]) for r in literal} == {(6, i) for i in N},
        "incomplete two-junction coverage",
    )

    def measured(row):
        m = tuple(map(F, row["mass"]))
        require(
            len(m) == 6 and m[4:] == (0, 0) and sum(m) == 1 and min(m) >= 0,
            "nonconservative row or nonzero jam/trap mass",
        )
        return m[:4]

    single = {r["input"]: measured(r) for r in isolated}
    p = tuple(single[i] for i in N)
    for row in isolated:
        i = row["input"]
        require(
            measured(row) == p[i] == tuple(F(i != j, 3) for j in N),
            "wrong single-junction P",
        )
    literal.sort(key=lambda r: r["input"])
    t = tuple(measured(r) for r in literal)
    for i, row in enumerate(literal):
        joint = {key: F(val) for key, val in row["joint"].items()}
        expected = {
            f"{k}:{j}": p[i][k] * p[k][j] for k in N for j in N if p[i][k] * p[k][j]
        }
        require(
            joint == expected, "literal passive joint disagrees with the factored table"
        )
        require(
            t[i] == tuple(sum(joint.get(f"{k}:{j}", 0) for k in N) for j in N),
            "literal marginal disagrees with the passive joint",
        )
    return p, t


def cmul(*terms):
    """Exact multiplication of complex pairs; no conversion to float."""
    a, b = 1, 0
    for c, d in terms:
        a, b = a * c - b * d, a * d + b * c
    return a, b


def conjugate(z):
    return z[0], -z[1]


def norm2(z):
    return z[0] ** 2 + z[1] ** 2


def csum(terms):
    return tuple(sum(col) for col in zip(*terms, strict=True))


def dephase_stage(stage):
    """Exact control for independently rephased scaled conference stages."""
    require(
        len(stage) == 4 and all(len(row) == 4 for row in stage), "expected a 4x4 stage"
    )
    require(
        all(norm2(stage[i][j]) == (i != j) for i in N for j in N), "not the observed P"
    )
    for i in N:
        for j in N:
            require(
                csum(cmul(stage[i][k], conjugate(stage[j][k])) for k in N)
                == (3 * (i == j), 0),
                "not lossless",
            )
    left = [(1, 0), *(cmul((-1, 0), conjugate(stage[i][0])) for i in range(1, 4))]
    right = [(1, 0), *(conjugate(stage[0][j]) for j in range(1, 4))]
    a = cmul(left[1], stage[1][2], right[2])
    right[0] = a
    for i in range(1, 4):
        left[i] = cmul(left[i], conjugate(a))
    canonical = tuple(tuple(cmul(left[i], stage[i][j], right[j]) for j in N) for i in N)
    require(canonical == REAL_C, "dephasing did not recover C")
    return canonical


def stage_product_table(left, right):
    return tuple(
        tuple(F(norm2(csum(cmul(left[i][k], right[k][j]) for k in N)), 9) for j in N)
        for i in N
    )


def phase_table(phases):
    require(
        len(phases) == 4 and all(norm2(z) == 1 for z in phases), "need four unit phases"
    )
    stage = tuple(tuple(cmul(REAL_C[i][j], phases[j]) for j in N) for i in N)
    return stage_product_table(stage, REAL_C)


def determinant(matrix):
    """Laplace expansion only for the at most four-by-four exact minors below."""
    if not matrix:
        return 1
    return sum(
        (-1) ** j * v * determinant(tuple(row[:j] + row[j + 1 :] for row in matrix[1:]))
        for j, v in enumerate(matrix[0])
        if v
    )


def inspect_table(table):
    """Necessary and sufficient for fixed phases in the aligned model (real Gram test).

    Every PSD matrix of rank <=2 with diagonal one factors into unit vectors in
    R², hence complex phases. Conversely their scalar products form exactly such
    a matrix. The explicit diagonal identity and reflected cells must also match.
    The one-input minors use ONLY that input, even for nonsymmetric observations.
    """
    require(
        len(table) == 4 and all(len(row) == 4 for row in table),
        "expected four-by-four rates",
    )
    t = tuple(tuple(map(F, row)) for row in table)
    g = [[F(i == j) for j in N] for i in N]
    for i, j in combinations(N, 2):
        k, l = (n for n in N if n not in (i, j))
        g[k][l] = g[l][k] = 1 - 9 * t[i][j] / 2
    gram = tuple(map(tuple, g))
    minors = [
        (size, determinant(tuple(tuple(g[i][j] for j in sub) for i in sub)))
        for size in range(1, 5)
        for sub in combinations(N, size)
    ]
    psd = all(d >= 0 for _, d in minors)
    # For a real symmetric matrix of rank r, the sum of its principal r-minors
    # is the product of its r nonzero eigenvalues, and all larger minors vanish.
    rank = max(size for size, d in minors if d)
    sym = all(t[i][j] == t[j][i] for i, j in combinations(N, 2))
    diag = all(
        9 * t[i][i]
        == 3 + 2 * sum(g[k][l] for k, l in combinations(N, 2) if i not in (k, l))
        for i in N
    )
    one_input = []
    for i in N:
        x, y, z = (1 - 9 * t[i][j] / 2 for j in N if j != i)
        one_input.append(1 + 2 * x * y * z - x * x - y * y - z * z)
    return {
        "gram": gram,
        "gram_determinant": minors[-1][1],
        "gram_rank": rank,
        "gram_psd": psd,
        "symmetric": sym,
        "diagonal_consistent": diag,
        "one_input_gram_determinants": tuple(one_input),
        "fixed_phase_possible": psd and rank <= 2 and sym and diag,
    }


def sharp_full_witness():
    """Exact aligned full-table minimax error, not merely the offdiagonal bound.

    Write h=(9/2) times the maximum absolute cell error from T. The offdiagonal
    errors constrain all six |cos(theta_i-theta_j)| <= h; diagonal errors
    constrain the absolute sum of those cosines on each of four triangles <= h.
    The case h>=1 needs no bound. For h<1 the origin cannot belong to the hull
    of any phase triple: if its circular gaps are all <= pi, its cosine sum is
    <= -1 (1+sum = 4 cos(x/2)cos(y/2)cos((x+y)/2), where x,y are successive
    gaps and x+y>=pi). By planar Caratheodory and strict separation all four
    phases lie in one open semicircle. Sort them there, with gaps x,y,z and
    total t<pi. Put a=acos(h). Each gap >=a; t<=pi-a, hence a<=pi/4.

    For the adjacent triple with smaller outer gap b=min(x,z)<=(t-y)/2,
    its sum cos(b)+cos(y)+cos(b+y) is decreasing in b, hence is at least
    cos(y)+2cos(t/2)cos(y/2). This decreases in y<=t-2a, giving the lower
    bound cos(t-2a)+cos(a)+cos(t-a) >= cos(a)-cos(3a)-cos(2a).
    The same triangle sum is <= h=cos(a), so 2cos(5a/2)cos(a/2)>=0 and
    a<=pi/5. Thus h>=cos(pi/5). The witness below attains that lower bound.

    Smaller offdiagonal-only tests use axes modulo pi: among n axes one
    consecutive gap is <=pi/n, so max |cos|>=cos(pi/n), attained by equally
    spaced axes. One input interrogates n=3; the full offdiagonal uses n=4.
    """
    # Pairs (a,b) encode a+b*u, u=2cos(pi/5)=(1+sqrt(5))/2,
    # u²=u+1. Generate 2cos(k*pi/5) by its exact Chebyshev recurrence.
    values = [(2, 0), (0, 1)]
    for _ in range(3):
        a, b = values[-1]
        c, d = values[-2]
        values.append((b - c, a + b - d))
    angles = (0, 1, 3, 4)
    edges = {(i, j): values[angles[j] - angles[i]] for i, j in combinations(N, 2)}
    triples = tuple(
        csum(edges[pair] for pair in combinations(sub, 2)) for sub in combinations(N, 3)
    )
    # Nine times each signed residual is either a negated edge or a triple
    # sum. 0 < u-1 < u, so the checks give its exact sup norm, u.
    residuals = [(-a, -b) for a, b in edges.values()] + list(triples)
    require(
        set(residuals) <= {(0, 1), (0, -1), (-1, 1), (1, -1)} and (0, 1) in residuals,
        "golden-angle residual mismatch",
    )
    return {
        "phase_multiples_of_pi_over_5": angles,
        "pair_basis": "a+b*u; u=(1+sqrt(5))/2; lexicographic index order",
        "twice_pair_cosines": tuple(edges.values()),
        "twice_triangle_cosine_sums": triples,
    }


def report(native=None):
    p, t = native_tables(raw.report() if native is None else native)
    dephase_stage(REAL_C)
    audit = inspect_table(t)
    require(
        audit["gram_rank"] == 4
        and audit["gram_determinant"] == 1
        and audit["gram_psd"]
        and audit["diagonal_consistent"]
        and audit["symmetric"]
        and not audit["fixed_phase_possible"],
        "not the aligned rank-four obstruction",
    )
    # A fixed intermediate permutation conjugates C to another single-stage
    # conference matrix, hence to a rephasing of C. Moving the permutation
    # outside leaves a relative relabeling of T. Its exact no-go persists;
    # no quantitative bound for unknown wiring is inferred here.
    for perm in permutations(N):
        relabelled_c = tuple(tuple(REAL_C[perm[i]][perm[j]] for j in N) for i in N)
        dephase_stage(relabelled_c)
        relabelled = tuple(tuple(row[j] for j in perm) for row in t)
        dets = inspect_table(relabelled)["one_input_gram_determinants"]
        require(
            dets == tuple(F(1) if perm[i] == i else F(3, 4) for i in N),
            "unverified input under relative relabeling",
        )
    one, unit_i = (1, 0), (0, 1)
    echo = phase_table((one,) * 4)
    require(all(echo[i][j] == (i == j) for i in N for j in N), "lost coherent echo")
    patterns = ((one, unit_i, one, unit_i), (one, unit_i, (-1, 0), (0, -1)))
    a, b = map(phase_table, patterns)
    require(
        a != b
        and all((a[i][j] + b[i][j]) / 2 == t[i][j] for i in N for j in N)
        and all(inspect_table(m)["fixed_phase_possible"] for m in (a, b)),
        "two-context control failed",
    )
    return {
        "single_even_free": p,
        "literal_L14_even_free": t,
        "aligned_inverse": audit,
        "exact_fixed_relative_wirings_excluded": 24,
        "sharp_one_input_offdiagonal_error": "1/9",
        "sharp_aligned_all_offdiagonal_error": "sqrt(2)/9",
        "sharp_aligned_full_table_error": "(1+sqrt(5))/18",
        "full_optimum_witness": sharp_full_witness(),
        "supplied_echo": echo,
        "equal_weight_patterns_re_im": patterns,
        "individual_context_tables": (a, b),
        "minimum_exact_frozen_phase_contexts": 2,
        "scope": "Raw rates assume uniform active offers. The literal recorder keeps the "
        "same marks; agreement with P squared does not imply physical reset. The "
        "comparator assumes a lossless single complex mode per corridor matching "
        "P at both stages and fixed phases across runs/inputs. Sharp errors refer "
        "to the known corridor map. External mixing, rereading/repreparation or "
        "extra modes are not excluded. No native amplitude, physical mixture, "
        "interference experiment or refutation of QM is inferred.",
    }


if __name__ == "__main__":
    print(json.dumps(report(), default=str, indent=2))
