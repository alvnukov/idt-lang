"""Single-pass resource wall for ONE unconditional event on raw signed rail updates.

On a nonzero final neutral current a, demand P(rail k)=a_k^2/sum(a_j^2).
The observer sees one stream once, not an installed graph representing a,
repeated copies, a rereadable record, or a precomputed current. Prefixes
all end at the same input time, suffixes all have equal length. The tested
event REF is the union of two reference rails. At the cut, all information
accessible later about the prefix must be in the counted memory. Arbitrary
time-dependent responses and independent fresh randomness are allowed.

Unconditional classical response factors as H_ij=p_i . e_j across the
cut: p_i is a probability distribution on s states and e_j is the vector
of suffix REF probabilities. Thus rank <= s. For a D-level quantum memory
H_ij=Tr(rho_i E_j); density operators live in a real D^2-dimensional
space so rank <= D^2. These are statements about a one-shot model, not
about a physical universe. If events may occur before the cut, include
their flags in the memory (e.g. absorbing REF/OTHER states for this bit,
or one flag per irrevocable rail), or explicitly keep the accumulated REF
probability plus a subnormalized live state. Do not omit a free output
register, replay tape, classical controller, correlated environment or clock
whose phase/timing encodes input history. An input-independent clock at the
same cut time does *not* by itself break factorization.

H_ii=1; H_ij=1/(1+4g^2(i-j)^2). Each off-diagonal row sum r_i < 1/g^2:
sum_{k>=1}1/k^2 <= 2 by 1/k^2 <= 1/(k(k-1)) for k>=2. Consequently H
has full rank for g>=1. For ANY deficient-rank approximation G, take a
null vector with largest absolute coordinate 1 at i. From H-G applied to
that vector, max entry error >= (1-max r_i)/d. This is a finite inequality.

There is a stronger UNBOUNDED-length binary approximation wall. Comparing
suffix i on cut states i and j gives a TV (or trace-distance) separation
at least 1-1/(1+4g^2)-2 epsilon if all pair-event errors are <= epsilon.
For any epsilon < 1/2 choose g making this positive, then choose d above
the packing number of the compact normalized fixed-size memory state space.
Thus the supremum error over inputs is >= 1/2; no single input need attain
that supremum. A fair REF/OTHER coin attains this binary minimax value,
not necessarily the same error for the full multi-rail distribution. For
per-rail absolute error, summing the two REF rails only gives a factor-two
conversion. These packing statements assume the cut state is sufficient.

For *exact* unconditional responses the quantum dimension wall is stronger:
Tr(rho_i E_i)=1, 0<=E_i<=I gives E_i=I on supp(rho_i), so E_i>=rho_i.
Then sum_ij H_ij >= Tr[(sum_i rho_i)^2] >= d^2/D. Taking g^2 >= d makes
D>=d by integrality. This saturation argument even holds with an external
input-independent shared CLASSICAL seed: diag=1 holds almost surely for
each of the finitely many diagonals, then sum the per-seed inequalities.
The naive rank and compact-packing arguments do not condition away a
persistent uncounted seed. No assumption about quantum side channels is implied.

For an exact HERALDED response P(REF|accepted,i,j)=H_ij, the numerator
N_ij=eta_ij H_ij is an ordinary unnormalized event probability, with the
same linear rank bound when the cut is sufficient. Since N_ij<=H_ij,
deficient rank requires eta_ii <= r_i for at least one i (otherwise strict
diagonal dominance). For fixed finite memory choose d greater than its
linear dimension, then let g increase: uniform positive efficiency is
impossible on this family. It does not follow that every stream has low
efficiency. Nonclicks must be retained, not normalized away silently.

Earlier local comparisons: probe_native_recurrence_witness.py uses a fixed
input and homogeneous return sequence; probe_driven_readout_memory.py
uses deterministic asymptotic setting rates, not this raw-input contract.
The derivations above are standalone, not Lean proofs or empirical tests.
"""

import json
from fractions import Fraction as F
from itertools import product

# Each brick is two actual signed rail updates, never an idle placeholder.
PLUS = ((0, 1), (1, -1))
MINUS = ((0, -1), (1, 1))
REF_BRICK = ((2, 1), (3, -1))


def words(d, g, i, j):
    k = d - 1
    prefix = PLUS * (g*i) + MINUS * (g*(k-i))
    suffix = MINUS * (g*j) + PLUS * (g*(k-j)) + REF_BRICK
    return prefix, suffix


def measure(word):
    current = [0]*4
    for rail, sign in word:
        if rail not in range(4) or sign not in (-1, 1):
            raise ValueError("not a raw signed update")
        current[rail] += sign
    if sum(current) or not any(current):
        raise ValueError("expected a nonzero neutral final stream")
    norm = sum(a*a for a in current)
    return current, tuple(F(a*a, norm) for a in current)


def rank(matrix):
    a = [list(map(F, row)) for row in matrix]
    n = 0
    for col in range(len(a[0])):
        pivot = next((k for k in range(n, len(a)) if a[k][col]), None)
        if pivot is None:
            continue
        a[n], a[pivot] = a[pivot], a[n]
        for k in range(n+1, len(a)):
            f = a[k][col] / a[n][col]
            if f:
                a[k] = [x-f*y for x, y in zip(a[k], a[n])]
        n += 1
    return n


def require(test, reason):
    if not test:
        raise AssertionError(reason)


def response_matrix(d, g):
    h = []
    for i in range(d):
        row = []
        for j in range(d):
            p, s = words(d, g, i, j)
            require(len(p) == 2*g*(d-1) and len(s) == len(p)+2, "input clock leaked index")
            a, rates = measure(p+s)
            t = 2*g*(i-j)
            require(a == [t, -t, 1, -1] and sum(rates[2:]) == F(1, 1+t*t),
                    "raw-stream cancellation/reference mismatch")
            row.append(sum(rates[2:]))
        h.append(row)
    return h


def finite(d, g):
    h = response_matrix(d, g)
    r = max(sum(row)-1 for row in h)
    require(rank(h) == d and r < F(1, g*g), "literal rank/dominance failed")
    # The trace argument uses the actual sum of *all* entries, not a fitted margin.
    lower = d*d / sum(map(sum, h))
    dim = -(-lower.numerator // lower.denominator)
    return {"indices": d, "spacing": g, "raw_updates_before_cut": 2*g*(d-1),
            "raw_updates_after_cut": 2*g*(d-1)+2, "exact_rank": d,
            "quantum_dimension_lower_from_exact_saturated_diagonal": dim,
            "max_off_diagonal_row_sum": str(r), "deficient_rank_pair_error_at_least": str((1-r)/d),
            "deficient_rank_exact_herald_some_matched_efficiency_at_most": str(r)}


def packing_example(states=3, bins=32, spacing=4):
    # Bin each of the first s-1 simplex coordinates in B intervals of
    # width 1/B (the endpoint 1 goes in the last bin).
    # In a shared cell, L1 on these coordinates <=(s-1)/B; the remaining
    # coordinate difference is at most the same. Therefore TV <=(s-1)/B.
    # This example calculates a guarantee without building a large matrix.
    diameter = F(states-1, bins)
    d = bins**(states-1) + 1
    gap = 1-F(1, 1+4*spacing**2)
    return {"classical_states": states, "indices": d, "bins_per_coordinate": bins, "spacing": spacing,
            "two_prefix_distributions_tv_at_most": str(diameter),
            "some_unconditional_pair_error_at_least": str(max(F(0), (gap-diameter)/2)),
            "large_matrix_materialized": False}


def filter_control():
    # One qubit restricted to the witness currents (t,-t,1,-1), not an
    # implementation for all four-rail currents. Initialize |ref>=(0,1).
    # Apply a sign-dependent Kraus K=[[1,sign],[0,1]]/2 on each raw rail-0
    # update (exactly once per data brick). Every other rail is an identity
    # step, so there is no private brick parser, buffered sign or lookahead.
    # A lost branch is recorded; the common REF brick is fixed.
    # I-K^*K has diagonals 3/4, 1/2 and determinant 5/16 for either sign.
    # This proves the loss completion exists. Work on unnormalized vectors.
    for sign in (-1, 1):
        off = F(-sign, 4)
        require(F(3, 4)*F(1, 2)-off*off == F(5, 16), "invalid contraction")
    d, g, samples = 5, 2, []
    accepted_ref, conditioned = [], []
    smallest = F(1)
    for i in range(d):
        nr, hr = [], []
        for j in range(d):
            p, s = words(d, g, i, j)
            raw = p+s
            x, y, losses, length = F(0), F(1), F(0), 0
            for rail, sign in raw:
                if rail != 0:
                    continue
                before = x*x+y*y
                x, y = (x+sign*y)/2, y/2
                failure = before-x*x-y*y
                require(failure >= 0, "negative loss probability")
                losses += failure
                length += 1
            t = 2*g*(i-j)
            eta = x*x+y*y
            # Within either selected pair, toss one fresh fair coin for its
            # rail label. These are absolute one-run probabilities, not scores.
            absolute_rails = (x*x/2, x*x/2, y*y/2, y*y/2)
            require(raw[-2:] == REF_BRICK and eta == F(1+t*t, 4**length) and losses+eta == 1 and
                    sum(absolute_rails) == eta and y*y == F(1, 4**length) and
                    tuple(a/eta for a in absolute_rails) == measure(raw)[1],
                    "conditional/absolute accounting mismatch")
            nr.append(y*y)
            hr.append(y*y/eta)
            smallest = min(smallest, eta)
            if (i, j) in ((0, 0), (0, d-1)):
                samples.append({"indices": [i, j], "data_bricks": length, "current_parameter": t,
                                "accepted": str(eta), "unconditional_accepted_ref": str(y*y),
                                "nonclick": str(losses), "conditional_ref": str(y*y/eta)})
        accepted_ref.append(nr)
        conditioned.append(hr)
    require(rank(accepted_ref) == 1 and rank(conditioned) == d, "lost filter normalization control")
    return {"live_memory_levels": 2, "recorded_loss_outcome": True,
            "indices": d, "unconditional_ref_numerator_rank": 1,
            "conditional_ref_rank": d, "minimum_efficiency": str(smallest), "samples": samples}


def shared_seed_control():
    # At the abstract cut, both ends can look up indexed bits of the *same*
    # uniformly random external hash. One communicated bit, equality test.
    # This is not a local raw-stream algorithm, nor the target kernel.
    d = 5
    h = [[F(0) for _ in range(d)] for _ in range(d)]
    for bits in product((0, 1), repeat=d):
        for i, j in product(range(d), repeat=2):
            h[i][j] += F(int(bits[i] == bits[j]), 2**d)
    require(all(h[i][j] == (1 if i == j else F(1, 2)) for i, j in product(range(d), repeat=2))
            and rank(h) == d, "shared-seed example lost its rank")
    return {"communicated_states": 2, "external_seed_bits": d, "rank": d,
            "target_kernel_reproduced": False}


def probe():
    return {"scope": "single nonzero raw stream; one required unconditional event; equal input durations; "
                     "cut must include all persistent information; synthetic kernel, no physical status",
            "literal_finite_checks": [finite(d, g) for d, g in ((3, 1), (5, 2), (9, 3), (12, 4))],
            "classical_packing_example": packing_example(), "conditional_filter_control": filter_control(),
            "shared_classical_seed_rank_control": shared_seed_control(),
            "excluded_countercontrol": "A readable external prefix tally can retain the exact current; using "
                                      "its final value to sample supplied squared shares bypasses the finite cut, "
                                      "not the algebra. A fixed elapsed-input clock alone cannot separate these prefixes."}


if __name__ == "__main__":
    print(json.dumps(probe(), separators=(",", ":")))
