"""Exact conditional witnesses, not an empirical result or a proof of physical QM.

The chosen normalized full ball S={(1,r): ||r||<=1} and standard ball Frame
are supplied models, not derived here. R^4 with W=||.||^2 is a common ambient
carrier, not a derivation of that Frame. Record-first and pool-first are both
retained: which is physical depends on the preparation/record rule realized.
For every unit U, q_+(U)+q_-(U)=4 and q_+(U)/4=(1+U.n)/2;
thus the two rules agree on every pure state algebraically. Averaging before
squaring instead removes the variance term, so mixed preparations can differ.
The rational checks below are executable witnesses, not universal Lean proofs.
Oriented real-linear channels L_+(t,r)=(0,(r+t*n)/sqrt(2)) and L_-
have exact rational intensities q_+/2 and q_-/2; no square-root rounding is used.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q

Vec = tuple[Q, ...]
Ensemble = tuple[tuple[Q, Vec], ...]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


def add(u: Vec, v: Vec) -> Vec:
    return tuple(x + y for x, y in zip(u, v, strict=True))


def scale(c: Q, v: Vec) -> Vec:
    return tuple(c * x for x in v)


def dot(u: Vec, v: Vec) -> Q:
    return sum((x * y for x, y in zip(u, v, strict=True)), Q(0))


def j(v: Vec) -> Vec:
    t, x, y, z = v
    return (-x, t, -z, y)


def branch(v: Vec, sign: int) -> Vec:
    return scale(Q(1, 2), add(v, scale(Q(sign), j(v))))


def f(u: Vec, v: Vec) -> tuple[Vec, Vec]:
    return add(branch(u, 1), branch(v, -1)), add(branch(u, -1), branch(v, 1))


def inverse_f(u: Vec, v: Vec) -> tuple[Vec, Vec]:
    return add(branch(u, -1), branch(v, 1)), add(branch(u, 1), branch(v, -1))


def q(v: Vec, sign: int) -> Q:
    t, x, y, z = v
    return (x + sign * t) ** 2 + y**2 + z**2


def ensemble_report(records: Ensemble) -> dict[str, object]:
    require(sum((p for p, _ in records), Q(0)) == 1, "record weights must sum to one")
    require(all(p >= 0 and dot(u, u) == 1 for p, u in records), "not pure records")
    mean = tuple(sum((p * u[k] for p, u in records), Q(0)) for k in range(3))
    variance = sum((p * dot(add(u, scale(Q(-1), mean)),
                            add(u, scale(Q(-1), mean))) for p, u in records), Q(0))
    averaged = tuple(sum((p * q((Q(1), *u), s) for p, u in records), Q(0))
                     for s in (1, -1))
    pooled = tuple(q((Q(1), *mean), s) for s in (1, -1))
    require(all(a == b + variance for a, b in zip(averaged, pooled, strict=True)),
            "variance identity failed")
    require(all(q((Q(1), *u), 1) + q((Q(1), *u), -1) == 4 for _, u in records),
            "pure-record total failed")
    return {"mean": mean, "variance": variance, "averaged_q": averaged,
            "pooled_q": pooled, "record_first_plus": averaged[0] / sum(averaged),
            "pool_first_plus": pooled[0] / sum(pooled)}


def main() -> None:
    zero = (Q(0),) * 4
    basis = tuple(tuple(Q(i == k) for i in range(4)) for k in range(4))
    columns = tuple(f(e, zero) for e in basis) + tuple(f(zero, e) for e in basis)
    gram = tuple(tuple(dot(u, x) + dot(v, y) for x, y in columns) for u, v in columns)
    require(all(gram[i][k] == Q(i == k) for i in range(8) for k in range(8)),
            "F Gram matrix is not the identity")
    for e in basis:
        require(j(j(e)) == scale(Q(-1), e), "J squared failed")
        for s in (1, -1):
            inverse = add(e, scale(Q(-s), j(e)))  # I -/+ J
            require(branch(inverse, s) == e, "branch right inverse failed")
            image = branch(e, s)
            require(add(image, scale(Q(-s), j(image))) == e, "branch left inverse failed")
        for pair in ((e, zero), (zero, e)):
            require(inverse_f(*f(*pair)) == pair, "F recovery failed")
            require(f(*inverse_f(*pair)) == pair, "F inverse recovery failed")
    pointers = f(add(basis[0], basis[1]), add(basis[0], scale(Q(-1), basis[1])))
    require(pointers == (zero, scale(Q(2), basis[0])), "normalized pointer routing failed")
    n, m = (Q(1), Q(0), Q(0)), (Q(0), Q(1), Q(0))
    first = ensemble_report(((Q(3, 4), n), (Q(1, 4), scale(Q(-1), n))))
    second = ensemble_report(((Q(1, 2), n), (Q(1, 4), m),
                              (Q(1, 4), scale(Q(-1), m))))
    require(first == second, "same-mean ensemble witnesses disagree")
    require(first["record_first_plus"] == Q(3, 4) and first["pool_first_plus"] == Q(9, 10),
            "expected split failed")
    slices = ((Q(1), *n), (Q(1), Q(3, 5), Q(4, 5), Q(0)),
              (Q(1), Q(1, 2), Q(0), Q(0)), (Q(1), Q(0), Q(0), Q(0)))
    intensities = tuple((q(v, 1) / 2, q(v, -1) / 2) for v in slices)
    require(all(sum(pair) == dot(v, v) for v, pair in zip(slices, intensities, strict=True)),
            "oriented branch intensity conservation failed")
    # Unique degree <=2 numerator from q(-1)=0, q(0)=1/2, q(1)=2.
    nodes = ((Q(-1), Q(0)), (Q(0), Q(1, 2)), (Q(1), Q(2)))
    position = Q(1, 2)
    interpolated = Q(0)
    for x, value in nodes:
        term = value
        for other, _ in nodes:
            if x != other:
                term *= (position - other) / (x - other)
        interpolated += term
    require(interpolated == (1 + position) ** 2 / 2, "quadratic interpolation failed")
    require(interpolated / (1 + position**2) == Q(9, 10), "interpolated readout failed")
    print(json.dumps({"status": "conditional exact witnesses; both candidates retained",
                      "boundary": "supplied ball/Frame; no empirical claim; physical QM not proved",
                      "carrier": {"F_gram_identity": True, "branch_inverses": "I -/+ J",
                                  "normalized_opposite_pointer_raw_F": pointers},
                      "pure_ensembles": ["3/4 at +x, 1/4 at -x",
                                         "1/2 at +x, 1/4 each at +y and -y"],
                      "shared_ensemble_results": first,
                      "normalized_slice_branch_intensities": intensities,
                      "quadratic_axis_calibration": {"numerator_at_half": interpolated,
                                                     "probability_at_half": Q(9, 10)},
                      "interpretation": "record rule unresolved; no physical no-go inferred"},
                     default=str, indent=2))


if __name__ == "__main__":
    main()
