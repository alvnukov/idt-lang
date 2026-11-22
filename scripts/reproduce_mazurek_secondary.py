"""Numerical reanalysis of the 100 photonic runs in Mazurek et al., Nat. Commun. 7, 11780.

Use the public count files through the separately pinned primary-data reader.
This independent implementation is based on Supplementary Notes 3–4, equations
21–29 and 36–41 (https://doi.org/10.1038/ncomms11780). No author notebook is
executed. Fit each run to a three-dimensional affine hyperplane in the four
measured probabilities, then mix primary states and effects by two independent
linear programs maximizing their original self-weights, NEVER the witness A.

The fixed default uses two conventions from the authors' original software:
the integrated counts divided by 100 set common per-run fit errors, using the
ordinal row order from each file, and the last preparation's second variance
term uses the unprimed P4 outcome-0 count. The two optional sensitivity modes
use the usual propagated Poisson error, without or with realignment of the
last two aggregate rows. Neither is the published software's convention.

Fixed numerical method: weighted orthogonal residuals, analytic Jacobian,
TRF from (2/3,2/3,2/3,0), closed-form projections; HiGHS dual simplex for
the secondary mixtures, independently compared to HiGHS interior point.
The optional optimal-face diagnostic bounds variation in A without selecting
weights to improve it. Floating-point optimization and its bounds are not
exact certificates or bitwise reproduction of Mathematica's interior point.

On the pinned counts the weighted fits and optimal self-weight sums agree
with the author's cached diagnostics, but A varies across equally optimal
mixtures. The default solver does not reproduce the published rounded
mean and SEM. Ties demonstrate nonuniqueness; they do not establish why
each archived score differs. The authors' precise numerical choices beyond
the published solver and objectives have not been independently reconstructed.
A sensitivity/backend combination matching those digits would
not recover the original calculation; it is never chosen as the main result.

The count ratios assume detected photons fairly sample the binary outcomes;
they are NOT all-herald unconditional rates. Operational equivalences beyond
the tested effects and preparations require tomographic completeness, not
established by a good fit. The 5/6 null requires preparation AND measurement
noncontextuality. An SEM from 100 separate runs is not a rigorous null p-value,
the fit uncertainty of a single run, or experimental confirmation of IDT.

Run: python3 -B -m scripts.reproduce_mazurek_secondary [--sensitivities] [--audit-faces]
Dependencies: NumPy, SciPy and the two pinned count tables. The optional
--notebook-checkpoints reads the 100 cached fit and LP diagnostics plus the
archived 100-point A plot as a fixed-size array of numbers. Recovering the
author's mean and SEM from those plot points is not recomputation from counts.
None of these checkpoints is an input to the fit or optimization.
"""

from __future__ import annotations

import argparse
import base64
import binascii
import hashlib
import json
import math
import os
import re
import stat
import struct
import warnings
import zlib
from collections.abc import Sequence
from dataclasses import dataclass
from importlib import import_module
from pathlib import Path
from typing import Literal

if __name__ == "__main__":
    for _key in (
        "OPENBLAS_NUM_THREADS",
        "OMP_NUM_THREADS",
        "MKL_NUM_THREADS",
        "VECLIB_MAXIMUM_THREADS",
    ):
        os.environ[_key] = "1"

import numpy as np
from numpy.typing import NDArray

Array = NDArray[np.float64]
Mode = Literal["author", "poisson", "aligned-poisson"]
Method = Literal["highs-ds", "highs-ipm"]
MODES: tuple[Mode, ...] = ("author", "poisson", "aligned-poisson")
FEAS = 5e-8
SELF_WEIGHT_SLACK = 1e-6


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def raw_probabilities(counts: Array) -> Array:
    """One run: eight preparations, four adjacent outcome pairs as published."""
    require(counts.shape == (8, 8), "expected an 8 by 8 count table")
    plus, minus = counts[:, ::2], counts[:, 1::2]
    require(bool(np.all(counts >= 0) and np.all(plus + minus > 0)), "invalid counts")
    return np.asarray(plus / (plus + minus))


def variances(aggregate: Array, runs: Array, mode: Mode) -> Array:
    """Fixed within-run variances; never use pooled SEMs to weight a single run."""
    require(
        aggregate.shape == (8, 8) and runs.shape == (100, 8, 8), "expected 100 runs"
    )
    swap = [0, 1, 2, 3, 4, 5, 7, 6]
    require(
        bool(np.array_equal(aggregate[swap], runs.sum(axis=0))),
        "unexpected aggregate mapping",
    )
    stock = (aggregate[swap] if mode == "aligned-poisson" else aggregate) / 100
    a, b = stock[:, ::2], stock[:, 1::2]
    second_a = a.copy()
    if mode == "author":
        second_a[7] = a[6]  # Supplementary Software 1, lines 415–429.
    v = (a * a * b + b * b * second_a) / (a + b) ** 4
    require(
        bool(np.all(np.isfinite(v)) and np.all(v > 0)), "invalid propagated variance"
    )
    return np.asarray(v)


@dataclass(frozen=True)
class Fit:
    primary: Array  # eight preparation rows, four outcome-0 effects
    normal: Array
    chi2: float


def fit_primary(raw: Array, var: Array) -> Fit:
    require(raw.shape == var.shape == (8, 4), "wrong fit shape")
    require(bool(np.all(var > 0) and np.all(np.isfinite(raw))), "invalid fit inputs")
    opt = import_module("scipy.optimize")

    def residual(n: Array) -> Array:
        return np.asarray((raw @ n - 1) / np.sqrt(var @ (n * n)))

    def jac(n: Array) -> Array:
        den = np.sqrt(var @ (n * n))
        return np.asarray(
            raw / den[:, None] - ((raw @ n - 1) / den**3)[:, None] * (var * n)
        )

    out = opt.least_squares(
        residual,
        np.array([2 / 3, 2 / 3, 2 / 3, 0.0]),
        jac=jac,
        method="trf",
        ftol=1e-12,
        xtol=1e-12,
        gtol=1e-12,
        max_nfev=2000,
    )
    require(bool(out.success), "weighted hyperplane fit did not converge")
    normal = np.asarray(out.x, dtype=float)
    delta = (raw @ normal - 1) / (var @ (normal * normal))
    primary = raw - delta[:, None] * (var * normal)
    chi2 = float(residual(normal) @ residual(normal))
    require(
        float(np.max(np.abs(primary @ normal - 1))) < 1e-10, "projection missed plane"
    )
    require(
        abs(chi2 - float(np.sum((raw - primary) ** 2 / var))) < 1e-7,
        "weighted distances disagree",
    )
    require(
        float(primary.min()) >= -FEAS and float(primary.max()) <= 1 + FEAS,
        "unphysical fitted probability; do not clip",
    )
    return Fit(primary, normal, chi2)


@dataclass(frozen=True)
class Equations:
    matrix: Array
    rhs: Array

    def independent(self) -> Equations:
        # Equalities include exact dependencies (complements and fitted plane).
        # SVD is ONLY for row conditioning, not the primary weighted plane fit.
        u, s, v = np.linalg.svd(self.matrix, full_matrices=False)
        rank = int(np.sum(s > s[0] * 1e-11))
        left = u[:, :rank]
        require(
            float(np.max(np.abs(self.rhs - left @ (left.T @ self.rhs)))) < 1e-9,
            "inconsistent dependent constraints",
        )
        return Equations(v[:rank], (left.T @ self.rhs) / s[:rank])


def linear(cost: Array, eq: Equations, method: Method) -> Array:
    opt = import_module("scipy.optimize")
    # SciPy forwards the native HiGHS threads option, with a generic warning.
    with warnings.catch_warnings():
        warnings.filterwarnings(
            "ignore",
            message="Unrecognized options detected: .*threads.*",
            category=opt.OptimizeWarning,
        )
        out = opt.linprog(
            cost,
            A_eq=eq.matrix,
            b_eq=eq.rhs,
            bounds=(0, None),
            method=method,
            options={
                "threads": 1,
                "primal_feasibility_tolerance": 1e-9,
                "dual_feasibility_tolerance": 1e-9,
                "ipm_optimality_tolerance": 1e-10,
            },
        )
    require(bool(out.success), f"{method} LP failure: {out.message}")
    x = np.asarray(out.x, dtype=float)
    require(
        float(x.min()) >= -FEAS
        and float(np.max(np.abs(eq.matrix @ x - eq.rhs))) < FEAS,
        "LP residual",
    )
    return x


@dataclass(frozen=True)
class MixtureLP:
    equations: Equations
    cost: Array

    def solve(self, method: Method) -> Array:
        return linear(self.cost, self.equations, method)

    def face(self, sol: Array) -> Equations:
        return Equations(
            np.vstack([self.equations.matrix, self.cost]),
            np.append(self.equations.rhs, np.dot(self.cost, sol)),
        ).independent()


def programs(p: Array) -> tuple[MixtureLP, MixtureLP, Array]:
    # p is D_p transposed from the paper, including BOTH fourth preparations.
    prep = [row for row in np.kron(np.eye(6), np.ones((1, 8)))]
    for pair in (1, 2):
        block = np.zeros(6)
        block[:2] = 1
        block[2 * pair : 2 * pair + 2] = -1
        prep.extend(np.kron(block[None, :], p.T))
    pe = Equations(np.asarray(prep), np.r_[np.ones(6), np.zeros(8)]).independent()
    pc = -np.eye(6, 8).ravel()
    e = np.column_stack([p, 1 - p[:, 3], np.ones(8), np.zeros(8)])
    me = Equations(
        np.vstack([np.kron(np.eye(3), np.ones((1, 7))), np.tile(e, (1, 3))]),
        np.r_[np.ones(3), np.full(8, 1.5)],
    ).independent()
    return MixtureLP(pe, pc), MixtureLP(me, -np.eye(3, 7).ravel()), e


def score(e: Array, u: Array, v: Array) -> float:
    q = u @ e @ v.T
    return float((3 + np.trace(q[::2] - q[1::2])) / 6)


def primary_success(p: Array) -> float:
    """Unweighted mean of the six matched PRIMARY success probabilities."""
    require(
        p.shape == (8, 4) and np.all(np.isfinite(p)).item(), "invalid primary table"
    )
    require(
        bool(np.min(p) >= -FEAS and np.max(p) <= 1 + FEAS),
        "expected physical probabilities",
    )
    return float((3 + np.trace(p[:6:2, :3] - p[1:6:2, :3])) / 6)


def self_weight_bounds(m: float, cp: float, cm: float) -> tuple[float, float]:
    """Two deterministic lower bounds, not standard errors or test statistics.

    In each of six terms retaining both the nominated preparation and effect
    retains its primary success probability. Other terms are in [0,1]; the
    chance of changing at least one is <=(1-u_ii)+(1-v_tt). Hence for exact
    probabilities and convex mixtures A>=m-(1-CP)-(1-CM)>=m-(9-S)/3.
    The last bound uses only S=6 CP+3 CM, not how a solver allocates it.
    If S is known only to be at least S0-epsilon, subtract epsilon/3 from
    the S0 bound. It does not remove fair sampling or tomography assumptions.
    """
    require(
        all(math.isfinite(x) and -FEAS <= x <= 1 + FEAS for x in (m, cp, cm)),
        "invalid self-weight bound input",
    )
    return m - (1 - cp) - (1 - cm), m - (9 - (6 * cp + 3 * cm)) / 3


@dataclass(frozen=True)
class Result:
    a: float
    cp: float
    cm: float
    alternate_a: float
    face: FaceAudit | None


@dataclass(frozen=True)
class FaceAudit:
    radius: float
    achieved_low: float
    achieved_high: float


def audit_face(pr: MixtureLP, mr: MixtureLP, e: Array, u: Array, v: Array) -> FaceAudit:
    """Conservative numerical bound for changing BOTH optimal mixtures at once.

    At fixed v the signed score is affine in u (two LPs). Moving the t-th
    effect by the vector z changes its paired contribution by at most
    max(z)-min(z), since the two u rows are probability vectors. Bound the
    eight coordinates of z by LPs on the measurement-optimal face. This
    includes unseen optima, unlike two solvers merely yielding the same A.
    """
    uf, vf = pr.face(u.ravel()), mr.face(v.ravel())
    q = v @ e.T
    c = np.repeat(q, 2, axis=0)
    c[1::2] *= -1
    c = c.ravel() / 6
    center = float(c @ u.ravel())

    def on_same_face(lp: MixtureLP, x: Array, base: Array) -> None:
        require(
            abs(float(lp.cost @ (x - base))) <= FEAS
            and float(np.max(np.abs(lp.equations.matrix @ x - lp.equations.rhs)))
            <= FEAS,
            "endpoint changed the original constraints or optimal self-weight",
        )

    u_scores = []
    for sign in (1, -1):
        trial = linear(sign * c, uf, "highs-ds")
        on_same_face(pr, trial, u.ravel())
        a = score(e, trial.reshape(6, 8), v)
        require(abs(a - 0.5 - float(c @ trial)) < FEAS, "preparation endpoint score")
        u_scores.append(a)
    fixed_u_radius = max(abs(a - (0.5 + center)) for a in u_scores)
    # Feasible endpoints at fixed other mixture, NOT globally optimized A.
    cv = ((u[::2] - u[1::2]) @ e).ravel() / 6
    v_scores = []
    for sign in (1, -1):
        trial = linear(sign * cv, vf, "highs-ds")
        on_same_face(mr, trial, v.ravel())
        a = score(e, u, trial.reshape(3, 7))
        require(abs(a - 0.5 - float(cv @ trial)) < FEAS, "measurement endpoint score")
        v_scores.append(a)
    effect_radii = 0.0
    for t in range(3):
        hi, lo = 0.0, 0.0
        for k in range(8):
            z = np.zeros((3, 7))
            z[t] = e[k]
            row = z.ravel()
            hi = max(hi, float(row @ linear(-row, vf, "highs-ds")) - float(q[t, k]))
            lo = min(lo, float(row @ linear(row, vf, "highs-ds")) - float(q[t, k]))
        effect_radii += (hi - lo) / 6
    scores = [score(e, u, v), *u_scores, *v_scores]
    return FaceAudit(fixed_u_radius + effect_radii, min(scores), max(scores))


def secondaries(p: Array, audit: bool = False) -> Result:
    pr, mr, e = programs(p)

    def compute(method: Method) -> tuple[Array, Array]:
        u, v = pr.solve(method).reshape(6, 8), mr.solve(method).reshape(3, 7)
        averages = ((u @ p)[::2] + (u @ p)[1::2]) / 2
        require(
            float(np.max(np.abs(averages - averages[:1]))) <= FEAS,
            "preparation equivalence",
        )
        require(
            float(np.max(np.abs(np.mean(v @ e.T, axis=0) - 0.5))) <= FEAS,
            "measurement equivalence",
        )
        require(
            all(float(np.max(np.abs(x.sum(axis=1) - 1))) <= FEAS for x in (u, v)),
            "unnormalized mixture",
        )
        return u, v

    u, v = compute("highs-ds")
    alt_u, alt_v = compute("highs-ipm")
    cp, cm = float(np.trace(u) / 6), float(np.trace(v) / 3)
    require(
        abs(cp - float(np.trace(alt_u) / 6)) < FEAS
        and abs(cm - float(np.trace(alt_v) / 3)) < FEAS,
        "LP objectives differ by solver",
    )
    a = score(e, u, v)
    return Result(
        a,
        cp,
        cm,
        score(e, alt_u, alt_v),
        audit_face(pr, mr, e, u, v) if audit else None,
    )


def mean_sem(xs: Sequence[float]) -> tuple[float, float]:
    require(len(xs) > 1, "SEM requires multiple runs")
    return float(np.mean(xs)), float(np.std(xs, ddof=1) / math.sqrt(len(xs)))


def decode_plot_numbers(encoded: str) -> Array:
    """Only the bounded numeric rank-two real64 plot format; no expression decoder."""
    require(
        0 < len(encoded) <= 2200 and encoded.isascii(), "unexpected encoded plot size"
    )
    try:
        compressed = base64.b64decode(encoded, validate=True)
    except (ValueError, binascii.Error) as exc:
        raise ValueError("invalid plot base64") from exc
    require(0 < len(compressed) <= 1650, "unexpected compressed plot size")
    require(
        base64.b64encode(compressed).decode("ascii") == encoded,
        "noncanonical plot base64",
    )
    header = b"!boRe" + struct.pack("<III", 2, 100, 2)
    expected = len(header) + 100 * 2 * 8
    decoder = zlib.decompressobj()
    try:
        raw = decoder.decompress(compressed, expected + 1)
    except zlib.error as exc:
        raise ValueError("invalid plot compression") from exc
    require(
        len(raw) == expected
        and decoder.eof
        and not decoder.unconsumed_tail
        and not decoder.unused_data,
        "truncated, oversized or trailing plot stream",
    )
    require(raw.startswith(header), "unexpected packed plot type or shape")
    rows = np.frombuffer(raw, dtype="<f8", offset=len(header)).reshape(100, 2)
    require(
        np.array_equal(rows[:, 0], np.arange(1, 101)),
        "plot labels are not runs 1 through 100",
    )
    a = rows[:, 1].copy()
    require(
        bool(np.all(np.isfinite(a)) and np.all((0 <= a) & (a <= 1))),
        "invalid A plot probabilities",
    )
    return a


def archived_plot(text: str) -> Array:
    """Choose the A plot, not the adjacent chi-squared plot in Supplementary Software 1."""
    lines = text.splitlines()[7015:7062]
    require(
        len(lines) == 47
        and lines[0] == "Cell[BoxData["
        and "GraphicsBox[" in lines[1]
        and ']], "Output",' in lines[-1]
        and "PlotRange->{{0., 100.}, {0.995292505365083, 0.998559704622935}}"
        in lines[39],
        "unrecognized author A-plot template",
    )
    block = "\n".join(lines)
    match = re.findall(
        r'LineBox\[CompressedData\["\s*1:([A-Za-z0-9+/=\s]+)"\]\]', block
    )
    require(
        len(match) == 1 and block.count("CompressedData[") == 1,
        "expected one A-plot payload",
    )
    data = decode_plot_numbers("".join(match[0].split()))
    # Pin the complete source at file ingress, and separately pin the 100 plotted
    # values here so that even other well-formed plots cannot become this receipt.
    require(
        math.isclose(float(data.min()), 0.995292505365083, rel_tol=0, abs_tol=1e-15)
        and math.isclose(
            float(data.max()), 0.998559704622935, rel_tol=0, abs_tol=1e-15
        ),
        "A-plot range disagrees with source",
    )
    require(
        hashlib.sha256(data.astype("<f8").tobytes()).hexdigest()
        == "1ae0dbcc0832efbf441e357ef2d4509e1f0bc6a7542f0d9ed430c74186a832b7",
        "unexpected archived A series",
    )
    return data


@dataclass(frozen=True)
class CachedRuns:
    chi2: Array
    self_weight: Array
    a: Array


def notebook_checkpoints(path: Path) -> CachedRuns:
    """Read only pinned cached outputs as inert numeric data. Never evaluate code."""
    fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    with os.fdopen(fd, "rb") as stream:
        meta = os.fstat(stream.fileno())
        require(
            stat.S_ISREG(meta.st_mode) and meta.st_size == 331_496,
            "expected original notebook file",
        )
        raw = stream.read(331_497)
    require(
        hashlib.sha256(raw).hexdigest()
        == "f7655afda05f4998b91cdf7dae780f772a2b51a030daf339ef30409f388e3ec7",
        "unexpected Supplementary Software 1 digest",
    )
    text = raw.decode("ascii")
    # Print cells for each run: {chi2,{a->...,b->...,c->...,d->...}},
    # {objective}, run number. The Input cells are never interpreted.
    cells = [
        body.partition('], "Print",')[0]
        for body in text.split("Cell[BoxData[")[1:]
        if '], "Print",' in body
    ]
    num = r"([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[Ee][+-]?\d+)?)"
    chis: list[float] = []
    objs: list[float] = []
    for i in range(len(cells) - 2):
        blocks = cells[i : i + 3]
        if all(f'"{key}"' in blocks[0] for key in ("a", "b", "c", "d")):
            x = re.search(r'RowBox\[\{\s*"' + num + r'`"\s*,\s*","', blocks[0])
            y = re.fullmatch(
                r'\s*RowBox\[\{"\{",\s*"' + num + r'`",\s*"\}"\}\]', blocks[1]
            )
            z = re.fullmatch(r'\s*"(\d+)"', blocks[2])
            if x is None or y is None or z is None:
                raise ValueError("unrecognized cached run output")
            require(int(z[1]) == len(chis) + 1, "nonsequential cached outputs")
            chis.append(float(x[1]))
            objs.append(float(y[1]))
    require(len(chis) == 100, "expected 100 cached diagnostics")
    return CachedRuns(np.array(chis), np.array(objs), archived_plot(text))


def analyze(
    aggregate: Array,
    runs: Array,
    mode: Mode,
    face: bool,
    checks: CachedRuns | None,
) -> dict[str, object]:
    var = variances(aggregate, runs, mode)
    fits = [fit_primary(raw_probabilities(row), var) for row in runs]
    sec = [secondaries(f.primary, face) for f in fits]
    values = [r.a for r in sec]
    a, sem = mean_sem(values)
    m = np.array([primary_success(f.primary) for f in fits])
    bounds = np.array(
        [
            self_weight_bounds(float(mean), r.cp, r.cm)
            for mean, r in zip(m, sec, strict=True)
        ]
    )
    require(
        bool(np.all(bounds[:, 0] <= np.asarray(values) + FEAS))
        and bool(np.all(bounds[:, 1] <= bounds[:, 0] + FEAS)),
        "self-weight bound violated",
    )
    out: dict[str, object] = {
        "mode": mode,
        "numerical_backend": f"NumPy {np.__version__}, SciPy {import_module('scipy').__version__}; primary HiGHS dual simplex; alternate HiGHS IPM",
        "runs": len(runs),
        "lower_bounds_conditional_on_fitted_probabilities_not_confidence_bounds": {
            "min_A_lower_bound_using_achieved_CP_and_CM": float(np.min(bounds[:, 0])),
            "min_A_lower_bound_using_achieved_total_self_weight_only": float(
                np.min(bounds[:, 1])
            ),
            "one_based_run_with_lowest_total_only_bound": int(np.argmin(bounds[:, 1]))
            + 1,
            "allowed_total_self_weight_loss_from_achieved_value": SELF_WEIGHT_SLACK,
            "min_across_runs_for_any_feasible_mixture_with_at_most_that_loss": float(
                np.min(bounds[:, 1]) - SELF_WEIGHT_SLACK / 3
            ),
        },
        "mean_A": a,
        "sample_SD_A": float(np.std(values, ddof=1)),
        "SEM_A": sem,
        "mean_A_and_SEM_at_published_decimals": [f"{a:.5f}", f"{sem:.5f}"],
        "matches_both_published_roundings": (f"{a:.5f}", f"{sem:.5f}")
        == ("0.99709", "0.00007"),
        "mean_and_SEM_chi2": mean_sem([r.chi2 for r in fits]),
        "mean_and_SEM_CP": mean_sem([r.cp for r in sec]),
        "mean_and_SEM_CM": mean_sem([r.cm for r in sec]),
        "alternate_solver_mean_and_SEM_A": mean_sem([r.alternate_a for r in sec]),
        "largest_A_change_with_other_solver": max(
            abs(r.a - r.alternate_a) for r in sec
        ),
        "scope": "Detected-count GPT reanalysis conditional on fair sampling and tomography, not new experimental data.",
    }
    if checks is not None:
        out["max_abs_chi2_minus_cached"] = float(
            np.max(np.abs([r.chi2 for r in fits] - checks.chi2))
        )
        out["max_abs_LP_selfweight_sum_minus_cached"] = float(
            np.max(np.abs([6 * r.cp + 3 * r.cm for r in sec] - checks.self_weight))
        )
        gaps = np.asarray(values) - checks.a
        cached_mean, cached_sem = mean_sem(checks.a.tolist())
        out["author_plot_cache_not_recomputed"] = {
            "runs": len(checks.a),
            "mean_A": cached_mean,
            "SEM_A": cached_sem,
            "matches_printed_mean_and_SEM_at_14_places": abs(
                cached_mean - 0.9970895242228291
            )
            < 1e-14
            and abs(cached_sem - 0.0000724422580520114) < 1e-14,
            "max_abs_A_difference_from_count_reanalysis": float(np.max(np.abs(gaps))),
            "one_based_run_of_largest_A_difference": int(np.argmax(np.abs(gaps))) + 1,
            "rms_A_difference_from_count_reanalysis": float(
                np.sqrt(np.mean(gaps * gaps))
            ),
            "runs_matching_A_at_five_decimals": sum(
                f"{a1:.5f}" == f"{a2:.5f}"
                for a1, a2 in zip(values, checks.a, strict=True)
            ),
            "min_A_lower_bound_for_mixtures_with_at_least_cached_total_self_weight": float(
                np.min(m - (9 - checks.self_weight) / 3)
            ),
            "interpretation": "Archived per-run values are not refitted. Different optimal mixtures can change A; this does not explain each discrepancy or recover the author's numerical tie and tolerance choices.",
        }
    if face:
        faces = [r.face for r in sec if r.face is not None]
        radii = [f.radius for f in faces]
        out["mean_numerical_optimal_face_A_radius_bound"] = float(np.mean(radii))
        out["largest_numerical_optimal_face_A_radius_bound"] = max(radii)
        out["attained_mean_A_extremes_changing_one_optimal_mixture_per_run"] = [
            float(np.mean([f.achieved_low for f in faces])),
            float(np.mean([f.achieved_high for f in faces])),
        ]
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__.splitlines()[0] if __doc__ else None
    )
    parser.add_argument(
        "--sensitivities",
        action="store_true",
        help="also run both conventional-Poisson controls",
    )
    parser.add_argument(
        "--audit-faces",
        action="store_true",
        help="bound A over the optimal mixture faces in every main run (extra LPs)",
    )
    parser.add_argument(
        "--notebook-checkpoints",
        type=Path,
        help="optional unexecuted author notebook TXT with cached diagnostic outputs",
    )
    args = parser.parse_args()
    counts = import_module("theory_experiments.mazurek_primary").load_counts()
    aggregate, runs = (
        np.asarray(counts.aggregate, dtype=float),
        np.asarray(counts.runs, dtype=float),
    )
    checks = (
        notebook_checkpoints(args.notebook_checkpoints)
        if args.notebook_checkpoints
        else None
    )
    for mode in MODES if args.sensitivities else MODES[:1]:
        print(
            json.dumps(
                analyze(
                    aggregate,
                    runs,
                    mode,
                    args.audit_faces and mode == "author",
                    checks if mode == "author" else None,
                ),
                sort_keys=True,
            )
        )


if __name__ == "__main__":
    main()
