"""Search periodic raw junction schedules for a common first-order spatial speed.

At a real momentum corner all signed permutations and the four-leg junction
preserve the 24 vectors (+/-e_i +/-e_j). Products have half-integral entries;
the integer scan checks divisions exactly. This is a finite period/corner
search on a supplied homogeneous diamond lattice, not an isotropy postulate.
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts import probe_balanced_phase_composition as base
from scripts import probe_routed_diamond_cones as r

REPS = ((1, 1, 1, 1), (1, -1, 1, 1), (1, -1, -1, 1))
WORD = (14, 21, 0)  # three successive two-tick pairs, same routing at A and B
EXPECTED = {
    1: ((0, 0), (12, 0), (8, 0)),
    2: ((0, 0), (240, 0), (160, 0)),
    3: ((0, 0), (5664, 12), (5888, 0)),
}


def generators(
    signs: tuple[int, ...],
) -> tuple[tuple[base.Matrix, tuple[base.Matrix, ...]], ...]:
    rotations = r.rotations()
    axes = tuple(r.diag(tuple(int(x[j]) for x in r.TETRA)) for j in range(3))
    directions = []
    for a, b in product(rotations, repeat=2):
        v = r.conjugate(r.diag(signs), base.multiply(r.G, b))
        f = base.multiply(v, base.multiply(r.G, a))
        h = tuple(r.sub(d, r.conjugate(v, d)) for d in axes)
        directions.append((f, h))
    return tuple(directions)


def exact_word(
    signs: tuple[int, ...], word: tuple[int, ...]
) -> tuple[F, base.Matrix] | None:
    f = r.I4
    hs: tuple[base.Matrix, ...] = (base.scale(0, r.I4),) * 3
    gs = generators(signs)
    for i in word:
        nxt, h = gs[i]
        hs = tuple(base.add(x, r.conjugate(nxt, y)) for x, y in zip(h, hs, strict=True))
        f = base.multiply(nxt, f)
    c = base.trace(f) / 4
    if abs(c) >= 1 or base.add(f, base.transpose(f)) != base.scale(2 * c, r.I4):
        return None
    k = r.sub(f, base.scale(c, r.I4))
    q = 1 - c * c
    r.need(base.multiply(k, k) == base.scale(-q, r.I4), "wrong corner")
    axes = tuple(
        base.scale(
            F(1, 2), r.sub(x, base.scale(1 / q, base.multiply(base.multiply(k, x), k)))
        )
        for x in hs
    )
    gram = base.matrix(
        tuple(tuple(base.trace(base.multiply(a, b)) / 4 for b in axes) for a in axes)
    )
    for i, j in product(range(3), repeat=2):
        x, y = axes[i], axes[j]
        r.need(
            base.trace(x) == 0
            and base.add(base.multiply(x, y), base.multiply(y, x))
            == base.scale(2 * gram[i][j], r.I4),
            "projected Clifford test",
        )
    return c, gram


def sector_traces(
    direction: tuple[int, int, int], order: int
) -> tuple[tuple[F, F], ...]:
    """Taylor derivatives of tr F and tr F², with common factors i^n omitted."""
    z = base.scale(0, r.I4)

    def compose(
        a: tuple[base.Matrix, ...], b: tuple[base.Matrix, ...]
    ) -> tuple[base.Matrix, ...]:
        out = []
        for n in range(order + 1):
            m = z
            for j in range(n + 1):
                m = base.add(m, base.scale(comb(n, j), base.multiply(a[j], b[n - j])))
            out.append(m)
        return tuple(out)

    total = (r.I4,) + (z,) * order
    dots = tuple(sum(x * y for x, y in zip(d, direction, strict=True)) for d in r.TETRA)
    signs = REPS[1]
    rs = r.rotations()
    for pos in WORD:
        a, b = divmod(pos, 6)
        ca, cb = base.multiply(r.G, rs[a]), base.multiply(r.G, rs[b])
        series = tuple(
            base.multiply(
                base.matrix(
                    tuple(
                        tuple(
                            cb[i][j] * signs[i] * signs[j] * (dots[i] - dots[j]) ** n
                            for j in range(4)
                        )
                        for i in range(4)
                    )
                ),
                ca,
            )
            for n in range(order + 1)
        )
        total = compose(series, total)
    return tuple(
        (base.trace(a), base.trace(b))
        for a, b in zip(total, compose(total, total), strict=True)
    )


def witness() -> None:
    result = exact_word(REPS[1], WORD)
    r.need(
        result == (F(0), base.scale(4, base.identity(3))),
        "period-three isotropic witness",
    )
    for s in product((1, -1), repeat=3):
        if (1, *s) != REPS[1]:
            r.need(
                exact_word((1, *s), WORD) is None,
                "extra nonreal double corner for witness",
            )
    a, b = sector_traces((5, 0, 0), 4), sector_traces((3, 4, 0), 4)
    r.need(a != b, "no finite-wavelength discriminator")
    print(
        "Three fixed wirings (both sublattices equal per two ticks): at one real momentum corner F²=−I and the two conjugate Weyl cones both have first-order metric 4 I₃, with zero tilt. Spatial layout and a six-tick clock are supplied."
    )
    first = next(n for n, (x, y) in enumerate(zip(a, b, strict=True)) if x != y)
    print(
        f"Equal-length spatial directions (5,0,0) and (3,4,0) give different trace data by order {first}: {a[first]} vs {b[first]} with the common Fourier factor i^{first} omitted. First-order isotropy does not extend to all wavelengths."
    )


def census(period: int) -> None:
    """Optional NumPy integer accelerator; each reported witness is checked independently."""
    import numpy as np

    eye = np.eye(4, dtype=np.int64)
    for rep, signs in enumerate(REPS):
        gs = generators(signs)
        fs = np.array([base.scale(2, v[0]) for v in gs], dtype=np.int64)
        delta = np.array([[base.scale(4, h) for h in v[1]] for v in gs], dtype=np.int64)
        block = len(gs)
        previous = 2 * eye[None, :, :]
        deriv = np.zeros((1, 3, 4, 4), dtype=np.int64)
        # Spread the prefixes once; process last addresses separately to keep
        # the peak working set small. A word is numbered base 36, newest first.
        for depth in range(1, period + 1):
            rows = []
            drows = []
            candidates = 0
            hits = 0
            first = None
            for i in range(block):
                f2 = fs[i] @ previous
                d4 = fs[i] @ deriv @ fs[i].T
                r.need(
                    not np.any(f2 % 2) and not np.any(d4 % 4),
                    "corner-lattice denominator",
                )
                f = f2 // 2
                d = d4 // 4 + delta[i]
                if depth < period:
                    rows.append(f)
                    drows.append(d)
                    continue
                ft = f.transpose(0, 2, 1)
                scalars = f[:, 0, 0] * 2
                inds = np.flatnonzero(
                    np.all(f + ft == scalars[:, None, None] * eye, axis=(1, 2))
                    & (abs(scalars) < 4)
                )
                if not len(inds):
                    continue
                candidates += len(inds)
                k = (f - ft)[inds, None]
                q = (16 - scalars[inds] ** 2)[:, None, None, None]
                axes = q * d[inds] - k @ d[inds] @ k
                grams = np.einsum("niax,njax->nij", axes, axes)
                diag = grams[:, 0, 0]
                valid = np.flatnonzero(
                    np.all(
                        grams == diag[:, None, None] * np.eye(3, dtype=np.int64),
                        axis=(1, 2),
                    )
                    & (diag > 0)
                )
                hits += len(valid)
                if len(valid) and first is None:
                    n = int(inds[valid[0]]) + i * (block ** (depth - 1))
                    first = tuple((n // (block**j)) % block for j in range(depth))
            if depth < period:
                previous, deriv = np.concatenate(rows), np.concatenate(drows)
        result = exact_word(signs, first) if first is not None else None
        if period in EXPECTED:
            r.need((candidates, hits) == EXPECTED[period][rep], "finite census drift")
        if result:
            _, g = result
            r.need(
                g == base.scale(g[0][0], base.identity(3)) and g[0][0] > 0,
                "independent witness",
            )
        print(
            f"period={period} signs={signs}: {candidates}/{block**period} nonreal double carriers, {hits} isotropic rank-three; first={first} exact={result}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--period",
        type=int,
        choices=(1, 2, 3),
        help="optional exhaustive NumPy integer scan",
    )
    args = parser.parse_args()
    witness()
    if args.period is not None:
        census(args.period)


if __name__ == "__main__":
    main()
