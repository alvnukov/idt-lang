"""What relative reactor spectra can and cannot distinguish.

Default: python3 -B -O -m scripts.probe_reactor_relative_clocks
Replay: add --archive PATH [--cnp-diagnostic]. No network access. The
optional CNP diagnostic alone requires NumPy; it is NOT a calibrated test.

PROSPECT-I final oscillation analysis, Eqs. (2)-(3):
  https://arxiv.org/html/2406.10408v2
Collaboration release: https://arxiv.org/abs/2406.10408v2 (ancillary files).
We retrieved the unmodified gzip source archive via HTTPS GET:
  https://arxiv.org/src/2406.10408v2
Each pinned member is also at https://arxiv.org/src/2406.10408v2/anc/data/
followed by its exact release-relative name in SPECTRA or COV below.
The 30-spectra and combined 33-file manifest digests fingerprint each
original member by name AND byte content; manifest_digest defines the format.

In each period, let M[l,e] be background-subtracted IBD counts (not raw
Poisson counts) and P[l,e] the supplied detector-space signal prediction.
The relative prediction is M[*,e] P[l,e]/P[*,e], where * sums baselines.
Multiplying every baseline's P at one reconstructed energy by the same
positive number leaves it unchanged. A global survival factor always cancels;
a factor at TRUE energy need not cancel after different responses are folded.
Different baseline efficiencies generally do NOT cancel. Source weights,
calibration, response and efficiencies are already included in P; do not
divide by them again. Do not subtract the released backgrounds again from M.
The author's REL column block is used only for a central SHAPE checksum:
match its per-period total to the measured signal total before comparing.
This explicitly discards the absolute rate, without fitting a shape parameter.

The collaboration's sterile-oscillation scan is consistent with its null
(reported toy-comparison p=0.87). The earlier PROSPECT data are not an
independent experiment; STEREO at another reactor independently reports
consistency with its no-oscillation hypothesis (p=0.52):
https://doi.org/10.1038/s41586-022-05568-2 . Neither p tests our controls.
The central replay is not a fit, an exclusion, or a native neutrino model.
No map from native ticks to metres or energy, source preparation, IBD
coupling, independent flux normalization, or emergence of geometry is derived.
To test a new law, freeze these bridges independently of these residuals,
fold its joint baseline/energy distribution through the detector, and verify
the likelihood and sensitivity before assigning significance.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import tarfile
from fractions import Fraction as F
from pathlib import Path

ARCHIVE_BYTES = 6_348_855
ARCHIVE_SHA = "0e8a7a4314a1405df00000d54249b54ae9031726ee716ed3336df34f255ab7f0"
SPECTRA = tuple(
    f"Period_{p}/Spectra_for_baseline_bin_{b}.txt"
    for p in range(1, 6) for b in range(1, 7)
)
COV = tuple(f"CovarianceMatrices/{name}CovMatrix.txt"
            for name in ("Statistical", "Systematic", "Background"))
SPECTRA_SHA = "88759dae909f8c240a42a5223c37a06d654eb234a42275ba998d55c24cddb1cc"
COMBINED_SHA = "afad7f61f5533130bec3e8baed2b502c762063f3a74eeffdb88eeb7b54798123"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def relative(measured, predicted):
    """One period; matrices indexed by baseline and reconstructed energy."""
    need(bool(measured) and len(measured) == len(predicted), "baseline dimensions")
    width = len(measured[0])
    need(width > 0 and all(len(row) == width for row in (*measured, *predicted)),
         "energy dimensions")
    m = tuple(map(sum, zip(*measured)))
    p = tuple(map(sum, zip(*predicted)))
    need(all(x >= 0 for row in predicted for x in row) and all(x > 0 for x in p),
         "invalid predicted signal or undefined relative comparison")
    return tuple(tuple(m[e] * y / p[e] for e, y in enumerate(row)) for row in predicted)


def synthetic_controls():
    # Purely synthetic detector kernel with unequal exposure/efficiency and
    # non-proportional energy responses. These integer depths are NOT metres.
    weights = ((F(12), F(5)), (F(8), F(9)), (F(4), F(16)))
    measured = ((F(10), F(7)), (F(6), F(12)), (F(5), F(14)))
    depths = ((0, 1), (1, 2), (2, 3))

    def clock(initial):
        # Deterministic 0->1->2->0; only state 0 clicks.
        return tuple(tuple(w * initial[-t % 3] for w, t in zip(row, dr))
                     for row, dr in zip(weights, depths))

    bright = relative(measured, weights)                    # always bright
    uniform = relative(measured, clock((F(1, 3),) * 3))      # exactly 1/3
    need(bright == uniform, "stationary uniform cycle should cancel exactly")
    rescaled = tuple((row[0] * F(2, 7), row[1] * F(5, 8)) for row in weights)
    need(relative(measured, rescaled) == bright, "columnwise scale did not cancel")
    biased = relative(measured, clock((F(1, 2), F(1, 3), F(1, 6))))
    # First energy: bright 21*(12/24); biased 21*(6/(6+4/3+4/3)).
    need(bright[0][0] == F(21, 2) and biased[0][0] == F(189, 13),
         "the independently specified baseline-shape control was not distinguished")
    print("Exact synthetic controls: always bright = uniform three-cycle in relative shape;"
          " biased three-cycle differs (first bin: 21/2 vs 189/13 predicted counts).")


def manifest_digest(files):
    body = "".join(f"{hashlib.sha256(files[k]).hexdigest()}  {k}\n" for k in sorted(files))
    return hashlib.sha256(body.encode("ascii")).hexdigest()


def read_release(path, diagnostic):
    wanted = set(SPECTRA + (COV if diagnostic else ()))
    with path.open("rb") as src:
        raw = src.read(ARCHIVE_BYTES + 1)
    need(len(raw) == ARCHIVE_BYTES and hashlib.sha256(raw).hexdigest() == ARCHIVE_SHA,
         "source archive size or SHA-256 does not match the pinned release")
    files = {}
    # Only process this authenticated archive; copy only allowlisted regular
    # file contents into memory. No extraction onto disk or link following.
    with tarfile.open(fileobj=io.BytesIO(raw), mode="r|gz") as archive:
        for member in archive:
            if not member.name.startswith("anc/data/"):
                continue
            name = member.name[len("anc/data/"):]
            if name not in wanted:
                continue
            need(member.isfile() and name not in files and 0 < member.size <= 14_000_000,
                 "invalid or duplicate release member")
            with archive.extractfile(member) as item:
                files[name] = item.read(member.size)
            need(len(files[name]) == member.size, "truncated release member")
    need(files.keys() == wanted, "incomplete release")
    need(manifest_digest({k: files[k] for k in SPECTRA}) == SPECTRA_SHA,
         "spectra manifest mismatch")
    if diagnostic:
        need(manifest_digest(files) == COMBINED_SHA, "covariance manifest mismatch")
    return files


def parse_spectrum(data):
    # Five consecutive 33-row blocks: predicted, relative-predicted,
    # measured (background-subtracted), cosmogenic background, accidentals.
    rows = [line.split() for line in data.decode("ascii").splitlines()
            if line.strip() and not line.lstrip().startswith("#")]
    need(len(rows) == 165, "spectrum dimensions")
    blocks = []
    for start in range(0, len(rows), 33):
        values = []
        for i, row in enumerate(rows[start:start + 33]):
            need(len(row) == 4 and int(row[0]) == i + 1
                 and F(row[1]) == F(9 + 2 * i, 10) and F(row[3]) >= 0,
                 "invalid bin, prompt energy in MeV or statistical error")
            values.append(F(row[2]))
        blocks.append(tuple(values))
    return tuple(blocks)


def cnp_diagnostic(files, measured, predicted, cosmogenic):
    """Unresolved covariance convention; do NOT attach a p-value to this."""
    import numpy as np  # optional; never used for central replay

    stat, sys, bkg = (np.loadtxt(io.BytesIO(files[k])) for k in COV)
    need(all(x.shape == (990, 990) for x in (stat, sys, bkg)), "covariance dimensions")
    m, p, b = (np.array(x, dtype=float) for x in (measured, predicted, cosmogenic))
    # Candidate convention: count^2 stat; reduced signal (background) cov
    # times the outer product of relative prediction (cosmogenic counts).
    v = stat + sys * np.outer(p, p) + bkg * np.outer(b, b)
    d = m - p
    value = float(d @ np.linalg.solve(v, d))
    need(abs(value - 831.49242664) < 0.00001, "diagnostic replay changed")
    print(f"Unresolved CNP reconstruction: {value:.6f}; paper null about 829.57"
          " (rounded minimum 827 + 2.57). No reproduced likelihood or native exclusion.")


def replay(path, diagnostic):
    files = read_release(path, diagnostic)
    measured, predicted, background = [], [], []
    max_residual = F()
    for period in range(5):
        bins = [parse_spectrum(files[k]) for k in SPECTRA[6 * period:6 * (period + 1)]]
        p, rel, m, b, _ = zip(*bins)
        central = relative(m, p)
        # One explicit display normalization per period. It is completely
        # determined by totals, not optimized against any bin residuals.
        scale = sum(map(sum, m)) / sum(map(sum, rel))
        for rows in zip(m, central, rel, b):
            for obs, calc, ref, bg in zip(*rows):
                measured.append(obs)
                predicted.append(calc)
                background.append(bg)
                max_residual = max(max_residual, abs(calc - scale * ref))
    need(len(predicted) == 990 and max_residual < F(161, 1_000_000),
         "central checksum outside the pinned tables' replay tolerance")
    print(f"PROSPECT-I central relative shape: 990 bins; maximum absolute discrepancy"
          f" {float(max_residual):.10f} counts after per-period total normalization.")
    if diagnostic:
        cnp_diagnostic(files, measured, predicted, background)
    else:
        print("Central values only. Full CNP reproduction remains unresolved;"
              " no confidence level or native exclusion.")


def main():
    ap = argparse.ArgumentParser(description="Relative reactor shape and clock controls.")
    ap.add_argument("--archive", type=Path, help="local unmodified arXiv:2406.10408v2 source")
    ap.add_argument("--cnp-diagnostic", action="store_true",
                    help="also replay the unresolved covariance convention (requires NumPy)")
    args = ap.parse_args()
    if args.cnp_diagnostic and args.archive is None:
        ap.error("--cnp-diagnostic requires --archive")
    synthetic_controls()
    if args.archive is not None:
        replay(args.archive, args.cnp_diagnostic)


if __name__ == "__main__":
    main()
