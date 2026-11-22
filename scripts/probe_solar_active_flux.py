"""SNO: three solar-neutrino reactions distinguish active flux, not coherence.

This is an offline replay of *published summaries*, not detector events or a
fit to tune an IDT candidate. Flux unit: 10^6 / (cm² s). Channel order: CC,
ES, NC. Electron-neutrino cross sections define the three equivalent fluxes.
For the constrained Phase-I analysis assume the standard boron-8 spectrum,
the published detector response/backgrounds and 5 MeV effective kinetic
energy threshold. The deuteron charged current selects electron neutrinos;
the neutral current samples all standard active flavors equally; elastic
scattering on electrons has a smaller mu/tau response. No predicted solar
flux normalization is needed for the electron-only comparison. To infer a
change on the way from the Sun also requires an electron-flavor source.

Primary sources:
* SNO, https://arxiv.org/html/nucl-ex/0610020 , Eqs. (39)-(41), Tables
  18-20 and Secs. X.1.2, X.6: fitted counts (not identified events),
  symmetric statistical errors/correlations, efficiencies, MC yields and
  corrections, direct flavor fit. Use the integrated ES coefficient 0.1559
  of Eq. (40), not the separate day/night approximation 1/6.48.
* SNO, https://arxiv.org/html/nucl-ex/0204008 , Fig. 3 and adjoining text:
  original result, asymmetric errors and author-reported null significance.
  SAME pure-D2O events as the detailed analysis, not a replication. The
  authors' 5.3 sigma concerns nonzero active non-electron flux under these
  assumptions, not a comparison of coherent and classical mechanisms.
* SNO, https://arxiv.org/html/nucl-ex/0309004 : distinct salt-phase events,
  same collaboration; neutron capture on chlorine gives a more isotropic
  light pattern, enabling extraction without imposing CC/ES energy shapes.
* KamLAND, https://arxiv.org/html/hep-ex/0406035 , Fig. 2 discussion:
  separate reactor electron ANTINEUTRINO inverse-beta sample, prompt energy
  threshold 2.6 MeV. Test of a free normalization of the no-oscillation
  reactor spectrum. Not a solar measurement or a proof against all classical
  energy-dependent laws. No solar/antineutrino parameter identification.

The author data page https://sno.phy.queensu.ca/sno/prlwebpage/ links day/
night spectra, live time and backgrounds. We do not redistribute its files,
use an unbinned likelihood or combine the reported significances.
Run: python3 -B -m scripts.probe_solar_active_flux (also with -O).
"""

from __future__ import annotations

from fractions import Fraction as F
from math import sqrt


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def row(*decimal: str) -> tuple[F, ...]:
    return tuple(map(F, decimal))


def dot(a, b) -> F:
    return sum((x*y for x, y in zip(a, b, strict=True)), F())


# Phase-I Table 18/19/20: (CC, ES, NC), not (CC, NC, ES).
COUNTS = row("1967.71", "263.64", "576.53")
COUNT_SD = row("61.36", "25.68", "48.82")
CORR = (row("1", "-.162", "-.520"), row("-.162", "1", "-.105"), row("-.520", "-.105", "1"))
MC_PER_UNIT = row("1120.48", "115.83", "116.23")
# Published PRODUCTS include live time, cut efficiency, applicable oxygen,
# eccentricity and cross-section corrections; do not apply cut efficiency twice.
CORRECTION = row("1.0043", "1.0500", "1.0267")
R = F("0.1559")


def replay_sno() -> None:
    scale = tuple(c/n for c, n in zip(CORRECTION, MC_PER_UNIT, strict=True))
    y = tuple(n*s for n, s in zip(COUNTS, scale, strict=True))
    sd = tuple(e*s for e, s in zip(COUNT_SD, scale, strict=True))
    v = tuple(tuple(sd[i]*sd[j]*CORR[i][j] for j in range(3)) for i in range(3))
    # Check positive definiteness (all three leading principal minors positive).
    a, b, c = v[0]
    d, e = v[1][1:]
    f = v[2][2]
    need(v == tuple(zip(*v, strict=True)) and min(a, a*d-b*b,
         a*(d*f-e*e) - b*(b*f-c*e) + c*(b*e-c*d)) > 0, "bad covariance")

    # Two flavor fluxes predict (e, e+r*x, e+x), so one linear contrast
    # vanishes. Generalized least squares projects the three measured fluxes
    # onto this plane in the inverse-covariance metric. All projection
    # arithmetic is exact on the printed decimals; the likelihood is NOT.
    contrast = (R-1, F(1), -R)
    vc = tuple(dot(v_i, contrast) for v_i in v)
    den = dot(contrast, vc)
    fit = tuple(y_i - vc_i*dot(contrast, y)/den for y_i, vc_i in zip(y, vc, strict=True))
    e_flux, x_flux = fit[0], fit[2] - fit[0]
    need(fit == (e_flux, e_flux + R*x_flux, e_flux + x_flux), "invalid flavor projection")
    vf = tuple(tuple(v[i][j]-vc[i]*vc[j]/den for j in range(3)) for i in range(3))
    var_e, var_x = vf[0][0], vf[0][0] + vf[2][2] - 2*vf[0][2]
    rho = float(vf[0][2]-var_e)/sqrt(var_e*var_x)
    estimates = (e_flux, x_flux, sqrt(var_e), sqrt(var_x), rho)
    need(tuple(f"{float(x):.5f}" for x in estimates) ==
         ("1.76819", "3.37299", "0.05396", "0.45036", "-0.67768"),
         "rounded statistical-only covariance replay")
    need(tuple(round(x, 2) for x in y) == row("1.76", "2.39", "5.09"), "three equivalent fluxes")
    print("SNO pure D2O, standard undistorted B-8 spectrum; flux units 10^6/(cm² s).")
    print("CC, ES, NC fluxes from their OWN fitted yields, MC and corrections:",
          ", ".join(f"{float(z):.5f}" for z in y))
    print(f"NC-CC alone: {float(y[2]-y[0]):.5f}. Three-channel statistical GLS:"
          f" e={float(e_flux):.5f} +/- {sqrt(var_e):.5f},"
          f" mu+tau={float(x_flux):.5f} +/- {sqrt(var_x):.5f}, corr={rho:.5f}.")
    print("Published direct joint flavor fit: e=1.76 +/-0.05(stat) +/-0.09(syst);"
          " mu+tau=3.41 +/-0.45(stat) +0.48/-0.45(syst); stat corr=-0.678."
          " SNO reports 5.3 sigma above zero; not reconstructed here.")


def flux_response(populations: tuple[F, F, F, F]) -> tuple[F, F, F]:
    """Diagonal active-flavor response per unit flux; fourth state sterile."""
    need(min(populations) >= 0 and sum(populations) == 1, "invalid incident populations")
    e, mu, tau, _sterile = populations
    return e, e + R*(mu+tau), e + mu + tau


def expected_channel_counts(fluxes, total_flux: F) -> tuple[F, ...]:
    """Separate calibrated acceptance and scale for each reaction."""
    need(total_flux >= 0, "negative incident flux")
    return tuple(total_flux*p*n/c for p, n, c in zip(fluxes, MC_PER_UNIT, CORRECTION, strict=True))


def matched_controls() -> None:
    # Write omega = exp(2 pi i/3) exactly as a pair (a,b) for a+b*omega.
    # Fourier tritter U_ij=omega^(i*j)/sqrt(3) vs a fresh classical uniform
    # choice at every application. Not claimed to describe solar propagation.
    omega = ((1, 0), (0, 1), (-1, -1))

    def one_step_rate(i: int, j: int) -> F:
        a, b = omega[(i*j) % 3]
        return F(a*a - a*b + b*b, 3)  # modulus squared of (a+b*omega)/sqrt(3)

    def root_sum(exponents) -> tuple[int, int]:
        terms = [omega[k % 3] for k in exponents]
        return sum(z[0] for z in terms), sum(z[1] for z in terms)

    for i in range(3):
        for j in range(3):
            need(root_sum((i-j)*k for k in range(3)) == (3*int(i == j), 0), "unitary columns")
    # Column zero has three identical amplitudes 1/sqrt(3). Classical
    # channel on |e> and a source mixture with no conversion give the same
    # three populations. This equality of diagonals survives arbitrary
    # diagonal energy-bin response when the incident spectra agree pointwise.
    e_only = (F(1), F(0), F(0), F(0))
    coherent = tuple(one_step_rate(i, 0) for i in range(3)) + (F(0),)
    classical = tuple(sum(e_only[:3])/3 for _ in range(3)) + (F(0),)
    source_mix = (F(1, 3), F(1, 3), F(1, 3), F(0))
    matched = (F(1, 3), F(6559, 15000), F(1))
    need(coherent == classical == source_mix, "different mechanisms, same incident populations")
    counts = [expected_channel_counts(flux_response(state), F(1)) for state in
              (coherent, classical, source_mix)]
    need(flux_response(coherent) == matched and counts[0] == counts[1] == counts[2],
         "same three calibrated event means")
    need(flux_response(e_only) == (1, 1, 1) and matched[0] != matched[2],
         "electron-only: all equivalent fluxes equal, not all event counts equal")
    need(len(set(expected_channel_counts(flux_response(e_only), F(1)))) == 3, "channel normalizations")
    mu = (F(0), F(1), F(0), F(0))
    tau = (F(0), F(0), F(1), F(0))
    sterile = (F(0), F(0), F(0), F(1))
    need(flux_response(mu) == flux_response(tau) == (0, R, 1)
         and flux_response(sterile) == (0, 0, 0), "mu/tau indistinguishable; sterile invisible")
    half_sterile = tuple((p+q)/2 for p, q in zip(source_mix, sterile, strict=True))
    need(expected_channel_counts(flux_response(half_sterile), F(2)) == counts[0],
         "without a source normalization, extra sterile flux need not change any active count")
    # A second identical unitary returns the incident electron, whereas a
    # fresh classical mixer (or a diagonal mixture sent through one tritter)
    # gives uniform populations. The following is a toy intervention, NOT a
    # claim that a different solar or reactor baseline implements this gate.
    twice = tuple(root_sum(i*k for k in range(3)) for i in range(3))
    need(twice == ((3, 0), (0, 0), (0, 0)) and sum(classical[:3])/3 == F(1, 3),
         "amplitude sums before normalization by 3; independent classical redraw")
    # Even the return is not uniquely quantum. A classical reversible swap of
    # the observed trit with a hidden uniform trit produces the same one-stage
    # uniform output AND two-stage return, with no fresh independent redraw.
    initial = [(0, b) for b in range(3)]
    once = [(b, a) for a, b in initial]
    again = [(b, a) for a, b in once]
    need(sorted(a for a, _ in once) == [0, 1, 2] and again == initial,
         "classical retained-memory control reproduces return")
    print(f"Exact one-stage CC, ES, NC controls per unit flux: e only (1,1,1);"
          f" coherent tritter = classical redraw = source mixture ({', '.join(map(str, matched))}).")
    print("Illustrative second operation: coherent P(e)=1, fresh classical redraw 1/3,"
          " reversible classical swap with retained hidden trit 1."
          " SNO did not perform this intervention. It cannot count species, split mu/tau,"
          " recover sterile flux, or identify propagation coherence from these three rates.")


def main() -> None:
    replay_sno()
    matched_controls()
    print("Different SNO salt-phase events: CC/NC=0.306 +/-0.026(stat) +/-0.024(syst);"
          " no imposed CC/ES spectral shapes for the NC extraction. Not a combined significance.")
    print("Separate KamLAND antineutrinos: free-normalization no-oscillation spectral shape,"
          " reported goodness of fit 0.4% (37.3/18, 20 bins, 10000 simulations; binning matters)."
          " No fit replay, solar parameter transfer or exclusion of general classical models.")


if __name__ == "__main__":
    main()
