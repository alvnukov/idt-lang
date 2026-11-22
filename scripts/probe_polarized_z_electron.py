"""What does a polarized Z-pole measurement add to an internal charge table?

On the existing even 16-mask carrier the 3+2 dictionary supplies a lepton
doublet and a conjugate charged singlet. It does NOT identify a laboratory
electron, its helicity, its current strength, a Z pole or any particle mass.
This probe changes only a supplied coupling-to-laboratory-helicity assignment.
It does not change a mask, pairing, charge, trace, anomaly check or invisible
current. It is not a second chiral gauge theory or a cross-adapter verdict:
the existing invisible-width adapter explicitly excludes visible new physics.

For real effective chiral couplings at one factorizing spin-1 resonance,
negligible external masses and the standard angular law, write wL,R = gL,R².
An unpolarized partial width fixes only their sum (up to a common factor).
The electron-only unpolarized pole forward/backward asymmetry is 3*A_e²/4;
polarized production gives A_e=(wL-wR)/(wL+wR). No equality of electron,
muon and tau couplings is used. The helicity-independent final-state factor
must cancel; additional exchanges, altered radiation, or helicity-dependent
acceptance need their own forward model. The conventional pole asymmetries
use real effective coupling parts, but full widths include imaginary parts.
Arbitrary complex Wilson coefficients are NOT compared to these data.

Primary sources (offline rounded published summaries; no event refit):
* SLD, https://arxiv.org/html/hep-ex/0004026, Eqs. (1)-(4), Table 1, text
  following Eq. (4), footnote 23. Counts are selected hadrons plus a small
  tau fraction, not tagged invisible decays. The sign uses measured laser
  helicity, measured Compton asymmetry and the theoretical Compton sign.
  Absolute beam polarization matters. Absolute luminosity cancels under the
  symmetry conditions, relative luminosity does not. Eq. (3) corrects for
  background, luminosity, polarization, energy and efficiency asymmetries
  and possible positron polarization. Pole extraction also corrects photon
  exchange and gamma-Z interference, depending on the calibrated beam energy.
* LEP collaborations/working groups, https://arxiv.org/html/hep-ex/0509008
  Eq. (1.66), Table 2.13, nine-parameter electron row WITHOUT universality.
  This is a corrected s-channel pseudo-observable: photon exchange/radiation,
  gamma-Z interference, and the Bhabha t-channel and s/t interference
  matter. It overlaps the LEP lineshape data, not an independent second LEP
  width. Its central value is an explicitly supplied sign-blind calibration.
* OPAL, https://arxiv.org/html/hep-ex/0103045, abstract and Sec. 8. Distinct
  detector/sample from SLD and a different method: forward/backward tau
  polarization, assuming V-A tau decay and correcting radiation/interference.
  Use its separately extracted electron value, not a universal-lepton fit.
  No combined significance, likelihood, exact exclusion or model preference.

Run: python3 -B -m scripts.probe_polarized_z_electron (also with -O).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from math import sqrt

from scripts.probe_chiral_carrier_holdout import EVEN, LABELS, block


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


@dataclass(frozen=True)
class Run:
    name: str
    left: int
    right: int
    raw: str
    raw_error: str
    polarization: str          # fractions, not percent
    polarization_error: str
    eq3_relative_percent: str
    eq3_relative_percent_error: str
    energy_gev: str
    collision: tuple[str, str, str]  # central, statistical, systematic
    pole: tuple[str, str, str]

    def raw_asymmetry(self) -> F:
        return F(self.left - self.right, self.left + self.right)

    def polarization_only(self) -> F:
        return self.raw_asymmetry() / F(self.polarization)


RUNS = (
    Run("1996", 29016, 22857, "0.11873", "0.00436", "0.7616", "0.0040",
        "+0.02", "0.05", "91.26", ("0.1559", "0.00572", "0.00084"),
        ("0.15929", "0.00573", "0.00101")),
    Run("1997-98", 183355, 148259, "0.10583", "0.00173", "0.7292", "0.0038",
        "+0.16", "0.07", "91.237", ("0.1454", "0.00237", "0.00077"),
        ("0.14906", "0.00237", "0.00096")),
)
SLD_96_98_POLE = ("0.15056", "0.00239")
SLD_ALL_POLE = ("0.15138", "0.00216")
LEP_ELECTRON_FB = ("0.0145", "0.0025")
OPAL_ELECTRON = ("0.1454", "0.0108", "0.0036")


def replay_counts() -> F:
    for run in RUNS:
        a = run.raw_asymmetry()
        n = run.left + run.right
        se = sqrt((1 - a*a) / n)  # conditional binomial counting error, not pole uncertainty
        need(round(a, 5) == F(run.raw) and f"{se:.5f}" == run.raw_error,
             f"{run.name}: counts do not reproduce published Eq. 2")
        print(f"{run.name}: NL={run.left}, NR={run.right}; raw A_m={a} = {float(a):.7f}"
              f" (counting error {se:.5f}); <P>={run.polarization} +/- {run.polarization_error}.")
        print(f"  A_m/<P>={float(run.polarization_only()):.7f} (polarization only);"
              f" published Eq. 3 relative correction {run.eq3_relative_percent}"
              f" +/- {run.eq3_relative_percent_error} percent.")
        print(f"  Reported A_LR at {run.energy_gev} GeV: {' +/- '.join(run.collision)};"
              f" corrected pole: {' +/- '.join(run.pole)} (stat, syst).")
    left = sum(r.left for r in RUNS)
    right = sum(r.right for r in RUNS)
    pooled = F(left - right, left + right)
    need((left, right, pooled) == (212371, 171116, F(41255, 383487)), "pooled selected counts")
    print(f"1996-98 pooled raw={pooled} = {float(pooled):.7f}; not a pole estimate."
          f" Reported combined pole {' +/- '.join(SLD_96_98_POLE)}; full 1992-98"
          f" {' +/- '.join(SLD_ALL_POLE)} includes these same events. Not recombined.")
    return pooled


def asymmetry(left: F, right: F) -> F:
    """Nonnegative rates in a *fixed laboratory basis*, not amplitude signs."""
    if min(left, right) < 0 or left + right == 0:
        raise ValueError("normalized asymmetry needs nonnegative rates and positive total")
    return (left - right) / (left + right)


def carrier_and_controls() -> None:
    # External dictionary. Nominate one component of L and the antiparticle of
    # e^c. Neither the choice of weak component nor lab helicity is inferred.
    doublet = tuple(m for m in EVEN if LABELS[block(m)] == "L")
    singlet = tuple(m for m in EVEN if LABELS[block(m)] == "e")
    need(doublet == (15, 23) and singlet == (24,), "same carrier / external 3+2 labels")
    electron_ports = (23, 24)  # second refers to the charge conjugate of this mask
    # Squared real amplitudes 2 and 1 (arbitrary control, NOT a magnitude fit).
    weights = dict(zip(electron_ports, (F(4), F(1)), strict=True))
    currents = [tuple(weights[m] for m in ports) for ports in (electron_ports, electron_ports[::-1])]
    need([sum(v) for v in currents] == [5, 5] and
         [asymmetry(*v) for v in currents] == [F(3, 5), F(-3, 5)], "exact mirror control")
    need(asymmetry(F(1), F(1)) == 0 and asymmetry(F(36), F(9)) == F(3, 5),
         "equal weights give zero; nonzero common amplitude scaling leaves A alone")
    # In an *ideal resolved-amplitude model*, a phase or common real
    # orthogonal rotation of unobserved final channels preserves both norms.
    # Rotating the physical incoming helicity axis is NOT this invariance.
    for im in (-1, 1):
        for overall in (-1, 1):
            left = ((F(overall), F(im*overall)), (F(0), F(0)))
            right = ((F(0), F(0)), (F(overall), F(0)))
            rates = []
            for z, w in (left, right):
                a, b = F(3, 5), F(4, 5)
                rot = tuple(a*x - b*y for x, y in zip(z, w, strict=True)), tuple(
                    b*x + a*y for x, y in zip(z, w, strict=True))
                rates.append(sum(x*x for row in rot for x in row))
            need(rates == [2, 1] and asymmetry(*rates) == F(1, 3),
                 "ideal squared moduli: sign, conjugation and unresolved-channel rotation")
    try:
        asymmetry(F(0), F(0))
    except ValueError:
        pass
    else:
        raise ArithmeticError("no Z signal must not be labeled a zero asymmetry")
    print("Carrier L={15,23}, e^c={24}; lab port and current assignments supplied."
          " Real-amplitude (2,1) versus (1,2): total 5, A=+3/5 versus -3/5."
          " Neither magnitude describes the observed result.")


def calibrated_mirror() -> None:
    """Exact coefficients (a,b) stand for a + b*sqrt(r), r fixed by LEP, not SLD."""
    fb, fb_error = map(F, LEP_ELECTRON_FB)
    radicand = F(4, 3) * fb
    need(radicand == F(29, 1500) and 0 < radicand < 1, "physical central-value branches")
    sld, sld_error = map(F, SLD_ALL_POLE)
    # Only classify the reported sign, not the degree of numerical agreement.
    observed_sign = 1 if sld - sld_error > 0 else -1 if sld + sld_error < 0 else 0
    same_sign = []
    for hand in (1, -1):
        # Unit total is merely a common normalization. Multiplication by an
        # independent positive width scale gives the same comparison.
        left, right = (F(1, 2), F(hand, 2)), (F(1, 2), F(-hand, 2))
        total = tuple(x+y for x, y in zip(left, right, strict=True))
        diff = tuple(x-y for x, y in zip(left, right, strict=True))
        need(total == (1, 0) and diff == (0, hand), "width fixed, difference reversed")
        need(F(3, 4)*diff[1]**2*radicand == fb, "identical electron-only A_FB")
        if diff[1] == observed_sign:
            same_sign.append(hand)
    need(same_sign == [1], "signed SLD observation distinguishes the branches")
    print(f"LEP electron-only pole A_FB={' +/- '.join(LEP_ELECTRON_FB)};"
          f" central-value branches A_e=+/-sqrt({radicand}) = +/-{sqrt(radicand):.5f}.")
    lo, hi = (sqrt(F(4, 3)*x) for x in (fb-fb_error, fb+fb_error))
    print(f"Mapping the printed central +/- quoted error endpoints gives |A_e|"
          f" {lo:.5f}..{hi:.5f}; not a likelihood or a confidence interval.")
    print(f"Only branch {same_sign[0]:+d} has the SLD sign; its calibrated magnitude"
          f" differs from the SLD central value by {float(sld)-sqrt(radicand):.5f}"
          " (SLD minus LEP-based branch, descriptive only).")
    print(f"OPAL tau method A_e="
          f"{' +/- '.join(OPAL_ELECTRON)} (stat, syst), conditional on V-A tau decay."
          " No joint significance, phase determination, or primitive verdict.")


def main() -> None:
    replay_counts()
    carrier_and_controls()
    calibrated_mirror()


if __name__ == "__main__":
    main()
