"""Offline numerical replay of rounded published Z-fit summaries, not event data."""

import argparse
import json
import math
from pathlib import Path


RECEIPT = Path(__file__).resolve().parents[1] / "data/published_observations/z_invisible_width_v1.json"
PARAMETERS = ("mass_z_gev", "sigma_had_nb", "r_lepton")
UNITS = ("GeV", "nb", "1")
# Exact SI definitions of h, c and e; 1 GeV = 10^9 eV; 1 nb = 10^-37 m^2.
HBARC_GEV_M = 6.62607015e-34 * 299792458 / (2 * math.pi * 1.602176634e-19 * 1e9)
NB_PER_GEV_MINUS_TWO = HBARC_GEV_M**2 / 1e-37


def read_receipt():
    return json.loads(RECEIPT.read_text(encoding="utf-8"))


def replay(data):
    """Apply Janot/Jadach Eq. (1), with first-order covariance on rounded inputs."""
    original, updated, atlas = (data[k] for k in ("lep_original", "lep_updated", "atlas"))
    if (original["sample"] != updated["sample"] or atlas["sample"] == original["sample"]
            or atlas["normalization"] != "external_LEP_charged_leptonic_width"
            or data["boundary"]["mode"] != "descriptive_only_no_combination"):
        raise ValueError("LEP reanalyses share events; the ATLAS MeV normalization is external")
    fit = updated["fit_inputs"]
    if tuple(fit["correlation_order"]) != PARAMETERS or tuple(fit[k]["unit"] for k in PARAMETERS) != UNITS:
        raise ValueError("parameter order or unit mismatch")
    corr = fit["correlations"]
    if (len(corr) != 3 or any(len(row) != 3 for row in corr)
            or any(corr[i][i] != 1 for i in range(3))
            or any(corr[i][j] != corr[j][i] or abs(corr[i][j]) > 1
                   for i in range(3) for j in range(3))):
        raise ValueError("malformed fit-input correlation matrix")
    m, sigma_nb, lepton = (fit[k]["value"] for k in PARAMETERS)
    r = updated["r_nu"]["value"]
    pole_term = math.sqrt(12 * math.pi / m**2 * lepton / (sigma_nb / NB_PER_GEV_MINUS_TWO))
    r_inv = pole_term - lepton - 3 - fit["delta_tau"]
    n_eff = r_inv / r
    # Jacobian of R_inv in covariance order; r_nu is an independent *theory input*
    # to this approximate uncertainty propagation, not another measurement.
    dr = (-pole_term / m, -pole_term / (2 * sigma_nb), pole_term / (2 * lepton) - 1)
    weighted = [derivative * fit[k]["error"] for k, derivative in zip(PARAMETERS, dr)]
    r_inv_variance = math.fsum(weighted[i] * corr[i][j] * weighted[j]
                               for i in range(3) for j in range(3))
    theory_component = abs(-n_eff / r) * updated["r_nu"]["error"]
    uncertainty = math.hypot(math.sqrt(r_inv_variance) / r, theory_component)
    original_quotient = original["r_inv"]["value"] / original["r_nu"]["value"]
    return {
        "lep_original": {
            "reported": original["n_eff"], "rounded_ratio_quotient": original_quotient,
        },
        "lep_updated": {
            "reported": updated["n_eff"], "replayed_n_eff": n_eff, "replayed_error": uncertainty,
            "replayed_r_inv": r_inv, "replayed_r_inv_error": math.sqrt(r_inv_variance),
            "error_component_external_r_nu": theory_component,
            "nb_per_gev_minus_two": NB_PER_GEV_MINUS_TWO,
            "uncertainty_method": "linear propagation of the Table 12 submatrix and independent external r_nu error; delta_tau fixed",
        },
        "atlas": {
            "reported_mev": atlas["gamma_inv_mev"], "normalization": atlas["normalization"],
        },
        "mode": data["boundary"]["mode"],
    }


def agrees_with_publication(result):
    """One printed last place for central value, half for error (rounded inputs)."""
    updated = result["lep_updated"]
    return (abs(updated["replayed_n_eff"] - updated["reported"]["value"]) < 0.0001
            and abs(updated["replayed_error"] - updated["reported"]["error"]) < 0.00005)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="compact JSON")
    args = parser.parse_args()
    result = replay(read_receipt())
    result["rounded_input_replay_agrees"] = agrees_with_publication(result)
    print(json.dumps(result, indent=None if args.json else 2, allow_nan=False))
    return 0 if result["rounded_input_replay_agrees"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
