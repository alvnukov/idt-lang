"""One prespecified finite-count test, not a general tomogram or empirical verdict.

JSON input: schema, contract (all four named Boolean declarations below), and
programs (exactly the three names below; each has integer issued, plus, minus).
Use independent Bernoulli units WITHIN each fixed-size program; different
programs may be dependent. Complete scoring, calibrated contacts and a common
neutral real population are external premises, not verified by the checker.
There is no optional stopping, search over settings/witnesses, or refitting.

Let h=(minus01, minus12, minus01 after swap12 with both first flags retained).
Then l02=2*h[2]-h[0]. For u=(3,1,-4), u^T R u = -6*l01+8*l12+24*l02
= -30*h[0]+8*h[1]+48*h[2] >= 0 for a common PSD moment R. At the fixed
corners (31/32,33/64,33/64) this equals -3/16, so the null requires at
least one of h[0]<=31/32, h[1]>=33/64, h[2]>=33/64. Use the MAX of the
three exact directional binomial tails: under the null at least one tail is
a valid conservative p-value. No joint independence or multiplicity benefit
is required. Failure to reject is not evidence of compatibility.

CLI: python3 -B -m scripts.check_triangle_population_witness < counts.json
Outputs JSON; exit 0 = conditional report issued, 2 = malformed input.
"""

import json
import sys
from fractions import Fraction as F

SCHEMA = "idt-triangle-population-witness/1"
PROGRAMS = ("swap01", "swap12", "swap12_then_swap01_keep_both")
CONTRACT = ("prespecified_fixed_design", "independent_units_within_program",
            "common_preparation", "calibrated_contacts_and_scoring")
CORNER = (F(31,32), F(33,64), F(33,64))
ALPHA = F(1,64)
MAX_N = 16384


def fields(value, keys):
    if type(value) is not dict or set(value) != set(keys):
        raise ValueError("expected exactly: " + ", ".join(keys))
    return value


def lower_tail(n, k, p):
    """P[Bin(n,a/b)<=k] as a rational; recurring integer terms are exact."""
    a, b = p.numerator, p.denominator
    term = (b-a)**n
    total = term
    for j in range(k):
        term = term * (n-j)*a // ((j+1)*(b-a))
        total += term
    return F(total, b**n)


def check(value):
    fields(value, ("schema", "contract", "programs"))
    if value["schema"] != SCHEMA:
        raise ValueError("wrong schema")
    contract = fields(value["contract"], CONTRACT)
    if any(type(flag) is not bool for flag in contract.values()):
        raise ValueError("contract declarations must be Boolean")
    programs = fields(value["programs"], PROGRAMS)
    missing = 0
    counts = []
    for name in PROGRAMS:
        row = fields(programs[name], ("issued", "plus", "minus"))
        n, plus, k = (row[key] for key in ("issued", "plus", "minus"))
        if (any(type(x) is not int for x in (n,plus,k)) or not 1 <= n <= MAX_N
                or min(plus,k) < 0 or plus+k > n):
            raise ValueError("invalid counts or unsupported sample size")
        missing += n-plus-k
        counts.append((n,k))
    result = {"schema": SCHEMA, "alpha": str(ALPHA), "corner_witness": "-3/16",
              "empirical_verdict": "not_assessed", "generic_candidate_verdict": "not_assessed",
              "unmet_declarations": [key for key in CONTRACT if not contract[key]],
              "missing_outcomes": missing}
    if missing or result["unmet_declarations"]:
        return dict(result, decision="contract_not_met")
    n0, k0 = counts[0]
    p = max(lower_tail(n0, n0-k0, 1-CORNER[0]),
            *(lower_tail(n, k, t) for (n,k),t in zip(counts[1:], CORNER[1:], strict=True)))
    # Compare before rounding; never print giant rational numerators/denominators.
    upper = -((-1_000_000*p.numerator)//p.denominator)
    return dict(result, decision="reject_fixed_null" if p <= ALPHA else "not_rejected",
                p_upper_millionths=upper, scope="conditional_on_declared_sampling_and_device_contract")


def unique(keys):
    obj = dict(keys)
    if len(obj) != len(keys):
        raise ValueError("duplicate JSON field")
    return obj


def main():
    try:
        raw = sys.stdin.buffer.read(16385)
        if len(raw) > 16384:
            raise ValueError("input too large")
        result = check(json.loads(raw, object_pairs_hook=unique))
    except (ValueError, RecursionError) as exc:
        print(json.dumps({"error": str(exc)}))
        return 2
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
