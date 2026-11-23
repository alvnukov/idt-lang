"""Forward-dark port intervention and data-only rerouting between frozen ABA blocks.

Run: python3 -m scripts.probe_dark_intermediate_port [--json]
All native rows are exhaustive finite counts, never experimental data. Reading
the middle of a stored microhistory inserts no detector or collapse into it.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
import json

from scripts import probe_three_port_dark_bounds as echo
from scripts import probe_vacuum_compensated_network as net
from scripts.probe_eight_label_interferometer import check


PORTS = range(3)
SETTINGS = ("off", "A", "B", "C", "cycle")
# Cell layout D,E,Z,scratch per port. A->B->C->A, using A's existing
# scratch=1: move C out, then B->C, A->B, scratch->A. No E contact.
CYCLE_WORD = (((8, 3),), ((4, 8),), ((0, 4),), ((3, 0),))


def history(source, stock, setting):
    """Launch, cut before intervention, cut after intervention, and exit."""
    check(type(source) is int and source in PORTS and len(stock) == 3
          and all(type(v) is int and v in net.SHADES for v in stock)
          and setting in SETTINGS, "unsupported launch or intervention")
    initial = tuple(v for i, e in enumerate(stock) for v in (3 if i == source else 1, e, 0, 1))
    block = echo._physical_word()
    replay = net.mobile._replay  # checks conservation after each individual contact
    middle = replay(initial, block).output
    wanted = list(middle)  # independent endpoint check; never input to replay
    if setting == "off":
        word = ()
    elif setting == "cycle":
        word = CYCLE_WORD
        wanted[0::4] = (middle[8], middle[0], middle[4])
    else:
        i = 4 * "ABC".index(setting)
        word = (((i+2, i+1),),)  # one real B(Z,E) with Z=0 at this cut
        wanted[i+1] = 3-middle[i+1]
    intervention = replay(middle, word)
    after = intervention.output
    check(after == tuple(wanted), "intervention changed untargeted stock or failed transport")
    final = replay(after, block).output
    for cut in (initial, middle, after, final):
        echo._raw_port(cut)  # all 12 cells, including auxiliaries, not just D
        check(all(v in net.SHADES for v in cut[1::4]), "cut controller outside shade code")
    check(middle[1::4] == tuple(stock) and final[1::4] == after[1::4], "block changed cut stock")
    check(setting != "off" or final == initial, "unplated raw echo not restored")
    return initial, middle, after, final


def native_census():
    middle = [[0]*3 for _ in PORTS]
    exits = {s: [[0]*3 for _ in PORTS] for s in SETTINGS}
    for source, stock in product(PORTS, product(net.SHADES, repeat=3)):
        common = None
        for s in SETTINGS:
            _, cut, _, final = history(source, stock, s)
            if common is None:
                common = cut
                middle[source][echo._raw_port(cut)] += 1
            check(common == cut, "launch condition depends on later setting")
            exits[s][source][echo._raw_port(final)] += 1
    return tuple(map(tuple, middle)), {s: tuple(map(tuple, t)) for s, t in exits.items()}


def cycle_controls():
    """Independent named models; transparent port routing is supplied."""
    permuted = [[0]*3 for _ in PORTS]
    for w, g in ((4, (0, 1, 2)), (2, (2, 1, 0)), (2, (0, 2, 1))):
        for i in PORTS:
            permuted[i][g[(g[i]+1) % 3]] += w
    # U P U with U a fixed real balanced Hadamard on AC or BC (fair
    # launch choice), identity on the spectator. Under this particular P
    # each (source,exit) has at most one nonzero amplitude path: signs
    # cannot interfere, so square path magnitudes exactly, without floats.
    coherent = [[F(0)]*3 for _ in PORTS]
    for pair in ((0, 2), (1, 2)):
        def h_squared(i, j):
            return F(1, 2) if i in pair and j in pair else F(i == j and i not in pair)
        for i, j in product(PORTS, repeat=2):
            paths = [h_squared(i, k)*h_squared((k+1) % 3, j) for k in PORTS]
            check(sum(x != 0 for x in paths) <= 1, "coherent path cross term neglected")
            coherent[i][j] += F(1, 2)*sum(paths)
    check(all((8*x).denominator == 1 for row in coherent for x in row), "nonintegral count")
    return {"fixed_permutation": tuple(map(tuple, permuted)),
            "fixed_coherent": tuple(tuple(int(8*x) for x in row) for row in coherent)}


@dataclass(frozen=True)
class Scope:
    same_preparation_at_cut: bool | None = None
    forward_q_bounds_full_active_weight: bool | None = None
    relative_unitary_identity_on_complement: bool | None = None
    common_subsequent_channel_and_event: bool | None = None
    all_launches_no_postselection: bool | None = None


def interval_verdict(intervals, scope, model="supported_unitary", *, q_lower_certified=False):
    """Conditional compatibility certificate, including mixed inputs/ancillas.

    P is the full active subspace, q=<P> before intervention. Compare OFF
    with a relative unitary V fixing its orthogonal complement pointwise;
    absorb the common evolution into the exit effect 0<=M<=I. On a
    purification psi (extend P,V,M by identity where necessary),
    ||sqrt(M)V psi|| <= ||sqrt(M)psi|| + ||(V-I)P psi|| <= sqrt(r)+2sqrt(q).
    This is a bound on unconditional event probabilities, not a weak value.

    For V=I-2P and r=0, sqrt(M)psi=0. Subtract the component of V psi
    along psi to get s<=1-|<psi,V psi>|²=4q(1-q). Attainable at every
    q: psi=(sqrt(1-q),sqrt(q)), P projects onto coordinate two, M onto
    the orthogonal complement of psi. Not valid by substituting small r for zero.
    By default only the upper endpoint of the q reading is certified to bound
    the active weight. Do not use the lower endpoint of an upper-bounding
    tracer as a lower bound on <P>. Opt in only for a certified two-sided
    interval for the actual full active weight.
    """
    def verdict(reason, exclude=False):
        return {"excluded": exclude, "reason": reason}

    if (not isinstance(scope, Scope) or not all(v is True for v in vars(scope).values())
            or type(q_lower_certified) is not bool
            or model not in ("supported_unitary", "scalar_pi")):
        return verdict("inconclusive: comparator scope not established")
    if not isinstance(intervals, dict) or set(intervals) != {"q", "r", "s"}:
        return verdict("inconclusive: simultaneous bounds on q, r and s required")
    for v in intervals.values():
        if (not isinstance(v, (list, tuple)) or len(v) != 2
                or not all(type(x) in (int, F) and 0 <= x <= 1 for x in v) or v[0] > v[1]):
            return verdict("inconclusive: invalid exact probability interval")
    q0, q1 = intervals["q"]
    r, s = intervals["r"][1], intervals["s"][0]
    excess = s-r-4*q1
    if excess > 0 and excess**2 > 16*r*q1:
        return verdict("violates supported-unitary triangle bound", True)
    if model == "scalar_pi" and r == 0:
        peak = min(q1, max(q0 if q_lower_certified else 0, F(1, 2)))
        if s > 4*peak*(1-peak):
            return verdict("violates scalar-pi exact-dark bound", True)
    return verdict("inconclusive: necessary bound not violated")


def verify():
    middle, exits = native_census()
    controls = cycle_controls()
    check(middle == ((6, 0, 2), (0, 6, 2), (2, 2, 4)), "forward cut population")
    check(exits["off"] == ((8, 0, 0), (0, 8, 0), (0, 0, 8)), "echo")
    check(exits["A"] == ((4, 2, 2), (2, 4, 2), (2, 2, 4)), "A controller")
    check(exits["B"] == exits["C"] == ((4, 0, 4), (0, 4, 4), (4, 4, 0)), "held-out controllers")
    check(exits["cycle"] == controls["fixed_permutation"] == ((0, 4, 4), (4, 0, 4), (4, 4, 0)),
          "native cycle or fixed-permutation alias")
    check(controls["fixed_coherent"] == ((1, 4, 3), (4, 1, 3), (3, 3, 2)), "named coherent cycle")
    scope = Scope(True, True, True, True, True)  # IF the common operational identification is supplied
    b_events = {}
    for name, ports in (("A_exit", (0,)), ("non_B_exit", (0, 2))):
        q = F(middle[1][0], 8)
        r, s = (F(sum(exits[k][1][j] for j in ports), 8) for k in ("off", "A"))
        values = {"q": q, "r": r, "s": s}
        check(interval_verdict({k: (x, x) for k, x in values.items()}, scope)["excluded"],
              "conditional forward-dark discriminator missing")
        b_events[name] = {k: str(x) for k, x in values.items()}
    # A simultaneous uncertainty box, not measured counts or an inferred
    # confidence interval. Choose root bounds rationally for an exact example.
    root_q = root_r = F(1, 8)
    s_lower = F(1, 4)
    demo = interval_verdict({"q": (0, root_q**2), "r": (0, root_r**2),
                             "s": (s_lower, 1)}, scope)
    return {
        "middle_over_8": middle, "exit_over_8": exits, "cycle_comparator_over_8": controls,
        "B_launch": b_events,
        "hypothetical_simultaneous_bounds": {
            "q_upper": str(root_q**2), "r_upper": str(root_r**2), "s_lower": str(s_lower),
            "allowed_s_upper": str((root_r+2*root_q)**2), "excluded_under_scope": demo["excluded"]},
        "comparator_bound": "sqrt(s) <= sqrt(r) + 2 sqrt(q), also for mixed inputs/ancillas. "
                            "If OFF is exactly event-dark and the relative operation is I-2P, "
                            "s <= 4q(1-q), sharp at each actual q.",
        "scope": "Finite classical histories, eight equally weighted stocks per source; no empirical data. "
                 "Rows are sources; columns detected ports. q is forward cut population over all launches.",
        "boundary": "The native plate flips E even on a token-empty port. A programmed controller change "
                    "is not a pure path phase. Exclusion requires the measured q to bound the entire active "
                    "subspace, a common cut preparation, supported unitary without cross-talk, common "
                    "subsequent evolution/detection and no postselection; these are not derived. "
                    "Data-only transparent rerouting distinguishes the named coherent device, not all "
                    "coherent models; the frozen permutation mixture still aliases the native cycle."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = verify()
    print(json.dumps(report, indent=2) if args.json else
          f"B launch: {report['B_launch']}. {report['boundary']}")
