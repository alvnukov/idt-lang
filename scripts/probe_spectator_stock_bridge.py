"""A conditional bridge from terminal odds to a common stock gain.

Use stable, exclusive terminal alternatives, not a coherent shutter.
For a fixed terminal field, assume positive pair odds are unchanged by
passive menu changes. In a simultaneous positive triple the three odds
around the triangle multiply to one. Comparing with one positive reference
then gives w_i = P(i)/P(ref), up to a common scale; normalization gives
P(i)=w_i/sum_j w_j. A supported menu can include an alternative with exact
zero probability in the model; we give it zero weight and do not
form odds with a dark denominator. An all-dark menu is not normalized.

To transfer the same weights between trials, also require odds against a
common reference to depend only on the specified local terminal stocks:
menu consistency by itself does not imply that cross-trial separability.
Use unchanged calibration for each named detector and no postselection
that changes relative event weights. Write A,A' for the sum of the two
active weights, and R,R'>0 for the isolated reference before and after its
raw coordinates double (the reference weight ratio is not given). If its probabilities agree before/after the
native mixer on the active pair, then

   R/(A+R) = R'/(A'+R')  <=>  R A' = R' A.

For one fixed surviving reference, the common gain is h=R'/R for every
active input covered by the comparison, including A=0 (then A'=0).
No functional form for the reference or the active weights is used in
the identity. A numeric h requires a calibrated reference ratio or an
additional law. A finite set of menus, stocks and words tests only that set;
the universal gain premise needs universal evidence or an additional law.

Reference drift that depends on the active field can forge spectator
equality even while each menu family passes. Multiplying all weights by a
common trial factor leaves every probability unchanged, so observations
cannot fix absolute stock. The bridge assumes stable local representatives
of normalized data; it does not identify a unique hidden representation.
"""

from collections.abc import Callable
from fractions import Fraction as F
from itertools import product
from math import prod

Gaussian = tuple[int, int]
Pair = tuple[Gaussian, Gaussian]
Menu = tuple[str, ...]
Menus = dict[Menu, tuple[F, ...]]
Law = Callable[[Gaussian], F]
ZERO: Gaussian = (0, 0)
ONE: Gaussian = (1, 0)


def check(condition: bool, message: str) -> None:
    """Keep checks active under python -O."""
    if not condition:
        raise AssertionError(message)


def normalize(weights: tuple[F, ...]) -> tuple[F, ...]:
    total = sum(weights, F(0))
    check(total > 0 and all(x >= 0 for x in weights), "supported menu only")
    return tuple(w / total for w in weights)


def reconstruct(menus: Menus, reference: str) -> dict[str, F]:
    """Use binary observations against the reference, then verify all menus."""
    weights = {reference: F(1)}
    for labels, frequencies in menus.items():
        if len(labels) != 2 or reference not in labels:
            continue
        i = labels.index(reference)
        check(frequencies[i] > 0, "reference must be positive in the binary menu")
        weights[labels[1 - i]] = frequencies[1 - i] / frequencies[i]
    for labels, frequencies in menus.items():
        check(
            normalize(tuple(weights[p] for p in labels)) == frequencies,
            "odds and dark alternatives must agree with the simultaneous menu",
        )
    return weights


def check_menus() -> int:
    menus: Menus = {
        ("r", "a"): (F(2, 5), F(3, 5)),
        ("r", "b"): (F(2, 7), F(5, 7)),
        ("r", "d"): (F(1), F(0)),
        ("a", "b"): (F(3, 8), F(5, 8)),
        ("r", "a", "b"): (F(1, 5), F(3, 10), F(1, 2)),
        ("r", "a", "b", "d"): (F(1, 5), F(3, 10), F(1, 2), F(0)),
    }
    check(
        reconstruct(menus, "r") == {"r": F(1), "a": F(3, 2), "b": F(5, 2), "d": F(0)},
        "reconstruct anchored weights from observations",
    )

    # Separate binary trials can each be normalized but disagree as a cycle:
    # A:B=2, B:C=2, C:A=2. Any one simultaneous triple has product one.
    binary_observations = ((F(2, 3), F(1, 3)),) * 3
    check(prod(a / b for a, b in binary_observations) == 8, "inconsistent binary cycle")
    a, b, c = normalize((F(4), F(2), F(1)))
    check((a / b, b / c, c / a) == (F(2), F(2), F(1, 4)), "joint triple control")
    return len(menus)


def mixer(x: Gaussian, y: Gaussian) -> Pair:
    """Integer numerators of T with the common per-layer divisor two."""
    a, b = x
    c, d = y
    return (a - b + c + d, a + b - c + d), (a + b + c - d, -a + b + c + d)


def q(x: Gaussian) -> F:
    a, b = x
    return F(a * a + b * b)


def l1(x: Gaussian) -> F:
    a, b = x
    return F(abs(a) + abs(b))


def active_mass(values: Pair, weigh: Law) -> F:
    return sum(map(weigh, values), F(0))


def spectator(active: F, reference: F) -> F:
    return normalize((active, reference))[1]


def check_reference() -> int:
    s, twice = (1, 2), (2, 4)
    r, r_next = q(s), q(twice)  # chosen local law for the control, not a premise
    check(r > 0 and r_next > 0, "surviving reference")
    h = r_next / r
    inputs = (ZERO, ONE, (0, 1), (-1, 1), (2, -3))
    for x, y in product(inputs, repeat=2):
        active = active_mass((x, y), q)
        changed = active_mass(mixer(x, y), q)
        p, p_next = spectator(active, r), spectator(changed, r_next)
        check((p == p_next) == (changed == h * active), "reference iff common gain")
        check(p == p_next, "exact fixture, including dark active pair")
    check(
        spectator(F(0), r) == 1 and spectator(F(1), r_next) < 1, "dark creation visible"
    )

    drifts = set()
    for inputs_pair in ((ONE, ZERO), (ONE, ONE)):
        active = active_mass(inputs_pair, l1)
        changed = active_mass(mixer(*inputs_pair), l1)
        ratio = changed / active
        drifts.add(ratio)
        check(spectator(active, F(0)) == spectator(changed, F(0)) == 0, "dark vacuity")
        check(spectator(active, F(1)) == spectator(changed, ratio), "reference drift")
        # The drifting reference still makes each trial a consistent menu
        # family; fixed reference calibration across fields is what it lacks.
        weights = (*map(l1, mixer(*inputs_pair)), ratio)
        u, v, w = normalize(weights)
        p, p_ref = normalize((weights[0], weights[2]))
        check(u / w == p / p_ref and v > 0, "local menu checks do not expose drift")
    check(drifts == {F(2), F(4)}, "no common gain in the drift control")

    before = (F(3), F(5), F(2))
    after = (F(8), F(24), F(8))
    scaled = tuple(F(3) * w for w in after)
    check(
        spectator(sum(before[:2], F(0)), before[-1]) == normalize(after)[-1],
        "matched reference in stable representatives",
    )
    check(normalize(after) == normalize(scaled), "global trial factor invisible")
    check(
        sum(after[:2]) / sum(before[:2]) != sum(scaled[:2]) / sum(before[:2]),
        "absolute active gain not identified from normalized observations",
    )
    return len(inputs) ** 2


def check_odds_identity() -> int:
    # Nothing in this check is evaluated as a function of a field amplitude.
    reference_weights = (F(1, 3), F(2), F(5, 4))
    active_weights = (F(0), F(1, 5), F(4))
    tested = 0
    for r, r_next, active in product(
        reference_weights, reference_weights, active_weights
    ):
        expected = active * r_next / r
        for changed in (expected, expected + F(1, 7)):
            check(
                (spectator(active, r) == spectator(changed, r_next))
                == (r * changed == r_next * active),
                "exact odds equivalence for arbitrary rational weights",
            )
            tested += 1
    return tested


def check_shutter_and_selection() -> None:
    split = mixer(ONE, ZERO)
    retained, blocked = split[0], ZERO
    closed_chain, shutter_chain = split, (retained, blocked)
    for _ in range(3):  # T^3 is the inverse of T; four layers total.
        closed_chain = mixer(*closed_chain)
        shutter_chain = mixer(*shutter_chain)
    check(closed_chain == ((16, 0), ZERO), "coherent return")
    observed = tuple(q(v) / 16**2 for v in shutter_chain)
    check(observed == (F(1, 4), F(1, 4)), "physical shutter changes the coherent state")
    check(1 - sum(observed) == F(1, 2), "account for shutter rejection")
    check(normalize(observed) == (F(1, 2), F(1, 2)), "postselected shutter result")
    base = normalize((F(1), F(1), F(1)))
    selected = normalize((F(1), F(1, 2), F(1)))
    check(
        base[0] / base[1] == 1 and selected[0] / selected[1] == 2,
        "outcome-dependent selection changes odds",
    )


def gain_interval(p: F, eps: F, h: F) -> tuple[F, F]:
    """Given exact p and |p'-p|<=eps with interior bounds and known ref gain."""
    lo, hi = p - eps, p + eps
    check(0 < lo <= hi < 1 and h > 0, "non-dark, non-vacuous interval only")
    factor = h * p / (1 - p)
    return factor * (1 - hi) / hi, factor * (1 - lo) / lo


def check_interval() -> tuple[F, F]:
    p, eps, h = F(1, 3), F(1, 30), F(4)
    bounds = gain_interval(p, eps, h)
    check(bounds == (F(38, 11), F(14, 3)), "exact approximate-gain interval")
    # Construct A=2, R=1 and R'=4. Each endpoint is attained by
    # choosing A' to put the spectator exactly at one error boundary.
    for r, p_next in zip(bounds, (p + eps, p - eps), strict=True):
        check(spectator(2 * r, h) == p_next, "endpoint witness")
    # When p=1 the ratio A'/A is undefined; created active weight is bounded.
    r_next = F(4)
    creation_bound = r_next * eps / (1 - eps)
    check(spectator(creation_bound, r_next) == 1 - eps, "dark creation bound")
    return bounds


def main() -> None:
    menus = check_menus()
    odds_cases = check_odds_identity()
    trials = check_reference()
    check_shutter_and_selection()
    lo, hi = check_interval()
    print(
        f"{menus} consistent passive menus; cyclic binary odds fail a simultaneous triple."
    )
    print(
        f"{odds_cases} exact odds comparisons with no amplitude-to-weight rule assumed."
    )
    print(
        f"{trials} stable-reference fixtures: exact common gain 4, including active dark."
    )
    print(
        "Dark reference is vacuous; drift forges gains 2 and 4; global trial scale is invisible."
    )
    print("Shutter and outcome-dependent postselection are not passive menu changes.")
    print(f"Approximate reference example bounds active gain to [{lo}, {hi}].")
    print("Conditional normalized bridge only; no universal detector law inferred.")


if __name__ == "__main__":
    main()
