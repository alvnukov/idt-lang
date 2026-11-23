"""Exact loss and memory controls for a late-choice two-arm parity game.

The null is a route mixture fixed independently of the current settings:
P(o|x,y) = a_o(x) + b_o(y). Each arm has constant total mass across its
settings. Losses must be local to the arm in use; a downstream filter that
knows both settings is not in the null. This is a finite channel check, not
an experimental fit or a test of amplitudes against positive two-arm models.
When the current setting pair is independent of all past settings, one may
condition on detector history without giving it either current setting.

For additive single-click rates C_xy = A_x + B_y, each component A_x makes
at least A_x / max_y C_xy of an error in the *sum* of the two conditional
failure rates for its row: whichever output it chooses, it is wrong in one
column. The same argument applies to B_y down its column. The terms for
max(A), max(B) sum to one. At least one other term is positive if every
cell has C_xy > 0, so the sum of failure rates is strictly greater than one.
Weighting by positive q_xy gives a failure rate strictly larger than min(q).
The family sharp_loss_model(t) approaches equality at the selected corner.
"""

import json
from collections.abc import Iterator, Mapping
from dataclasses import asdict, dataclass
from decimal import Decimal
from fractions import Fraction
from itertools import product

Setting = tuple[int, int]
CELLS: tuple[Setting, ...] = ((0, 0), (0, 1), (1, 0), (1, 1))
UNIFORM = dict.fromkeys(CELLS, Fraction(1, 4))
ZERO = Fraction(0)
HALF = Fraction(1, 2)
ONE = Fraction(1)


@dataclass(frozen=True)
class OutcomeMass:
    """Exact masses in order: left only, right only, none, double."""

    left: Fraction
    right: Fraction
    none: Fraction
    double: Fraction

    def __post_init__(self) -> None:
        if any(not isinstance(p, Fraction) or p < 0 for p in self.parts):
            raise ValueError("outcome masses must be nonnegative Fractions")

    @property
    def parts(self) -> tuple[Fraction, Fraction, Fraction, Fraction]:
        return self.left, self.right, self.none, self.double

    @property
    def total(self) -> Fraction:
        return self.left + self.right + self.none + self.double

    @property
    def single_click(self) -> Fraction:
        return self.left + self.right

    def __add__(self, other: "OutcomeMass") -> "OutcomeMass":
        return OutcomeMass(
            self.left + other.left,
            self.right + other.right,
            self.none + other.none,
            self.double + other.double,
        )


@dataclass(frozen=True)
class RawCell:
    """Counts prior to any single-click selection; None means unrecorded."""

    triggers: int | None
    left: int
    right: int
    none: int | None
    double: int | None

    def __post_init__(self) -> None:
        counts = (self.left, self.right, self.none, self.double)
        values = (*counts, self.triggers)
        if any(
            value is not None and (type(value) is not int or value < 0)
            for value in values
        ):
            raise ValueError("counts must be nonnegative integers")
        if self.triggers is not None:
            observed = sum(value for value in counts if value is not None)
            if observed > self.triggers or (
                None not in counts and observed != self.triggers
            ):
                raise ValueError("outcomes must account for all triggers")

    def probabilities(self) -> OutcomeMass | None:
        if not self.triggers or self.none is None or self.double is None:
            return None
        return OutcomeMass(
            Fraction(self.left, self.triggers),
            Fraction(self.right, self.triggers),
            Fraction(self.none, self.triggers),
            Fraction(self.double, self.triggers),
        )


@dataclass(frozen=True)
class Scores:
    raw_contrast: Fraction | None
    pooled_success: Fraction | None
    stratified_success: Fraction | None


@dataclass(frozen=True)
class CountScores:
    scores: Scores
    per_trigger_status: str
    observed_pooled_success: Fraction | None


Arm = tuple[OutcomeMass, OutcomeMass]
ProbTable = dict[Setting, OutcomeMass]
CountTable = dict[Setting, RawCell]


def additive_model(left: Arm, right: Arm) -> ProbTable:
    """Combine two arms holding subdistributions with a fixed path share."""
    if (
        left[0].total != left[1].total
        or right[0].total != right[1].total
        or left[0].total + right[0].total != ONE
    ):
        raise ValueError("arm masses must represent a fixed, normalized path mixture")
    return {(x, y): left[x] + right[y] for x, y in CELLS}


def positive_weights(
    weights: Mapping[Setting, Fraction] | None,
) -> Mapping[Setting, Fraction]:
    q = UNIFORM if weights is None else weights
    if set(q) != set(CELLS) or any(
        not isinstance(w, Fraction) or w <= 0 for w in q.values()
    ):
        raise ValueError("all four setting weights must be positive Fractions")
    if sum(q.values()) != ONE:
        raise ValueError("setting weights must normalize to one")
    return q


def score_probabilities(
    table: Mapping[Setting, OutcomeMass],
    weights: Mapping[Setting, Fraction] | None = None,
) -> Scores:
    """Contrast always uses uniform signs; click-only aggregations use q."""
    if set(table) != set(CELLS) or any(row.total != ONE for row in table.values()):
        raise ValueError("all four outcome distributions must normalize to one")
    q = positive_weights(weights)
    click = {cell: table[cell].single_click for cell in CELLS}
    correct = {
        (x, y): table[x, y].left if x ^ y else table[x, y].right for x, y in CELLS
    }
    contrast = (
        sum(
            (
                (table[x, y].right - table[x, y].left) * (-1 if x ^ y else 1)
                for x, y in CELLS
            ),
            ZERO,
        )
        / 4
    )
    total_click = sum(q[cell] * click[cell] for cell in CELLS)
    pooled = (
        sum(q[cell] * correct[cell] for cell in CELLS) / total_click
        if total_click
        else None
    )
    stratified = (
        sum((q[cell] * correct[cell] / click[cell] for cell in CELLS), ZERO)
        if all(click.values())
        else None
    )
    return Scores(contrast, pooled, stratified)


def score_counts(table: Mapping[Setting, RawCell]) -> CountScores:
    """Return point scores, not a significance decision or a win for a null."""
    probabilities = {
        setting: row
        for setting, counts in table.items()
        if (row := counts.probabilities()) is not None
    }
    if set(probabilities) != set(CELLS) or set(table) != set(CELLS):
        return CountScores(
            Scores(None, None, None), "inconclusive_missing_denominators", None
        )
    scores = score_probabilities(probabilities)
    correct = sum(table[x, y].left if x ^ y else table[x, y].right for x, y in CELLS)
    clicks = sum(row.left + row.right for row in table.values())
    status = (
        "nonzero_raw_contrast_point_score_only"
        if scores.raw_contrast
        else "inconclusive_zero_contrast"
    )
    return CountScores(scores, status, Fraction(correct, clicks) if clicks else None)


def count_table(table: Mapping[Setting, OutcomeMass], triggers: int) -> CountTable:
    """Realize an exact rational control at a common integer herald count."""
    if type(triggers) is not int or triggers <= 0:
        raise ValueError("triggers must be a positive integer")
    counts: CountTable = {}
    for setting, row in table.items():
        left, right, none, double = (p * triggers for p in row.parts)
        if any(p.denominator != 1 for p in (left, right, none, double)):
            raise ValueError(
                "trigger count does not realize the rational table exactly"
            )
        counts[setting] = RawCell(
            triggers, left.numerator, right.numerator, none.numerator, double.numerator
        )
    return counts


def stratified_supremum(weights: Mapping[Setting, Fraction] | None = None) -> Fraction:
    """Strict upper bound when each cell's single-click rate is positive."""
    return ONE - min(positive_weights(weights).values())


def pooled_majority_bound(
    weights: Mapping[Setting, Fraction] | None = None,
) -> Fraction:
    """Sharp bound: best row/column majority, achievable by clicking only there."""
    q = positive_weights(weights)
    slices = (
        (q[0, 0], q[0, 1]),
        (q[1, 0], q[1, 1]),
        (q[0, 0], q[1, 0]),
        (q[0, 1], q[1, 1]),
    )
    return max(max(a, b) / (a + b) for a, b in slices)


def sharp_loss_model(t: Fraction, wrong_corner: Setting = (1, 1)) -> ProbTable:
    """Click t on either low setting, 1/2 on either high setting.

    Both arms give the same port for a given click rate: the parity-correct
    port at low/low, wrong at high/high. At t=0 low/low has no clicks.
    """
    if (
        not isinstance(t, Fraction)
        or not ZERO <= t <= HALF
        or wrong_corner not in CELLS
    ):
        raise ValueError(
            "use an exact rate in [0,1/2] and one of the four wrong corners"
        )
    high_x, high_y = wrong_corner
    low_port_right = high_x == high_y
    low = OutcomeMass(
        ZERO if low_port_right else t, t if low_port_right else ZERO, HALF - t, ZERO
    )
    high = OutcomeMass(
        HALF if low_port_right else ZERO, ZERO if low_port_right else HALF, ZERO, ZERO
    )
    a = (high, low) if high_x == 0 else (low, high)
    b = (high, low) if high_y == 0 else (low, high)
    return additive_model(a, b)


def cross_setting_rejection() -> tuple[CountTable, CountTable]:
    """A both-setting censor can accept just the correct half of fair clicks."""
    full: CountTable = {}
    for x, y in CELLS:
        # Port is initially fair. An independent bit chooses which failed
        # outcome gets reported when the filter (which knows x and y) rejects.
        outcome = [port if port == (x ^ y) else 2 + failure for port, failure in CELLS]
        right, left, none, double = (outcome.count(i) for i in range(4))
        full[x, y] = RawCell(len(outcome), left, right, none, double)
    selected = {
        cell: RawCell(None, row.left, row.right, None, None)
        for cell, row in full.items()
    }
    return full, selected


def joint_reference(*, inverted: bool = False) -> CountTable:
    """Idealized both-input parity readout, not an optical mechanism."""
    table: CountTable = {}
    for x, y in CELLS:
        parity = x ^ y ^ int(inverted)
        table[x, y] = RawCell(1, parity, 1 - parity, 0, 0)
    return table


def memory_shot_success(k: int) -> Fraction:
    """With fixed block settings, unresolved after k iff all k routes agree."""
    if type(k) is not int or k <= 0:
        raise ValueError("shot index must be a positive integer")
    return ONE - Fraction(1, 2**k)


def memory_block_success(n: int) -> Fraction:
    """Mean across N repeated-setting shots, not just the last one."""
    return ONE - memory_shot_success(n) / n


def replay_memory(n: int, *, fresh_settings: bool) -> tuple[CountTable, ...]:
    """Enumerate all equiprobable raw route/guess/setting schedules, N<=4."""
    if type(n) is not int or not 1 <= n <= 4:
        raise ValueError("exact schedule enumeration supports 1 to 4 shots")
    fresh: Iterator[tuple[Setting, ...]] = product(CELLS, repeat=n)
    settings = fresh if fresh_settings else ((cell,) * n for cell in CELLS)
    totals = [{cell: [0, 0] for cell in CELLS} for _ in range(n)]
    for schedule in settings:
        for raw_route_and_guess in product(CELLS, repeat=n):
            known: list[int | None] = [None, None]
            for shot, ((x, y), (route, guess)) in enumerate(
                zip(schedule, raw_route_and_guess)
            ):
                pair = (x, y)
                known[route] = pair[route]
                a, b = known
                parity_guess = a ^ b if a is not None and b is not None else guess
                totals[shot][pair][parity_guess] += 1
    return tuple(
        {
            cell: RawCell(right + left, left, right, 0, 0)
            for cell, (right, left) in shot.items()
        }
        for shot in totals
    )


def count_report(table: CountTable) -> dict[str, object]:
    return {
        **asdict(score_counts(table)),
        "raw_counts": {
            f"{x}{y}": asdict(table[x, y]) for x, y in CELLS if (x, y) in table
        },
    }


def report() -> dict[str, object]:
    observed, postselected = cross_setting_rejection()
    n = 15000
    return {
        "scope": "Exact synthetic controls for a fixed one-arm mixture with local loss; not an experimental fit.",
        "definitions": {
            "correct_port": "right only when x XOR y = 0; left only otherwise",
            "raw_contrast": "W = sum_xy (-1)**(x+y) * (P(right only|xy)-P(left only|xy)) / 4",
            "pooled_success": "Ratio of weighted correct clicks to weighted single clicks; default q uniform.",
            "stratified_success": "Weighted mean of setting-wise click-only success; default q uniform.",
            "observed_pooled_success": "Ratio from observed total counts without setting reweighting.",
        },
        "one_arm_bounds": {
            "raw_contrast": "0 by cancellation, including setting-local loss and double events",
            "uniform_pooled_success_when_defined": HALF,
            "uniform_stratified_supremum": stratified_supremum(),
            "strict_if_all_cells_have_single_clicks": True,
            "positive_weight_stratified_supremum": "1 - min(q_xy)",
            "biased_pooled_upper_bound": "maximum conditional majority over rows and columns",
            "sharp_family_uniform_scores": {
                str(t): score_probabilities(sharp_loss_model(t)).stratified_success
                for t in (Fraction(1, 8), Fraction(1, 20), Fraction(1, 2000))
            },
            "sharp_limit_has_a_zero_click_cell": count_report(
                count_table(sharp_loss_model(ZERO), 2)
            ),
        },
        "uniform_eight_herald_control": count_report(
            count_table(sharp_loss_model(Fraction(1, 8)), 8)
        ),
        "cross_setting_rejection": {
            "outside_null": True,
            "complete": count_report(observed),
            "only_selected_counts": count_report(postselected),
        },
        "ideal_both_input_reference": {
            "correct_parity": count_report(joint_reference()),
            "inverted_parity": count_report(joint_reference(inverted=True)),
        },
        "memory": {
            "assumptions": "One intrinsic iid fair route per shot; receiver retains last input on each arm.",
            "repeated_settings_small_replay": [
                count_report(table) for table in replay_memory(3, fresh_settings=False)
            ],
            "fresh_independent_settings_small_replay": [
                count_report(table) for table in replay_memory(3, fresh_settings=True)
            ],
            "repeated_settings_large_block": {
                "shots": n,
                "last_shot_formula": f"1 - 2**(-{n})",
                "mean_formula": f"1 - (1 - 2**(-{n}))/{n}",
                "mean_approx": f"{Decimal(n - 1) / Decimal(n):.10f}",
                "note": "Symbolic exact formula; no expansion/enumeration of the large block.",
            },
            "fresh_independent_settings_mean": HALF,
        },
        "published_context": {
            "article": "Massa et al., DOI 10.1002/qute.201900050",
            "numbers_are_conditional_registered_output_fractions": True,
            "overlap": "0.961 ± 0.006",
            "delayed": "0.498 ± 0.006",
            "per_trigger_table_available_in_article": False,
            "per_trigger_status": "inconclusive_missing_denominators",
            "no_fit_or_significance_test": True,
        },
        "zero_raw_contrast_is_a_win": False,
    }


def json_exact(value: object) -> object:
    if isinstance(value, Fraction):
        return str(value)
    raise TypeError(f"not a JSON reporting value: {type(value).__name__}")


if __name__ == "__main__":
    print(json.dumps(report(), default=json_exact, sort_keys=True))
