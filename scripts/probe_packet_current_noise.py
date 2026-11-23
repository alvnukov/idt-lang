"""Same one-launch packet readout, different finite-window count fluctuations.

The device is the existing uncolored four-label circuit, replayed from two
occupied D inputs on each launch. The three stationary interlaunch seed laws,
the reset between launches, and the additive number meter are supplied. The
test does not derive a source process, physical current, or quantum noise.
"""

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product

from scripts import probe_colorless_pair_additivity as pair

PROCESSES = ("iid", "frozen", "cycle")


@dataclass(frozen=True)
class Launch:
    seed: tuple[int, int]
    output: pair.State

    @property
    def left_count(self) -> int:
        return sum(self.output[i] == pair.base.TOKEN for i in pair.SITES[:2])

    @property
    def right_count(self) -> int:
        return sum(self.output[i] == pair.base.TOKEN for i in pair.SITES[2:])

    @property
    def left_click(self) -> int:
        return int(self.left_count >= 1)


def seed_outcomes(*, splitter_only: bool = False) -> tuple[Launch, ...]:
    """Replay by labelled seed; an unordered stock would discard time correlations."""
    base = pair.base
    suffix = () if splitter_only else tuple((pair.EDGES[i],) for i in pair.EARLY_WORD)
    return tuple(Launch(seed, base.replay((base.TOKEN, seed[0], 0,
                                         base.TOKEN, seed[1], 0), base.SPLITTER + suffix)[-1])
                 for seed in base.SOURCE_SEEDS)


def independent_balanced_counts() -> tuple[int, ...]:
    """Separate control: two distinguishable particles use independent balanced ports."""
    return tuple(a + b for a, b in product((0, 1), repeat=2))


def moments(counts: Sequence[int]) -> tuple[F, F]:
    if not counts:
        raise ValueError("the launch count support must be nonempty")
    mean = F(sum(counts), len(counts))
    return mean, F(sum(x * x for x in counts), len(counts)) - mean**2


def seed_pairs(process: str, lag: int, size: int) -> tuple[tuple[int, int], ...]:
    """Equally weighted joint seed indices at any two launches separated by lag.

    IID draws a fresh index each period; frozen uses one index for all periods;
    cycle uses one uniform initial phase and advances in the fixed seed order.
    At lag zero even IID samples the same launch twice. Both marginals of each
    joint law are uniform, including at every cycle phase offset.
    """
    if process not in PROCESSES:
        raise ValueError(f"unknown source process: {process!r}")
    if type(lag) is not int or lag < 0 or type(size) is not int or size <= 0:
        raise ValueError("expected a nonnegative integer lag and a positive seed support size")
    indices = range(size)
    if lag == 0 or process == "frozen":
        return tuple((i, i) for i in indices)
    if process == "iid":
        return tuple(product(indices, repeat=2))
    return tuple((i, (i + lag) % size) for i in indices)


def lag_covariance(counts: Sequence[int], process: str, lag: int) -> F:
    pairs = seed_pairs(process, lag, len(counts))
    mean, _ = moments(counts)
    return F(sum(counts[i] * counts[j] for i, j in pairs), len(pairs)) - mean**2


def window_structure_factor(counts: Sequence[int], process: str, length: int,
                            quarter_turns: int) -> F:
    """E[|sum_t (X_t - E X_t) exp(i omega t)|^2]/length, omega=k*pi/2.

    The sampled phases permit exact rational arithmetic. The centering uses the
    ensemble mean, not a mean estimated separately in each window or realization.
    """
    if type(length) is not int or length <= 0:
        raise ValueError("the window length must be a positive integer")
    if type(quarter_turns) is not int or not 0 <= quarter_turns < 4:
        raise ValueError("the frequency must be 0, 1, 2, or 3 quarter turns per launch")
    cosines = (1, 0, -1, 0)
    total = length * lag_covariance(counts, process, 0)
    for lag in range(1, length):
        total += 2 * (length - lag) * cosines[quarter_turns * lag % 4] * lag_covariance(
            counts, process, lag)
    return total / length


def window_variance(counts: Sequence[int], process: str, length: int) -> F:
    return window_structure_factor(counts, process, length, 0) * length


def report() -> str:
    launches = seed_outcomes()
    counts = tuple(row.left_count for row in launches)
    splitter = tuple(row.left_count for row in seed_outcomes(splitter_only=True))
    clicks = tuple(row.left_click for row in launches)
    mean, variance = moments(counts)
    lines = [
        "Finite count-noise control: two old uncolored D inputs, splitter then Z_L,C; no shutters or postselection.",
        "Fair shade seed -> (left,right) additive counts: " + ", ".join(
            f"{row.seed}->({row.left_count},{row.right_count})" for row in launches),
        f"Left count X: mean={mean}, variance={variance}.",
        f"Splitter-only variance={moments(splitter)[1]}; independent balanced-port variance="
        f"{moments(independent_balanced_counts())[1]}.",
        "The device and detector are fixed; reset launches, and supply one of three stationary seed laws.",
        "IID reselection, one shared frozen seed, and uniform-phase deterministic cycling have the same full "
        "one-launch raw output histogram.",
        "Exact Var(sum over M launches): iid=3M/16; frozen=3M^2/16; cycle=r(4-r)/16 with r=M mod 4.",
        "Per-launch-normalized finite-window structure factor: S_M(0)=Var(sum)/M, centered by ensemble mean.",
        "The frozen source has only a between-realization offset, not fluctuations within a frozen run.",
    ]
    for m in (4, 5, 6, 7):
        variances = ", ".join(f"{p}={window_variance(counts, p, m)}" for p in PROCESSES)
        lines.append(f"M={m}: {variances}.")
    lines.extend([
        f"The saturated binary meter X>=1 gives {clicks}; its window variance is zero in all three processes.",
        "A bridge to low-frequency current noise would additionally require a stationary pulse train with a fixed "
        "time base, a number-to-current conversion and detector response, and treatment of thermal noise, "
        "background and loss. Count fluctuations are not physical current noise.",
        "This is not a prediction or rejection of the Bocquillon et al. experiment; no empirical parameter is fitted.",
    ])
    return "\n".join(lines)


if __name__ == "__main__":
    print(report())
