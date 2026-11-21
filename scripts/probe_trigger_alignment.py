"""Test a strict two-of-every-sliding-four rotor against a raw binary click word.

Fix ONE unbroken run, unknown starting phase, no substitutions or false
clicks. Every observed click corresponds to a distinct true arrival in the
same order; unobserved arrivals are arbitrary deletions. If every four
consecutive true arrivals contain exactly two ones, subtracting adjacent
window sums gives x[t+4]=x[t]. Thus the six balanced four-bit patterns
already include all possible start phases. The checker asks for the minimum
number of missed arrivals consistent with this model, not the most likely
alignment. It does not estimate the actual number missed from the retained
word. Extra unobserved arrivals before/after the word cannot lower the cost.

For a fixed pattern choose the earliest possible occurrence of the next
requested bit. Induction: if the greedy previous position is no later than
another match's, that match's next position is also available to greedy.
Hence greedy minimizes the final true-arrival index; minimize over patterns
to allow free start phase. Complexity: O(n) time and constant extra space.

Separately, for an independently fair binary target of growing length, the
phase of the last greedy match performs a finite Markov chain. Each next bit
chooses the first matching position at positive distance. These chains are
irreducible (the immediate successor always has positive probability).
The finite-chain ergodic theorem applied to transition spacings gives the
almost-sure average; initialization contributes only a bounded offset.
Taking a minimum over finitely many rotations does not change each class's
limit. If mean spacing is d, the asymptotic fraction of true arrivals missed
is 1-1/d, NOT d-1 (which is per retained click). These iid reference numbers
are not finite-record bounds and are not a model of actual detector losses.

For context, Luo et al. (2020), https://doi.org/10.1364/OL.396561,
https://arxiv.org/abs/2003.09551, report detector-indexed raw bits from a
continuous source, with dead time and dark counts. No such data, complete
incident-arrival indices, or certified loss budgets are supplied here.
Never pass extracted bits as if they were consecutive unprocessed clicks.

Run: python3 -O -m scripts.probe_trigger_alignment
Or:  python3 -O -m scripts.probe_trigger_alignment 000011 --max-missed 1
"""

import argparse
from fractions import Fraction as F
from itertools import product

ROTORS = ("0011", "0101", "0110", "1001", "1010", "1100")


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError(reason)


def minimum_missed(word: str) -> int:
    """Fewest true arrivals absent from this ordered record, over all rotors."""
    if any(bit not in "01" for bit in word):
        raise ValueError("expected raw binary click labels (only 0 and 1)")

    def cost(rotor: str) -> int:
        cursor = 0
        for bit in word:
            while rotor[cursor % 4] != bit:
                cursor += 1
            cursor += 1
        return cursor - len(word)

    return min(cost(rotor) for rotor in ROTORS)


def compatible(word: str, max_missed: int) -> bool:
    """Compatibility only, for an independently supplied upper bound on losses."""
    if max_missed < 0:
        raise ValueError("negative loss budget")
    return minimum_missed(word) <= max_missed


def exhaustive_check(length: int = 7) -> None:
    """Independent finite oracle: branch on keeping/skipping every true bit."""
    balanced = {
        "".join(bits) for bits in product("01", repeat=4) if bits.count("1") == 2
    }
    need(balanced == set(ROTORS), "six balanced rotations")
    opt = {"": 0}
    for rotor in balanced:
        reachable = {""}
        # An alternating rotor alone realizes every n-bit word by time 2n.
        for size in range(1, 2 * length + 1):
            bit = rotor[(size - 1) % 4]
            reachable |= {w + bit for w in reachable if len(w) < length}
            for w in reachable:
                cost = size - len(w)
                opt[w] = min(cost, opt.get(w, cost))
    for n in range(length + 1):
        for bits in product("01", repeat=n):
            w = "".join(bits)
            needed = opt[w]
            need(minimum_missed(w) == needed, "independent alignment oracle")
            need(compatible(w, needed), "exact budget suffices")
            if needed:
                need(
                    not compatible(w, needed - 1),
                    "strictly smaller budget cannot suffice",
                )
    need(sum(1 for w in opt if len(w) == length and opt[w] == 0) == 6, "no-loss words")


def stationary_spacing(rotor: str, pi: tuple[F, ...]) -> F:
    """Check a stationary distribution from exact transitions and return mean spacing."""
    need(
        rotor in ROTORS and len(pi) == 4 and sum(pi) == 1 and min(pi) > 0, "chain data"
    )
    incoming = [F(0) for _ in range(4)]
    spacing = F(0)
    for start, mass in enumerate(pi):
        for bit in "01":
            d = next(k for k in range(1, 5) if rotor[(start + k) % 4] == bit)
            incoming[(start + d) % 4] += mass / 2
            spacing += mass * d / 2
    need(tuple(incoming) == pi, "stationarity on last-matched phases")
    return spacing


def diagnostics() -> None:
    exhaustive_check()
    # A genuine raw prefix 0011 plus one false detector click after its
    # first zero yields 00011, even when every true arrival was observed.
    need(compatible("0011", 0) and not compatible("00011", 0), "false-click control")
    need(minimum_missed("0000") == 2, "0000 embeds as 00[11]00")
    alternate = stationary_spacing("0101", (F(1, 4),) * 4)
    paired = stationary_spacing("0011", (F(1, 3), F(1, 6), F(1, 3), F(1, 6)))
    need(
        (alternate, paired) == (F(3, 2), F(5, 3)),
        "independent fair target mean spacings",
    )
    fractions = (1 - 1 / alternate, 1 - 1 / paired)
    need(fractions == (F(1, 3), F(2, 5)), "fractions per true arrival")
    print(
        "Checked all 255 binary words of lengths 0..7 against an independent keep/drop oracle."
    )
    print(
        "0000: at least 2 missed true arrivals. A spurious click can invalidate a zero-loss rejection."
    )
    print("IID fair target, almost-sure limiting missed fractions per true arrival:")
    print(
        "  alternating rotor: 1/3; paired rotor: 2/5; best across the six phases/patterns: 1/3."
    )
    print("Those are not finite-record thresholds. No experimental data were ingested.")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Exact missing-arrival budget for a balanced period-four rotor."
    )
    parser.add_argument(
        "word", nargs="?", help="one ordered raw click word, e.g. 001101"
    )
    parser.add_argument(
        "--max-missed",
        type=int,
        default=None,
        help="independent upper bound on omitted true arrivals",
    )
    args = parser.parse_args()
    if args.word is None:
        if args.max_missed is not None:
            parser.error("--max-missed requires a word")
        diagnostics()
        return
    try:
        needed = minimum_missed(args.word)
        print(f"Minimum missed true arrivals: {needed}")
        if args.max_missed is not None:
            result = compatible(args.word, args.max_missed)
            print(
                "Compatible with this budget."
                if result
                else "Excluded under this budget and the stated detector assumptions."
            )
    except ValueError as exc:
        parser.error(str(exc))


if __name__ == "__main__":
    main()
