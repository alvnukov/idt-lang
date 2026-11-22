"""Finite cube preparation by strict cyclic ballot survival.

Sample the full cube uniformly. With preparation setting n and sampled word
v, scan the increment tape x_i = n_i v_i from a uniform indexed cyclic origin.
Reject at the first nonpositive prefix sum; otherwise herald and keep v, not
the scanned rotation. Only then pick an analyzer m and read whether m.v > 0.

Cycle-lemma argument for unit increments: if s = sum(x) <= 0, the full prefix
rejects. Otherwise extend the tape periodically in both directions and let
S_j be its integer cumulative sum (S_{j+d} = S_j + s). Every integer level
h has a last visit t(h); all following sums exceed h, by unit steps and
positive drift. An origin r with all d future prefixes positive is exactly
such a last visit (the next periods have positive additional drift). Since
t(h+s) = t(h)+d, reducing last visits modulo d gives exactly s indexed
origins, even for words with repeated rotations. Thus the herald count at a
fixed v is max(n.v, 0), without testing the terminal score in advance.
For odd d, summing those counts by the number j of positive increments uses
(2j-d) C(d,j) = d [C(d-1,j-1) - C(d-1,j)] for j > d/2. Division of the
telescoping sum by d * 2**d gives the full-cube herald yield.

For odd d, v -> -v pairs opposite analyzer signs and gives
E[(n.v)_+ sign(m.v)] = E[(n.v) sign(m.v)]/2 under the uniform cube. Sign
flips and coordinate symmetry give E[v_i sign(m.v)] = m_i E[|m.v|]/d.
Dividing by E[(n.v)_+] = E[|m.v|]/2 yields the affine-dot response.

The replay counts finite trial histories exactly. Fair bits, an indexed
origin, strict killing, the finite horizon and terminal sign readout are
supplied rules. This is not iteration of native T, a stationary or
long-survival distribution, a continuous measurement model, or a Born proof.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import comb

Word = tuple[int, ...]


def check(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def cube(dimension: int) -> tuple[Word, ...]:
    return tuple(product((-1, 1), repeat=dimension))


def compare(left: Word, right: Word) -> Word:
    return tuple(a * b for a, b in zip(left, right, strict=True))


def dot(left: Word, right: Word) -> int:
    return sum(a * b for a, b in zip(left, right, strict=True))


def survives(tape: Word, origin: int, *, strict: bool) -> bool:
    running = 0
    for index in range(len(tape)):
        running += tape[(origin + index) % len(tape)]
        if running < 0 or (strict and running == 0):
            return False
    return True


@dataclass(frozen=True)
class Trials:
    heralds_by_word: dict[Word, int]
    rejected: int
    total: int

    @property
    def heralds(self) -> int:
        return self.total - self.rejected

    def readout(self, analyzer: Word) -> tuple[int, int]:
        """Keep both outcomes on the same heralded sample, never reselect it."""
        positive = nonpositive = 0
        for word, count in self.heralds_by_word.items():
            if dot(analyzer, word) > 0:
                positive += count
            else:
                nonpositive += count
        return positive, nonpositive


def prepare(normal: Word, *, strict: bool = True, fixed_origin: bool = False) -> Trials:
    origins = range(1 if fixed_origin else len(normal))
    counts: dict[Word, int] = {}
    rejected = 0
    for word in cube(len(normal)):
        tape = compare(normal, word)
        for origin in origins:
            if survives(tape, origin, strict=strict):
                counts[word] = counts.get(word, 0) + 1
            else:
                rejected += 1
    return Trials(counts, rejected, len(origins) * 2 ** len(normal))


def rotate_after_herald(normal: Word) -> Trials:
    """Fix origin 0; move the uniform cyclic draw to the accepted output.

    Rotate the accepted *comparison* tape, then undo the preparation signs
    at the destination coordinates. The d formal copies of each rejection
    share the same rejected outcome; no rotation is needed on those trials.
    """
    dimension = len(normal)
    counts: dict[Word, int] = {}
    rejected = 0
    for word in cube(dimension):
        tape = compare(normal, word)
        if not survives(tape, 0, strict=True):
            rejected += dimension
            continue
        for shift in range(dimension):
            rotated = tape[shift:] + tape[:shift]
            output = compare(normal, rotated)
            counts[output] = counts.get(output, 0) + 1
    return Trials(counts, rejected, dimension * 2**dimension)


def check_preparation(normal: Word, trials: Trials) -> None:
    """Compare scanned histories to the formula only after recording them."""
    words = cube(len(normal))
    for word in words:
        check(
            trials.heralds_by_word.get(word, 0) == max(dot(normal, word), 0),
            f"wrong per-word number of indexed origins: {normal=}, {word=}",
        )
    check(
        trials.rejected + sum(trials.heralds_by_word.values()) == trials.total,
        "herald and rejection counts do not cover the full trial space",
    )


def check_responses(dimension: int, *, all_normals: bool) -> None:
    check(dimension % 2 == 1, "the sign-response check requires odd d")
    words = cube(dimension)
    normals = words if all_normals else ((1,) * dimension,)
    expected_yield = Fraction(comb(dimension - 1, (dimension - 1) // 2), 2**dimension)
    for normal in normals:
        trials = prepare(normal)
        check_preparation(normal, trials)
        check(
            Fraction(trials.heralds, trials.total) == expected_yield,
            "wrong acceptance cost from the uniform full cube",
        )
        for analyzer in words:
            positive, negative = trials.readout(analyzer)
            check(
                positive + negative == trials.heralds
                and positive + negative + trials.rejected == trials.total,
                "analyzer changed the herald/reject partition or lost trials",
            )
            expected = Fraction(dimension + dot(normal, analyzer), 2 * dimension)
            check(
                Fraction(positive, trials.heralds) == expected,
                f"wrong response: {normal=}, {analyzer=}",
            )
    print(
        f"d={dimension}: {len(normals) * len(words)} exact setting pairs; "
        f"full-cube herald yield={expected_yield}"
    )


def check_orbit(dimension: int) -> None:
    normal = tuple(-1 if index % 2 else 1 for index in range(dimension))
    analyzer = (1,) * dimension
    trials = prepare(normal)
    transposition = (1, 0, *range(2, dimension))
    mirrors = tuple(
        -1 if index in (0, dimension - 1) else 1 for index in range(dimension)
    )

    def permute(word: Word) -> Word:
        return tuple(word[index] for index in transposition)

    def mirror(word: Word) -> Word:
        return compare(mirrors, word)

    for transform in (permute, mirror):
        transformed = prepare(transform(normal))
        check(
            transformed
            == Trials(
                {
                    transform(word): count
                    for word, count in trials.heralds_by_word.items()
                },
                trials.rejected,
                trials.total,
            ),
            "herald counts are not covariant under a mirror or permutation",
        )
        check(
            transformed.readout(transform(analyzer)) == trials.readout(analyzer),
            "jointly transformed analyzer changed the conditional response",
        )
    for variant in (normal, permute(normal), mirror(normal)):
        check(
            rotate_after_herald(variant) == prepare(variant),
            "fixed origin then covariant output rotation is not equivalent",
        )


def check_controls() -> None:
    normal = (1, 1, 1)
    first_flip, last_flip = (-1, 1, 1), (1, 1, -1)
    fixed = prepare(normal, fixed_origin=True)
    cyclic = prepare(normal)
    first = Fraction(fixed.readout(first_flip)[0], fixed.heralds)
    last = Fraction(fixed.readout(last_flip)[0], fixed.heralds)
    check(
        (first, last) == (Fraction(1, 2), Fraction(1)),
        "fixed origin without output rotation should have coordinate bias",
    )
    check(
        Fraction(fixed.heralds, fixed.total) == Fraction(cyclic.heralds, cyclic.total),
        "the fixed-origin defect should affect the output, not the herald yield",
    )
    loose = prepare(normal, strict=False)
    loose_response = Fraction(loose.readout(first_flip)[0], loose.heralds)
    check(loose_response == Fraction(5, 9), "non-strict rule changed unexpectedly")
    check(
        not survives((1, -1, 1), 0, strict=True)
        and survives((1, -1, 1), 0, strict=False),
        "non-strict rule should allow an intermediate zero prefix",
    )
    check(
        prepare((1, 1)).heralds_by_word.get((1, -1), 0) == 0
        and prepare((1, 1), strict=False).heralds_by_word.get((1, -1), 0) == 1,
        "non-strict rule should admit an even-dimensional zero-score bridge",
    )
    print(
        f"controls: fixed origin gives {first} vs {last}; non-strict gives {loose_response}"
    )


def main() -> None:
    for dimension in (3, 5, 7, 9):
        check_responses(dimension, all_normals=dimension <= 5)
    for dimension in (2, 4, 6, 8):
        normal = (1,) * dimension
        check_preparation(normal, prepare(normal))
    for dimension in (3, 5):
        check_orbit(dimension)
    check_controls()
    print("even d=2,4,6,8: strict count including ties; no affine response claim")
    print(
        "mirror/permutation covariance and covariant post-herald rotation: exact at d=3,5"
    )
    print(
        "finite supplied protocol; no native T, continuous settings, or Born derivation"
    )


if __name__ == "__main__":
    main()
