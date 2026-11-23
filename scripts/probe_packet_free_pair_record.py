"""Read a joint record prepared entirely in vacant cells, with no plate.

Four independent vacant cells A, B, A', B' receive two disjoint contacts.
The choice of pairing is blind to every label; A' and B' are always retired.
Only then is an independent occupied token C introduced. A fixed two-contact
reader on A, B, C reports their occupation bits without postselection.

This is a finite classical test of a joint blank record, not a phase/fringe
test or an internal detector construction. Stock, wiring and readout are supplied.
"""

from collections import Counter
from collections.abc import Callable
from dataclasses import dataclass, replace
from fractions import Fraction
from functools import partial
from itertools import permutations, product

from scripts.probe_eight_label_interferometer import H_VACUUM_XOR, check, coupler, number

Pair = tuple[int, int]
Triple = tuple[int, int, int]
Stock = tuple[int, int, int, int]
F = Fraction


@dataclass(frozen=True)
class Fixture:
    name: str
    labels: tuple[int, ...]
    blank_stock: tuple[int, ...]
    token_stock: tuple[int, ...]
    contact: Callable[[Pair], Pair]
    occupied: Callable[[int], int]
    square_is_swap: bool


def four_label_contact(pair: Pair, *, identity_blank: bool = False) -> Pair:
    if pair in ((3, 1), (1, 3)):
        return pair[::-1]
    if not identity_blank:
        left, right = pair
        if left == 0 and right in (1, 2):
            return 0, 3 - right
        if right == 0 and left in (1, 2):
            return 3 - left, 0
    return pair


EIGHT_LABEL = Fixture("eight_label", tuple(range(8)), (0, 1), (4, 5), coupler, number, True)
EIGHT_LABEL_VACUUM_XOR = replace(
    EIGHT_LABEL, name="eight_label_vacuum_xor", contact=partial(coupler, homogeneous=H_VACUUM_XOR)
)
EIGHT_LABEL_UNIFORM_BLANK = replace(
    EIGHT_LABEL, name="eight_label_uniform_blank", blank_stock=(0, 1, 2, 3)
)
FOUR_LABEL = Fixture(
    "four_label", tuple(range(4)), (0, 1), (3,), four_label_contact, (0, 0, 0, 1).__getitem__, False
)
FOUR_LABEL_IDENTITY_BLANK = replace(
    FOUR_LABEL, name="four_label_identity_blank", contact=partial(four_label_contact, identity_blank=True)
)
FIXTURES = (
    EIGHT_LABEL, EIGHT_LABEL_VACUUM_XOR, EIGHT_LABEL_UNIFORM_BLANK, FOUR_LABEL, FOUR_LABEL_IDENTITY_BLANK
)


def prepare(fixture: Fixture, stock: Stock, *, crossed: bool) -> Pair:
    a, b, a_prime, b_prime = stock
    check(all(label in fixture.blank_stock for label in stock), "invalid vacant stock")
    # Each contact guarantees occupancy conservation. Keep the indicated outputs
    # without inspecting any label of the two retired cells to decide acceptance.
    contact = fixture.contact
    if crossed:
        a, b_prime = contact((a, b_prime))
        a_prime, b = contact((a_prime, b))
    else:
        a, b = contact((a, b))
        a_prime, b_prime = contact((a_prime, b_prime))
    check(
        all(label in fixture.labels and fixture.occupied(label) == 0 for label in (a, b, a_prime, b_prime)),
        "blank preparation was not entirely vacant",
    )
    return a, b


def read(fixture: Fixture, blanks: Pair, token: int) -> Triple:
    check(token in fixture.token_stock, "invalid fresh occupied stock")
    a, b = blanks
    a, c = fixture.contact((a, token))
    a, b = fixture.contact((a, b))
    return a, b, c


@dataclass(frozen=True)
class Trial:
    stock: Stock
    survivors: Pair
    token: int
    raw_outputs: Triple
    occupation: Triple


@dataclass(frozen=True)
class Result:
    labels: tuple[int, ...]
    trials: tuple[Trial, ...]

    @property
    def blank_joint(self) -> dict[Pair, Fraction]:
        counts = Counter(trial.survivors for trial in self.trials)
        return {pair: F(count, len(self.trials)) for pair, count in counts.items()}

    @property
    def blank_marginals(self) -> tuple[tuple[Fraction, ...], ...]:
        return tuple(
            tuple(F(sum(trial.survivors[arm] == label for trial in self.trials), len(self.trials))
                  for label in self.labels)
            for arm in range(2)
        )

    @property
    def occupation_rates(self) -> tuple[Fraction, ...]:
        return tuple(F(sum(trial.occupation[arm] for trial in self.trials), len(self.trials))
                     for arm in range(3))


def run_pairing(fixture: Fixture, *, crossed: bool) -> Result:
    trials = []
    for stock in product(fixture.blank_stock, repeat=4):
        survivors = prepare(fixture, stock, crossed=crossed)
        for token in fixture.token_stock:
            outputs = read(fixture, survivors, token)
            check(all(label in fixture.labels for label in outputs), "reader escaped raw alphabet")
            occupation = tuple(map(fixture.occupied, outputs))
            check(occupation in ((1, 0, 0), (0, 1, 0), (0, 0, 1)), "reader did not keep exactly one token")
            trials.append(Trial(stock, survivors, token, outputs, occupation))
    check(len(trials) == len(fixture.blank_stock)**4 * len(fixture.token_stock) > 0, "missing trials")
    return Result(fixture.labels, tuple(trials))


def verify_raw(fixture: Fixture) -> None:
    pairs = set(product(fixture.labels, repeat=2))
    contact = fixture.contact
    check({contact(pair) for pair in pairs} == pairs, f"nonreversible {fixture.name}")
    vacancy, token = fixture.blank_stock, fixture.token_stock
    check(all(fixture.occupied(label) == 0 for label in vacancy), "blank stock contains a token")
    check(all(fixture.occupied(label) == 1 for label in token), "token stock contains a blank")
    for pair in pairs:
        image = contact(pair)
        check(contact(pair[::-1]) == image[::-1], f"swap equivariance failed on {pair}")
        check(contact(image) == (pair[::-1] if fixture.square_is_swap else pair), f"wrong square on {pair}")
        check(pair[0] != pair[1] or image == pair, f"diagonal moved at {pair}")
        count = sum(map(fixture.occupied, pair))
        check(sum(map(fixture.occupied, image)) == count, f"occupation changed on {pair}")
        if count == 1:
            original = EIGHT_LABEL if fixture.labels == EIGHT_LABEL.labels else FOUR_LABEL
            check(image == original.contact(pair), f"control changed mixed routing on {pair}")
    if not fixture.square_is_swap:
        check(contact(contact((0, 1))) != (1, 0), "involution unexpectedly squares to swap")


@dataclass(frozen=True)
class BinaryBlankBound:
    permutations: int
    equivariant_kernels: int
    preserves_bias: int
    complements_bias: int


def verify_binary_blank_bound() -> BinaryBlankBound:
    """One contact on two i.i.d. binary vacancies cannot create a record here.

    The swap-fixed diagonal labels can only permute with each other; the other
    two labels form a single swap orbit. For Bernoulli(p) inputs, the input atom
    with k ones has mass p**k * (1-p)**(2-k). Check the exponent on each output
    atom against Bernoulli(p) or Bernoulli(1-p) products, symbolically in p.
    One pairing thus keeps an i.i.d. output pair, and crossed pairing keeps
    independent cells from disjoint identical contacts with those same marginals.
    This includes diagonal swaps and does not address larger preparation circuits.
    """
    pairs = tuple(product(range(2), repeat=2))
    all_count = preserves = complements = 0
    for images in permutations(pairs):
        all_count += 1
        table = dict(zip(pairs, images, strict=True))
        if any(table[pair[::-1]] != table[pair][::-1] for pair in pairs):
            continue
        complement = int(table[(0, 0)] == (1, 1))
        for pair, image in table.items():
            exponent = 2 - sum(image) if complement else sum(image)
            check(sum(pair) == exponent, "binary contact violated the symbolic i.i.d. law")
        preserves += 1 - complement
        complements += complement
    check((all_count, preserves, complements) == (24, 2, 2), "binary kernel census changed")
    return BinaryBlankBound(all_count, preserves + complements, preserves, complements)


def verify() -> dict[str, tuple[tuple[Fraction, ...], tuple[Fraction, ...]]]:
    half = F(1, 2)
    quarter = F(1, 4)
    split = (quarter, quarter, half)
    expected = {
        EIGHT_LABEL.name: ((half, 0, half), (F(5, 16), F(3, 16), half)),
        EIGHT_LABEL_VACUUM_XOR.name: (split, split),
        EIGHT_LABEL_UNIFORM_BLANK.name: (split, split),
        FOUR_LABEL.name: ((0, quarter, F(3, 4)), (F(3, 16), F(1, 16), F(3, 4))),
        FOUR_LABEL_IDENTITY_BLANK.name: (split, split),
    }
    rates = {}
    for fixture in FIXTURES:
        verify_raw(fixture)
        same = run_pairing(fixture, crossed=False)
        crossed = run_pairing(fixture, crossed=True)
        check(same.blank_marginals == crossed.blank_marginals, f"distinct raw marginals: {fixture.name}")
        marginal_a, marginal_b = same.blank_marginals
        iid_joint = {(a, b): p_a * p_b for a, p_a in zip(fixture.labels, marginal_a, strict=True)
                     for b, p_b in zip(fixture.labels, marginal_b, strict=True) if p_a and p_b}
        check(crossed.blank_joint == iid_joint, f"crossed survivors not independent: {fixture.name}")
        if fixture in (EIGHT_LABEL, FOUR_LABEL):
            check(same.blank_joint != iid_joint, f"no joint blank record: {fixture.name}")
        if fixture in (EIGHT_LABEL_UNIFORM_BLANK, FOUR_LABEL_IDENTITY_BLANK):
            check(same.blank_joint == iid_joint, f"unexpected blank record in {fixture.name}")
        observed = same.occupation_rates, crossed.occupation_rates
        check(observed == expected[fixture.name], f"wrong fixed-reader occupation rates: {fixture.name}")
        rates[fixture.name] = observed
    verify_binary_blank_bound()
    return rates


def main() -> None:
    for name, (same, crossed) in verify().items():
        print(f"{name}: same ({', '.join(map(str, same))}); crossed ({', '.join(map(str, crossed))})")
    print("All preparations match per-cell raw marginals; every reader trial keeps one token.")
    print("Binary bound: all four swap-equivariant reversible blank kernels preserve i.i.d. stock.")
    print("Finite joint blank record with supplied wiring and occupation readout; no phase or plate claim.")


if __name__ == "__main__":
    main()
