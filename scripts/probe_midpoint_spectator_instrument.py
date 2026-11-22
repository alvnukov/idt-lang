"""One five-tag, three-site rule realizes a repeatable six-setting instrument.

The spectator is a distinct addressed wire and is never modified. The two
targets receive T if the spectator equals their midpoint, inverse T if not;
T(x,y)=(4x+2y,2x+4y) mod 5. No lookup table, separate memory alphabet,
outcome-conditioned external branch, raw tag measurement or built-in gate
other than this rule is used in the physical program. Fixed wiring, ordered
visits, blank supplies, one defect and fresh fair preparation choices count
as supplied resources. Introducing a spectator is a CHANGE of the binary
candidate, not a construction from its original two-site gate.

The prescribed ideal comparison is a two-outcome rank-one projective
instrument on six coplanar settings. Every realized first click is counted,
including either outcome of the second click. Preparation and reset use
the same two independent fair skip/step choices. Coinciding tables are not
evidence for Born's law, general measurement disturbance, tomography,
entanglement, any particle, or an internal origin for the program.
"""

from __future__ import annotations

from collections import Counter
from itertools import product

from scripts.probe_affine_pulse_holdouts import (
    FRINGE,
    TAGS,
    encode,
    gates,
    need,
    power,
)

Contact = tuple[int, int, int]
Word = tuple[Contact, ...]
Q = range(5)
S = range(6)
# Source data, a palette of *all* tags, the record/two tokens, and two
# new center-defect systems. No dedicated memory tag type.
DATA = (0, 1, 2)
PALETTE = (3, 4, 5, 6, 7)
RECORD = 8
TOKENS = (9, 10)
FRESH = (11, 12, 13)
OPPOSITE = (14, 15, 16)


def rule(s: int, x: int, y: int) -> tuple[int, int]:
    left, right = (4 * x + 2 * y) % 5, (2 * x + 4 * y) % 5
    return (left, right) if (2 * s - x - y) % 5 == 0 else (right, left)


def apply(v: list[int], word: Word) -> None:
    for s, i, j in word:
        v[i], v[j] = rule(v[s], v[i], v[j])


def plain(i: int, j: int, inverse: bool = False) -> Word:
    # Exactly one midpoint among the five spectators gives T, the others
    # its inverse: the net exponent -3 is +1 mod 4. Append U²=SWAP to
    # realize T^-1 regardless of the pair, with the very same primitive.
    return tuple((s, i, j) for s in PALETTE) + (
        ((PALETTE[0], i, j),) * 2 if inverse else ()
    )


def clock(ports: tuple[int, int, int], inverse: bool = False) -> Word:
    a, b, c = ports
    edges = ((a, b), (b, c)) * 2
    return tuple(
        u
        for i, j in (reversed(edges) if inverse else edges)
        for u in plain(i, j, inverse)
    )


def test_swap(control: int, ref: int, i: int, j: int) -> Word:
    """For targets with midpoint ref, swap iff control=ref (equal targets are inert)."""
    return ((control, i, j), (ref, i, j))


def reader() -> Word:
    # Initial latch m, hit token p=2b-m. A hit exchanges those two; if
    # a previous hit filled the latch the next token is identical and no
    # operation can undo it. Thus this is OR, not an XOR/two-hit cancellation.
    return (
        test_swap(DATA[0], PALETTE[0], RECORD, TOKENS[0])
        + clock(DATA, True)
        + test_swap(DATA[0], PALETTE[0], RECORD, TOKENS[1])
        + clock(DATA)
    )


def source(b: int, a: int, kits: int) -> tuple[int, ...]:
    """From one defect prepare one kit on 48 wires or two kits on 99.

    A contact on (blank, b+t) with blank spectator splits relative t into
    (-t,2t). Four such splits turn one t and four blanks into two t and
    three 3t. Nothing is cloned with all other wires restored. Unselected
    factory wires remain as explicit unused stock/garbage.
    No color-dependent address or independent supply of defects.
    """
    v = [b, a]
    visits = 0

    def blank() -> int:
        v.append(b)
        return len(v) - 1

    def split(j: int) -> tuple[int, int]:
        nonlocal visits
        i = blank()
        need(len({0, i, j}) == 3, "factory address collision")
        apply(v, ((0, i, j),))
        visits += 1
        return i, j

    defects = [1]
    need(kits in (1, 2), "unknown factory layout")
    for _ in range(9 * kits - 1):
        minus, twice = split(defects.pop())
        back1, _ = split(minus)
        _, fourfold = split(twice)
        back2, _ = split(fourfold)
        defects.extend((back1, back2))
    need(
        len(set(defects)) == 9 * kits and all(v[i] == a for i in defects),
        "single-defect fanout",
    )

    def make_pair() -> tuple[int, int]:
        return split(defects.pop())

    def make_three() -> int:
        _, j = make_pair()
        i, _ = split(j)
        return i

    indices: list[int] = []
    for k in range(kits):
        four, two = make_pair()
        three = make_three()
        _, m = make_pair()
        hit1, hit2 = make_three(), make_three()
        bank = (
            0 if k == 0 else blank(),
            defects.pop(),
            two,
            three,
            four,
            m,
            hit1,
            hit2,
        )
        seed, fresh, opposite = [(blank(), defects.pop(), blank()) for _ in range(3)]
        indices.extend(seed + bank + fresh + opposite)
    delta = a - b
    actual = tuple(v[i] for i in indices)
    need(
        actual
        == tuple(
            (b + u * delta) % 5
            for u in (0, 1, 0, 0, 1, 2, 3, 4, 2, 3, 3, 0, 1, 0, 0, 1, 0)
        )
        * kits,
        "stock compiler",
    )
    need(
        len(set(indices)) == 17 * kits
        and len(v) == 51 * kits - 3
        and not defects
        and visits == 44 * kits - 4,
        "factory accounting",
    )
    need((sum(v) - ((len(v) - 1) * b + a)) % 5 == 0, "factory lost conserved sum")
    return actual


def elementary() -> None:
    for s, x, y in product(Q, repeat=3):
        p, q = rule(s, x, y)
        need(
            rule(s, p, q) == (y, x) and (p + q - x - y) % 5 == 0,
            "swap root or conserved sum",
        )
        for u, v in product(range(1, 5), Q):
            transformed = rule((u * s + v) % 5, (u * x + v) % 5, (u * y + v) % 5)
            need(transformed == ((u * p + v) % 5, (u * q + v) % 5), "frame covariance")
        for another in Q:
            t = rule(another, p, q)
            if (2 * another - x - y) % 5 == 0:
                need(
                    t == ((y, x) if (2 * s - x - y) % 5 == 0 else (x, y)),
                    "comparison-controlled swap",
                )
    # Restricted preparation cost: to synthesize the same T on *every*
    # unequal pair with a word solely of unmodified stock spectators on
    # these target ports, each midpoint must have the same parity of visits.
    # If all even the total exponent is even; if all odd at least 5 visits.
    for length in range(5):
        for word in product(Q, repeat=length):
            need(
                any((2 * word.count(mid) - length) % 4 != 1 for mid in Q),
                "shorter fixed-palette pulse",
            )


def main() -> None:
    elementary()
    w, _ = gates()
    dials = [power(w, j) for j in S]
    read_word = reader()
    switch_word = tuple(
        c
        for i, j in zip(FRESH, OPPOSITE, strict=True)
        for c in test_swap(RECORD, PALETTE[2], i, j)
    )
    prepare_opposite = clock(OPPOSITE) * 3
    need(
        (len(read_word), len(switch_word), len(prepare_opposite)) == (52, 6, 60),
        "contact accounting",
    )
    all_words = read_word + switch_word + prepare_opposite + clock(FRESH)
    # A second physical recorder uses the first apparatus's output wires as
    # its signal. Distinct supplies preserve the first raw record throughout.
    ports = (*FRESH, *range(20, 34))
    second_reader = tuple((ports[s], ports[i], ports[j]) for s, i, j in read_word)
    need(
        all(
            len({c, i, j}) == 3 and min(c, i, j) >= 0 and max(c, i, j) < 17
            for c, i, j in all_words
        ),
        "invalid addresses",
    )
    first_cases = joint_trials = 0
    for b, a in product(Q, repeat=2):
        if b == a:
            continue
        stock = source(b, a, 1)
        double = source(b, a, 2)
        need(double == stock * 2, "two-kit factory")
        m, hit = stock[RECORD], stock[TOKENS[0]]
        seed_id = encode(*stock[:3])
        orbit = [h[seed_id] for h in dials]
        reading: dict[int, bool] = {}
        transitions: dict[int, tuple[int, ...]] = {}
        for n, s in enumerate(TAGS):
            start = [*s, *stock[3:]]
            current = start.copy()
            apply(current, read_word)
            bit = current[RECORD] == hit
            need(
                current[:8] == start[:8] and current[RECORD] in (m, hit),
                "record damaged data or wrong code",
            )
            need(bit == (s[0] == b or TAGS[dials[5][n]][0] == b), "old D not recorded")
            reading[n] = bit
            apply(current, prepare_opposite + switch_word)
            need(
                current[:8] == start[:8] and current[RECORD] == (hit if bit else m),
                "source or record drift",
            )
            outputs = []
            for count in (0, 1, 1, 2):
                trial = current.copy()
                apply(trial, clock(FRESH) * count)
                out = encode(*(trial[p] for p in FRESH))
                need(
                    out == orbit[(count + (0 if bit else 3)) % 6],
                    "poststate is not the target raw ticket",
                )
                need((sum(trial) - sum(start)) % 5 == 0, "lost tag sum")
                outputs.append(out)
            transitions[n] = tuple(outputs)
            first_cases += 1
        for n, j in product(S, repeat=2):
            scores: Counter[tuple[bool, bool]] = Counter()
            for pre in (0, 1, 1, 2):
                initial = orbit[(pre + n) % 6]
                for shift, out in zip((0, 1, 1, 2), transitions[initial], strict=True):
                    physical = list(double)
                    apply(
                        physical,
                        clock(DATA) * (pre + n)
                        + read_word
                        + prepare_opposite
                        + switch_word
                        + clock(FRESH) * (shift + j)
                        + second_reader,
                    )
                    observed = (physical[RECORD] == hit, physical[ports[RECORD]] == hit)
                    need(
                        observed == (reading[initial], reading[dials[j][out]]),
                        "two physical records vs independent table",
                    )
                    need(
                        (sum(physical) - sum(double)) % 5 == 0,
                        "double instrument tag sum",
                    )
                    scores[observed] += 1
                    joint_trials += 1
            for bright in (False, True):
                first = FRINGE[n] if bright else 4 - FRINGE[n]
                second = FRINGE[(j + (0 if bright else 3)) % 6]
                need(
                    scores[bright, True] == first * second
                    and scores[bright, False] == first * (4 - second),
                    "joint all-trial benchmark",
                )
    need((first_cases, joint_trials) == (2500, 11520), "incomplete frame or trial grid")

    # Distinct control: two spacelike-separated devices with independent
    # setting selection and no messages. For every possible paired latent
    # state the two local responses are deterministic. Convex mixing and
    # independent local coins cannot raise the CHSH bound. A sequential
    # signal is *not* a second separated device. The comparison ideal for
    # these six directions is 5/2, not the optimized continuum 2*sqrt(2).
    def local(i: int, j: int) -> int:
        x = dials[j][i]
        return 1 if TAGS[x][0] == 0 or TAGS[dials[5][x]][0] == 0 else -1

    chsh = {
        local(x, 0) * (local(y, 1) + local(y, 0))
        + local(x, 2) * (local(y, 1) - local(y, 0))
        for x, y in product(range(125), repeat=2)
    }
    cos_twice = tuple(n - 2 for n in FRINGE)
    ideal_twice = sum(
        sgn * (-cos_twice[(u - v) % 6])
        for u, v, sgn in ((0, 1, 1), (0, 0, 1), (2, 1, 1), (2, 0, -1))
    )
    need(chsh == {-2, 2} and ideal_twice == -5, "separated pair control")
    print(
        "One midpoint-spectator gate on five tags: common root of swap, affine-label covariant, nonlinear color response."
    )
    print(
        "One defect + 47 blank tags: 40 contacts prepare all 17 working wires. Reader 52, opposite preparation 60, switching 6; addresses and fair tickets supplied."
    )
    print(
        "All 2,500 raw input/frame cases record the original detector and prepare the exact conditional four-ticket stock."
    )
    print(
        "One defect + 98 blanks: two complete kits (84 stock contacts); all 11,520 literal two-record histories match the supplied projective benchmark."
    )
    print(
        "Separate local copies and arbitrary shared raw stock: |CHSH| <= 2; supplied singlet target for the same dial family is 5/2."
    )


if __name__ == "__main__":
    main()
