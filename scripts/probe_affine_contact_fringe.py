"""A native six-beat process on five tags; what the observer still supplies.

On two tags in Fp impose covariance under every affine change x -> ux+v
(u!=0), equality-diagonal fixing and T²=wire SWAP. The affine group acts
sharply transitively on ordered distinct pairs, so a gate is determined by
T(0,1)=(j,j+t). Its difference multiplier must obey t²=-1 and j(1+t)=1.
In F5 the two solutions are each other's inverse. Choose t=2: the same
gate T(x,y)=(4x+2y,2x+4y) is used on either neighboring pair. No six
tags, phase angle, table of probabilities or space coordinates enter it.

On three addressed cells let A=T01, B=T12, W=ABAB in chronological order.
All nonconstant triples have period six under W, even though one isolated
gate has order four. W³ reflects all tags about their common mean. With
only the triple and no oriented reference, that is a simultaneous affine
relabeling: no affine-invariant observation of the isolated triple can
distinguish these antipodes. A shared frame is not an observed phase.

Prepare (b,a,b) with a!=b, retain one local reference b, then supply two
independent fair choices of skipping or applying W. At the terminal reader
ask whether the first cell contacts the reference (is equal to b) now
OR after one reverse W step. This fixed two-visit reader uses only literal
comparisons, not a six-mark lookup; it gives one output bit per trial. No
reference is consulted mid-word. The reference, reliable equality event,
OR of contacts, addressing and preparation randomness are NOT derived.
The earlier end-defect/last-cell two-reverse-visit proposal fails; its
actual row is kept below. The center-defect arrangement is an alternative
construction, not a blind experimental holdout.

The readout gap is constructive: for the six states from a uniform
background plus one defect, any *single* nonconstant affine scalar readout
takes at least three distinct values; no raw affine circuit with fixed
additional cells can provide a nonconstant two-value latch even just on
this orbit. The code enumerates all affine line tests on its two-dimensional
constant-sum plane. This is not a wall on nonlinear detectors or another
primitive. Changing the frame (a,b) alone supplies no random skip history.

In F13 also test the distinct stronger single-relative-tag requirement:
(c+x,c-x,c) -> (c+4x,c-4x,c) by six elementary visits. Conservation of
the total tag forbids rotating only one uncompensated tag while restoring
all others. These are finite affine models, not quantum waves or particles;
in particular no occupation label, Born law or experimental counts appear.

Replay: python3 -B -O -m scripts.probe_affine_contact_fringe
"""

from __future__ import annotations

from collections import Counter, deque
from itertools import product

Triple = tuple[int, int, int]
Word = tuple[int, ...]
Six = (0, 1, 0, 1)


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ValueError(why)


def gate(x: int, y: int, p: int, t: int) -> tuple[int, int]:
    j = pow(1 + t, -1, p)
    first = x + j * (y - x)
    return first % p, (first + t * (y - x)) % p


def act(s: Triple, word: Word, p: int = 5, t: int = 2) -> Triple:
    a, b, c = s
    for i in word:
        if i == 0:
            a, b = gate(a, b, p, t)
        elif i == 1:
            b, c = gate(b, c, p, t)
        else:
            raise ValueError("unknown contact")
    return a, b, c


def inverse(word: Word) -> Word:
    # Each T has order four. No implicit inverse device.
    return tuple(i for i in reversed(word) for _ in range(3))


def cycle(s: Triple, word: Word) -> list[Triple]:
    seen = [s]
    nxt = act(s, word)
    while nxt != s:
        need(nxt not in seen, "non-permutation orbit")
        seen.append(nxt)
        nxt = act(nxt, word)
    return seen


def detector(s: Triple, reference: int) -> bool:
    r = inverse(Six)
    first = act(s, r)
    return s[0] == reference or first[0] == reference


def rule_checks() -> None:
    for p, roots in ((2, []), (3, []), (5, [2, 3]), (7, []), (13, [5, 8])):
        choices = [
            (j, t)
            for j, t in product(range(p), range(p))
            if t * t % p == (-1) % p and j * (1 + t) % p == 1
        ]
        need(sorted(t for j, t in choices) == roots, "unexpected scalar gate")
        for j, t in choices:
            for x, y in product(range(p), range(p)):
                a, b = gate(x, y, p, t)
                need((a + b - x - y) % p == 0, "sum not conserved")
                need(gate(a, b, p, t) == (y, x), "not a swap root")
                for u, v in product(range(1, p), range(p)):
                    need(
                        gate((u * x + v) % p, (u * y + v) % p, p, t)
                        == ((u * a + v) % p, (u * b + v) % p),
                        "affine frame dependence",
                    )


def shortest_process() -> None:
    states = list(product(range(5), range(5), range(5)))
    winners = []
    for length in range(5):
        for word in product(range(2), repeat=length):
            lengths = Counter(len(cycle(s, word)) for s in states)
            if 6 in lengths:
                need(lengths == {1: 5, 6: 120}, "partial period-six branch")
                winners.append(word)
    need(winners == [Six, (1, 0, 1, 0)], "unexpected shortest native programs")
    for s in states:
        mean = sum(s) * pow(3, -1, 5) % 5
        need(
            act(s, Six * 3) == tuple((2 * mean - x) % 5 for x in s),
            "unmarked antipodes are not frame reflections",
        )


def fringe_checks() -> None:
    for a, b in product(range(5), range(5)):
        if a == b:
            need(act((a, b, b), Six) == (a, b, b), "no-defect control moved")
            continue
        failed = cycle((a, b, b), Six)
        old_hits = [x[2] == b for x in failed]
        old_window = [old_hits[(n - 1) % 6] or old_hits[(n - 2) % 6] for n in range(6)]
        old_row = [
            sum(old_window[(n + i + k) % 6] for i, k in product(range(2), repeat=2))
            for n in range(6)
        ]
        need(old_row == [3, 3, 1, 0, 0, 1], "failed detector control")
        s = (b, a, b)
        six = cycle(s, Six)
        need(len(six) == 6, "wanted actual six distinct triples")
        need([int(x[0] == b) for x in six] == [1, 1, 0, 0, 0, 0], "contact sequence")
        need([int(detector(x, b)) for x in six] == [1, 1, 1, 0, 0, 0], "window shift")
        rows = []
        for n in range(6):
            outputs = [
                int(detector(act(s, Six * (i + k + n)), b))
                for i, k in product(range(2), repeat=2)
            ]
            need(len(outputs) == 4, "lost a source history")
            rows.append(sum(outputs))
        need(rows == [4, 3, 1, 0, 1, 3], "all-emission finite fringe")
        # Constant-sum plane: for arbitrary output coordinate of an affine
        # circuit the third raw tag can be eliminated into an offset. An
        # affine line hits at most two points (also after adding fixed stock).
        all_ranges = set()
        for u, v in product(range(5), range(5)):
            if u or v:
                counts = Counter((u * x + v * y) % 5 for x, y, _ in six)
                all_ranges.add(len(counts))
                need(max(counts.values()) <= 2, "three orbit points collinear")
        need(min(all_ranges) >= 3, "raw binary readout escape")


def conserved_pair_pulse() -> Word:
    initial = (1, 12, 0)
    goal = (4, 9, 0)
    paths: dict[Triple, Word] = {initial: ()}
    queue = deque([initial])
    while queue:
        s = queue.popleft()
        for i in (0, 1):
            nxt = act(s, (i,), 13, 5)
            if nxt not in paths:
                paths[nxt] = paths[s] + (i,)
                queue.append(nxt)
    need(len(paths) == 168, "wrong balanced orbit")
    word = paths[goal]
    need(word == (1, 1, 0, 1, 0, 1), "shortest restored-reference witness changed")
    for c, x in product(range(13), range(13)):
        s = ((c + x) % 13, (c - x) % 13, c)
        need(
            act(s, word, 13, 5) == ((c + 4 * x) % 13, (c - 4 * x) % 13, c),
            "failed symbolic encoding",
        )
    need(
        [pow(4, i, 13) for i in range(6)] == [1, 4, 3, 12, 9, 10]
        and pow(4, 6, 13) == 1,
        "encoded action is not order six",
    )
    return word


def main() -> None:
    rule_checks()
    shortest_process()
    fringe_checks()
    word = conserved_pair_pulse()
    print(
        "F5: ABAB or BABA are the shortest positive neighbor programs with an order-six orbit."
    )
    print(
        "Each fixes 5 constant triples and cycles the other 120; the unmarked antipodes are affine-equivalent."
    )
    print(
        "One defect, two fair skip/step choices, two literal reference contacts: 4,3,1,0,1,3 out of four."
    )
    print(
        "All 20 ordered defect/background choices agree. No affine output wire gives a nonconstant binary latch."
    )
    print(
        f"F13: shortest balanced-pair x->4x with restored center: {''.join('AB'[i] for i in word)}; all 169 inputs."
    )
    print(
        "The equality event, recording it and fair preparation remain supplied; no native occupation or QM claim."
    )


if __name__ == "__main__":
    main()
