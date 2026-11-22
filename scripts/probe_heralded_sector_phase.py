"""Exact heralded and finite-mean RUS sector phase, with every outcome retained.

Target U=diag(z,1), z=(3+4i)/5=(2+i)/(2-i), and pi=1+i. The native
logical instructions are T=((1+i,1-i),(1-i,1+i))/2 and a slot phase i.
On SUPPLIED antisymmetric dual rails, logical T is two addressed physical
T gates and slot i is one within-pair physical T. Product addresses
(charge, ancilla, rail) and coherent charge-controlled wiring are supplied.
The charges here are logical labels, not derived physical conserved charges.
No independent Hadamard, continuous phase, or external fair-bit source is used.

First control: a compiled balanced 16-path prepare/phase/unprepare circuit
has heralded Kraus diag((3+4i)/8,5/8), hence success 25/64 independent of
data. Some other outcomes distinguish the charges. They cannot be repaired
by a protocol that terminates almost surely with exactly U for every input
while retaining the entire record: every terminal refined Kraus would be
scalar*U, so summing effects below any prefix would make that prefix effect
scalar*I, contradicting the informative failure. Heralded success remains
valid; blindly repeating after those failures does not implement RUS.

Constructive RUS: prepare the following ancilla columns conditioned on charge:
    u=(2+i, 1+i, 1)/pi^3,  v=(2-i, 1+i, 1)/pi^3.
Their squared coordinate magnitudes are (5,2,1)/8. Ancilla-only readout gives
    K0=((2-i)/pi^3) U, K1=(1/pi^2) I, K2=(1/pi^3) I.
Thus failure is harmless even on data entangled with a reference. Reset the
observed ancilla basis state to 0 and retry. Under the SUPPLIED ideal
conditional instrument law, tail after N attempts is (3/8)^N, expected
attempts 8/5 and expected resets 3/5. No bounded worst-case time exists.
Native gate counts below are explicit sequential physical T applications,
not optimal parallel depth. Readout/control latency and initial encoded-data
preparation are not included; a finite fixed readout cost adds 8/5 times it.

CRITICAL APPARATUS PREMISE: read only the ancilla, coherently grouping both
charge sectors, without recording charge or rail. Charge-resolved physical
port detection destroys the data coherence. Ideal heralds, nondemolition
grouped readout, conditional reset and the stochastic instrument law are
not derived by these gate identities. No individual-outcome origin or
physical implementation/empirical iid claim follows.
All guarantees use exact gates and readout/reset instruments. No robustness
bound is supplied: imperfect failures may leak charge or accumulate errors.

Finite-tree wall survives. Let R=Z[i,1/2]. A finite complete native tree
with basis heralds, all resources in R and exact corrected output U has
every refined terminal Kraus beta_j U. Both beta_j and beta_j*z belong to R,
forcing beta_j=(2-i)gamma_j with gamma_j in R. Indeed reduction modulo
(2-i) sends i to 2 in F5; the factor (2+i) maps to 4, a unit. Hence each
terminal probability |beta_j|^2 lies in 5 Z[1/2]. No finite sum equals 1.
This excludes bounded complete trees in that resource class, not a finite
heralded subexperiment or an infinite almost-sure finite-mean tree. The RUS
sum (5/8)*sum_n(3/8)^n=1 escapes exactly through its infinite support.

All numbers and compiled words below are exact. General arguments above
are not Lean proofs. No new physical primitive, fitted parameter, Born-law
derivation, finite deterministic phase, or full QM closure is asserted.

Run: python3 -B -O -m scripts.probe_heralded_sector_phase
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import (
    CROSS,
    DIAG,
    ONE,
    PI,
    ZERO,
    Gaussian,
    I,
    Move,
    eye,
    g,
    integral_lift,
    unitary,
)
from scripts.gaussian_dyadic_words import (
    run as run_words,
)

Column = tuple[Gaussian, ...]
Kraus = tuple[Gaussian, Gaussian]
Z = g(F(3, 5), F(4, 5))


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError(reason)


def divide(value: Gaussian, divisor: Gaussian) -> Gaussian:
    need(divisor != ZERO, "division by zero")
    return value * divisor.star() * g(1 / divisor.norm2())


def compact(moves: tuple[Move, ...]) -> tuple[Move, ...]:
    """Only adjacent identical order-four gates are reduced; no optimization claim."""
    out: list[Move] = []
    for move in moves:
        out.append(move)
        if len(out) >= 4 and out[-4:] == [move] * 4:
            del out[-4:]
    return tuple(out)


def inverse(moves: tuple[Move, ...]) -> tuple[Move, ...]:
    return compact(tuple(move for move in reversed(moves) for _ in range(3)))


def apply_column(column: Column, move: Move) -> Column:
    tag, j, k = move
    need(0 <= j < len(column) and 0 <= k < len(column), "address outside column")
    out = list(column)
    if tag == "i" and j == k:
        out[j] = I * column[j]
    elif tag == "T" and j != k:
        out[j] = DIAG * column[j] + CROSS * column[k]
        out[k] = CROSS * column[j] + DIAG * column[k]
    else:
        raise ValueError("invalid native move")
    return tuple(out)


def propagate(column: Column, moves: tuple[Move, ...]) -> Column:
    for move in moves:
        column = apply_column(column, move)
    return column


def prepare_column(target: Column) -> tuple[tuple[Move, ...], tuple[int, ...]]:
    """Pi-denominator lowering with replay of an actual finite native word.

    At denominator pi^k the integer norm is 2^k. Odd Gaussian entries come
    in pairs. Rotate y by i if needed so y=i*x mod 2. The native T sends
    x,y to (i*x+y)/pi,(x+i*y)/pi, both divisible by pi. Pairing every odd
    entry therefore lowers the denominator. The integral endpoint is a
    signed unit axis. This constructs a column, not an imported completion.
    """
    need(bool(target) and all(x.dyadic() for x in target), "Gaussian-dyadic column")
    need(sum((x.norm2() for x in target), F(0)) == 1, "unit column")
    current = target
    reduction: list[Move] = []
    powers = []

    def move(op: Move) -> None:
        nonlocal current
        current = apply_column(current, op)
        reduction.append(op)

    while True:
        power, nums = integral_lift(current)
        powers.append(power)
        need(sum((x.norm2() for x in nums), F(0)) == 2**power, "integer norm")
        if power == 0:
            break
        odd = [j for j, x in enumerate(nums) if int(x.re + x.im) % 2]
        need(bool(odd) and len(odd) % 2 == 0, "even nonempty odd-entry count")
        for j, k in zip(odd[::2], odd[1::2], strict=True):
            difference = nums[k] - I * nums[j]
            if int(difference.re) % 2 or int(difference.im) % 2:
                move(("i", k, k))
            move(("T", j, k))
        need(integral_lift(current)[0] < power, "strict denominator descent")
    axes = [j for j, x in enumerate(current) if x != ZERO]
    need(len(axes) == 1, "integral unit axis")
    axis = axes[0]
    if axis:
        move(("T", 0, axis))
        move(("T", 0, axis))
    for _ in range(3):
        if current[0] == ONE:
            break
        move(("i", 0, 0))
    source = (ONE,) + (ZERO,) * (len(target) - 1)
    need(current == source, "column reduction endpoint")
    word = inverse(tuple(reduction))
    need(propagate(source, word) == target, "prepared column replay")
    matrix = run_words(eye(len(target)), word)
    need(
        unitary(matrix) and tuple(row[0] for row in matrix) == target,
        "unitary completion replay",
    )
    return word, tuple(powers)


def physical_word(moves: tuple[Move, ...]) -> tuple[Move, ...]:
    """Decode logical operations into physical T-only paired-rail gates."""
    out: list[Move] = []
    for tag, j, k in moves:
        if tag == "i":
            need(j == k, "phase instruction")
            out.append(("T", 2 * j, 2 * j + 1))
        else:
            out.extend((("T", 2 * j, 2 * k), ("T", 2 * j + 1, 2 * k + 1)))
    return tuple(out)


def shifted(moves: tuple[Move, ...], offset: int) -> tuple[Move, ...]:
    return tuple((tag, j + offset, k + offset) for tag, j, k in moves)


def paired(column: Column) -> Column:
    # Common unnormalized code norm is 2; no free 1/sqrt(2) gate is inserted.
    return tuple(value for x in column for value in (x, ZERO - x))


def check_physical(moves: tuple[Move, ...], size: int) -> int:
    physical = physical_word(moves)
    need(all(tag == "T" for tag, _, _ in physical), "physical instruction alphabet")
    for j in range(size):
        source = tuple(ONE if i == j else ZERO for i in range(size))
        need(
            propagate(paired(source), physical) == paired(propagate(source, moves)),
            "physical paired-code replay",
        )
    return len(physical)


def balanced_word(bits: int) -> tuple[Move, ...]:
    """Uniform-magnitude binary tree: G=S T S, not a supplied Hadamard."""
    need(bits > 0, "positive binary depth")
    moves: list[Move] = []
    for bit in range(bits):
        for j in range(2**bits):
            if not (j & (1 << bit)):
                k = j | (1 << bit)
                moves.extend((("i", k, k), ("T", j, k), ("i", k, k)))
    return tuple(moves)


def unit_phase_moves(phases: Column) -> tuple[Move, ...]:
    units = (ONE, I, g(-1), g(0, -1))
    need(all(x in units for x in phases), "branch phases must be native fourth roots")
    return tuple(
        ("i", j, j) for j, phase in enumerate(phases) for _ in range(units.index(phase))
    )


def simple_heralded_control() -> tuple[Kraus, ...]:
    # Sixteen phases sum to 6+8i and 10 respectively: denominator-16
    # variant of the denominator-8 construction, with no diverted leaf.
    phases0 = (ONE,) * 7 + (g(-1),) + (I,) * 8
    phases1 = (ONE,) * 13 + (g(-1),) * 3
    word = balanced_word(4)
    source = (ONE,) + (ZERO,) * 15
    prepared = propagate(source, word)
    need(all(x.norm2() == F(1, 16) for x in prepared), "native balanced magnitudes")
    outputs = []
    for phases in (phases0, phases1):
        outputs.append(
            propagate(source, word + unit_phase_moves(phases) + inverse(word))
        )
    kraus = tuple(zip(outputs[0], outputs[1], strict=True))
    need(kraus[0] == (g(F(3, 8), F(1, 2)), g(F(5, 8))), "simple heralded target")
    need(divide(kraus[0][0], kraus[0][1]) == Z, "heralded relative phase")
    need(
        kraus[0][0].norm2() == kraus[0][1].norm2() == F(25, 64),
        "heralded success independent of data",
    )
    need(
        all(sum((pair[q].norm2() for pair in kraus), F(0)) == 1 for q in range(2)),
        "all simple-control outcomes retained",
    )
    harmful = [
        (j, a.norm2(), b.norm2())
        for j, (a, b) in enumerate(kraus[1:], 1)
        if a.norm2() != b.norm2()
    ]
    need(bool(harmful), "simple LCU must expose its informative failure")
    # Independently verify the concrete G table without using H as a gate.
    gate = run_words(eye(2), balanced_word(1))
    need(gate == ((DIAG, DIAG), (DIAG, ZERO - DIAG)), "compiled S T S table")
    check_physical(balanced_word(1), 2)
    print(
        f"Simple native 16-path herald: success=25/64; first informative failure (label,p0,p1)={harmful[0]}."
    )
    print(
        "That herald is exact, but informative failure forbids an all-record a.s.-exact repair for every input."
    )
    return kraus


def dyadic(value: F) -> bool:
    denominator = value.denominator
    return denominator & (denominator - 1) == 0


def residue_mod_five(value: Gaussian) -> int:
    """R/(2-i) -> F5, where i maps to 2 and dyadic denominators are units."""
    need(value.dyadic(), "mod-five input outside Gaussian-dyadic ring")
    return (
        value.re.numerator * pow(value.re.denominator, -1, 5)
        + 2 * value.im.numerator * pow(value.im.denominator, -1, 5)
    ) % 5


def finite_tree_controls(success: Gaussian, failures: tuple[Gaussian, ...]) -> int:
    need(not Z.dyadic() and Z.norm2() == 1, "non-dyadic unit target")
    need(
        residue_mod_five(g(2, -1)) == 0 and residue_mod_five(g(2, 1)) == 4,
        "distinct Gaussian prime factors",
    )
    cases = 0
    for power in range(4):
        for re, im in product(range(-6, 7), repeat=2):
            beta = g(F(re, 2**power), F(im, 2**power))
            admissible = (beta * Z).dyadic()
            need(admissible == (residue_mod_five(beta) == 0), "divisibility control")
            if admissible:
                gamma = divide(beta, g(2, -1))
                need(
                    gamma.dyadic() and beta.norm2() == 5 * gamma.norm2(),
                    "terminal weight factor five",
                )
            cases += 1
    for depth in range(7):
        aggregate_success = F(0)
        for history in product(failures, repeat=depth):
            beta = success
            for scalar in history:
                beta = beta * scalar
            need((beta * Z).dyadic() and beta.dyadic(), "native terminal amplitudes")
            need(
                dyadic(beta.norm2() / 5),
                "every refined RUS leaf has five-dyadic weight",
            )
            aggregate_success += beta.norm2()
        need(
            aggregate_success == F(5, 8) * F(3, 8) ** depth,
            "sum of every recorded terminal history at this depth",
        )
    return cases


def run() -> None:
    simple_heralded_control()
    denominator = PI * PI * PI
    u = tuple(divide(x, denominator) for x in (g(2, 1), PI, ONE))
    v = tuple(divide(x, denominator) for x in (g(2, -1), PI, ONE))
    need(
        tuple(x.norm2() for x in u)
        == tuple(x.norm2() for x in v)
        == (F(5, 8), F(1, 4), F(1, 8)),
        "equal outcome effects",
    )
    word0, descent0 = prepare_column(u)
    word1, descent1 = prepare_column(v)
    controlled = word0 + shifted(word1, 3)
    preparation_cost = check_physical(controlled, 6)
    need(
        all((j < 3) == (k < 3) for _, j, k in controlled),
        "no native gate changes charge",
    )
    for charge, expected in enumerate((u, v)):
        source = tuple(ONE if j == 3 * charge else ZERO for j in range(6))
        actual = propagate(source, controlled)
        need(actual[3 * charge : 3 * charge + 3] == expected, "controlled preparation")
        need(
            all(x == ZERO for j, x in enumerate(actual) if j // 3 != charge),
            "sector leakage",
        )
    kraus = tuple(zip(u, v, strict=True))
    success = divide(g(2, -1), denominator)
    need(kraus[0] == (success * Z, success), "success exact unitary times scalar")
    failures = (divide(PI, denominator), divide(ONE, denominator))
    need(
        kraus[1:] == tuple((scalar, scalar) for scalar in failures),
        "every failure is scalar identity",
    )
    # Splitting the success herald by charge and then forgetting that record
    # is dephasing, not a coherent ancilla-only herald. Probe a normalized
    # dyadic coherent input (DIAG,CROSS), whose off-diagonal entry is nonzero.
    input_coherence = DIAG * CROSS.star()
    success_coherence = kraus[0][0] * kraus[0][1].star() * input_coherence
    fine_grained = ((kraus[0][0], ZERO), (ZERO, kraus[0][1]))
    charge_resolved_coherence = sum(
        (a * b.star() * input_coherence for a, b in fine_grained), ZERO
    )
    need(
        success_coherence == g(F(5, 8)) * Z * input_coherence != ZERO,
        "coherent grouped herald preserves the relative phase",
    )
    need(
        charge_resolved_coherence == ZERO, "charge-resolved readout destroys coherence"
    )
    need(sum((scalar.norm2() for scalar in failures), F(0)) == F(3, 8), "failure mass")
    reset_costs = []
    for outcome in (1, 2):
        reset: tuple[Move, ...] = tuple(
            ("T", 3 * charge, 3 * charge + outcome)
            for charge in range(2)
            for _ in range(2)
        )
        reset_costs.append(check_physical(reset, 6))
        for charge in range(2):
            source = tuple(ONE if j == 3 * charge + outcome else ZERO for j in range(6))
            target = tuple(ONE if j == 3 * charge else ZERO for j in range(6))
            need(
                propagate(source, reset) == target,
                "conditional reset preserves charge coherence",
            )
    need(reset_costs == [8, 8], "explicit physical reset cost")
    p, q = F(5, 8), F(3, 8)
    for cutoff in range(1, 17):
        tail = q**cutoff
        success_by_cutoff = sum((p * q**k for k in range(cutoff)), F(0))
        expected_truncated = sum((q**k for k in range(cutoff)), F(0))
        need(
            success_by_cutoff == 1 - tail < 1,
            "finite cutoff is not deterministic completion",
        )
        need(expected_truncated == (1 - tail) / p, "finite survival-sum cost")
        need(dyadic(success_by_cutoff / 5), "finite-tree success remains five-dyadic")
    expected_attempts = 1 / p
    expected_resets = q / p
    expected_native_cost = (
        preparation_cost * expected_attempts + reset_costs[0] * expected_resets
    )
    cases = finite_tree_controls(success, failures)
    print(
        f"RUS columns compiled: pi-denominator descents={descent0}, {descent1}; logical moves={len(word0)}+{len(word1)}."
    )
    print(
        "All three recorded effects are input-independent: success 5/8, identity failures 1/4 and 1/8."
    )
    print(
        f"Exact tail=(3/8)^N; expected attempts={expected_attempts}, resets={expected_resets}; no finite worst-case bound."
    )
    print(
        f"Explicit sequential physical T applications: preparation={preparation_cost}, each reset=8, expected total={expected_native_cost}."
    )
    print(
        f"Finite-tree Gaussian-prime control: {cases} exact grid points; all refined terminal RUS branches through six failures checked."
    )
    print(
        "Costs exclude supplied encoded-data preparation and coherent ancilla readout/control. No physical outcome-origin or Lean-proof claim."
    )


if __name__ == "__main__":
    run()
