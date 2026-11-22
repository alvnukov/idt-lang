"""Alternative-setting gap budgets and an inaccessible routed Bell journal.

Generic finite bound: any common joint Q(A0,A1,B0,B1) has |CHSH(Q)|<=2.
If standalone pair tables P_xy are at total-variation distances d_xy from
Q's pair reductions, |CHSH(P)|<=min(4,2+2*sum d_xy). The factor two uses
the full [-1,1] range of a binary correlation. Explicit local joints below
make the bound sharp for isotropic boxes and for the existing routed box.

A cheaper operational comparison needs TWO triples, A0,B_y,A1, not one
experiment measuring all four alternatives. Its first pair is the original
A0,B_y by causality of a retained record. Let d_y compare the second pair
with standalone B_y,A1, and r_y=Pr(A0=A1) in the triple. For signed outcomes,
    S_seq = E[(A0+A1)B0] + E[(A0-A1)B1],
    |S_seq| <= 2*r_0 + 2*(1-r_1).
Consequently |S|<=2+2*(d_0+d_1+r_0-r_1). A conservative version uses
|r_0-r_1|. Correlation/parity differences alone can replace the full TV
budgets for this CHSH functional. Comparing to A1,B_y in the opposite
causal order requires a separate order-invariance test (or an added error
budget); the existing source fixture is checked in BOTH orders here.
History-dependent postselection can spoil the causal-prefix premise. All
source trials here are retained; no detector-loss correction is claimed.

The routed journal below is NOT a new physical measurement instrument.
It records hidden tags after A0, B_y and A1 while continuing to propagate
the entire cloud WITHOUT collapse or backreaction. Both pair reductions
match the standalone routed tables, but Alice's hidden-history equality is
7/10 versus 3/10 as y changes. Thus S=14/5=2+2*(2/5). The existing fixture
checks single-bit no-signalling, not accessibility of this joint history.
Physical no-signalling would constrain EVERY accessible local record. This
calculation exposes why a nondisturbing local readout of the hidden history
cannot simply be assumed; it does not predict physical remote signalling.

Mixed-setting extension of the finite unread-insertion theorem:
For a supplied finite nonnegative instrument family K_x,a, require
mu K_u(P_x-I)K_v 1=0 for EVERY x and every MIXED prefix/suffix word.
Bases from the union of the K_x,a have dimension<=d and word length<=d-1.
Use the Cesaro projector of the AVERAGE Pbar=sum_x P_x/number_of_settings,
not just a cyclic product. Each closed class of Pbar is closed under every
K_x,a by nonnegativity. Independent unread-gap averaging therefore gives
one common mixture sum_c w_c product_j p_c,x_j,a_j. This is a conditional
analytical extension, not a Lean proof. Label individual alternatives as
settings: treating an entire joint context as one setting does NOT supply
Bell-local response factorization. Invariance only under whole cycles is
weaker; within-one-setting iid laws do not imply this mixed-context premise.

Exact rational finite controls, no empirical fit or uncertainty estimate.
No conclusion about physical iid, a stochastic origin, or QM closure.
Run: python3 -B -O -m scripts.probe_alternative_setting_gaps
"""

from __future__ import annotations

import sys
from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_cancellation_event_router import Cloud, Pair, pairs, route_block
from scripts.probe_routed_pair_bell import (
    A_FIRST,
    ANALYZERS,
    B_FIRST,
    RAILS,
    prepare,
    raw_counts,
    run_setting,
)
from scripts.probe_unread_tick_instruments import (
    Instrument,
    col_mul,
    dot,
    identity,
    mat_mul,
    mat_sub,
    record_probability,
    row_mul,
    unread_certificate,
    vector,
    word_basis,
)

PairTable = tuple[F, F, F, F]
Box = tuple[PairTable, PairTable, PairTable, PairTable]
Triple = tuple[int, int, int]  # (A0, B_y, A1)
TripleTable = dict[Triple, F]
Assignment = tuple[int, int, int, int]  # (A0,A1,B0,B1)
Joint = dict[Assignment, F]
SETTINGS = tuple((x, y) for x, y in product(range(2), repeat=2))
OUTCOMES = SETTINGS
ASSIGNMENTS: tuple[Assignment, ...] = tuple(
    (a0, a1, b0, b1) for a0, a1, b0, b1 in product(range(2), repeat=4)
)
TRIPLES: tuple[Triple, ...] = tuple(
    (a0, b, a1) for a0, b, a1 in product(range(2), repeat=3)
)
TARGET_CORRELATIONS = (F(3, 5), F(3, 5), F(4, 5), F(-4, 5))


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def sign(bit: int) -> int:
    need(bit in (0, 1), "binary outcome")
    return 1 - 2 * bit


def correlation(table: PairTable) -> F:
    need(all(p >= 0 for p in table) and sum(table, F(0)) == 1, "pair probabilities")
    return table[0] - table[1] - table[2] + table[3]


def tv(left: PairTable, right: PairTable) -> F:
    correlation(left)
    correlation(right)
    return sum((abs(a - b) for a, b in zip(left, right, strict=True)), F(0)) / 2


def chsh(box: Box) -> F:
    a, b, c, d = (correlation(table) for table in box)
    return a + b + c - d


def unbiased_box(correlations: tuple[F, F, F, F]) -> Box:
    tables = []
    for value in correlations:
        need(-1 <= value <= 1, "binary correlation range")
        tables.append(
            ((1 + value) / 4, (1 - value) / 4, (1 - value) / 4, (1 + value) / 4)
        )
    return tables[0], tables[1], tables[2], tables[3]


def marginal(joint: Joint, x: int, y: int) -> PairTable:
    need(
        all(p >= 0 for p in joint.values()) and sum(joint.values(), F(0)) == 1,
        "joint probabilities",
    )
    return tuple4(
        tuple(
            sum(
                (p for row, p in joint.items() if (row[x], row[2 + y]) == outcome), F(0)
            )
            for outcome in OUTCOMES
        )
    )


def tuple4(values: tuple[F, ...]) -> PairTable:
    need(len(values) == 4, "four-entry table")
    return values[0], values[1], values[2], values[3]


def joint_box(joint: Joint) -> Box:
    return (
        marginal(joint, 0, 0),
        marginal(joint, 0, 1),
        marginal(joint, 1, 0),
        marginal(joint, 1, 1),
    )


def local_joint(bad_edge_weights: tuple[F, F, F, F]) -> Joint:
    """Eight CHSH=+2 atoms, one failed CHSH edge and its global bit flip."""
    need(
        all(p >= 0 for p in bad_edge_weights) and sum(bad_edge_weights, F(0)) == 1,
        "bad-edge distribution",
    )
    result: Joint = {}
    for row in ASSIGNMENTS:
        edges = tuple(
            sign(row[x]) * sign(row[2 + y]) * (-1 if (x, y) == (1, 1) else 1)
            for x, y in SETTINGS
        )
        need(abs(sum(edges)) == 2, "deterministic CHSH magnitude")
        if sum(edges) == 2:
            result[row] = bad_edge_weights[edges.index(-1)] / 2
    need(chsh(joint_box(result)) == 2, "local facet construction")
    return result


def full_joint_bound(box: Box, joint: Joint) -> tuple[F, F, F, F]:
    reduced = joint_box(joint)
    gaps = tuple4(tuple(tv(p, q) for p, q in zip(box, reduced, strict=True)))
    need(abs(chsh(reduced)) <= 2, "common-joint CHSH")
    need(
        abs(chsh(box) - chsh(reduced)) <= 2 * sum(gaps, F(0)),
        "TV correlation continuity",
    )
    need(
        abs(chsh(box)) <= min(F(4), 2 + 2 * sum(gaps, F(0))), "four-context gap budget"
    )
    return gaps


def triple_pair(table: TripleTable, second: bool) -> PairTable:
    a_index = 2 if second else 0
    return tuple4(
        tuple(
            sum(
                (p for row, p in table.items() if (row[a_index], row[1]) == outcome),
                F(0),
            )
            for outcome in OUTCOMES
        )
    )


def history_equal(table: TripleTable) -> F:
    need(
        all(p >= 0 for p in table.values()) and sum(table.values(), F(0)) == 1,
        "triple distribution",
    )
    return sum((p for row, p in table.items() if row[0] == row[2]), F(0))


def history_table(table: TripleTable) -> PairTable:
    return tuple4(
        tuple(
            sum(
                (p for row, p in table.items() if (row[0], row[2]) == outcome),
                F(0),
            )
            for outcome in OUTCOMES
        )
    )


def sequential_box(tables: tuple[TripleTable, TripleTable]) -> Box:
    return (
        triple_pair(tables[0], False),
        triple_pair(tables[1], False),
        triple_pair(tables[0], True),
        triple_pair(tables[1], True),
    )


def triple_bound(box: Box, tables: tuple[TripleTable, TripleTable]) -> tuple[F, F, F]:
    sequential = sequential_box(tables)
    need(
        sequential[:2] == box[:2],
        "first pair must be the causal prefix; otherwise add its error budget",
    )
    d0, d1 = tv(box[2], sequential[2]), tv(box[3], sequential[3])
    delta = history_equal(tables[0]) - history_equal(tables[1])
    ceiling = 2 + 2 * delta
    need(abs(chsh(sequential)) <= ceiling, "two-triple binary identity")
    shift = chsh(box) - chsh(sequential)
    parity_budget = sum(
        (abs(correlation(box[j]) - correlation(sequential[j])) / 2 for j in (2, 3)),
        F(0),
    )
    need(
        abs(shift) <= 2 * parity_budget <= 2 * (d0 + d1),
        "parity-only disturbance budget",
    )
    need(
        abs(chsh(box)) <= ceiling + abs(shift) <= 2 + 2 * (d0 + d1 + abs(delta)),
        "operational alternative-setting bound",
    )
    need(abs(chsh(box)) <= 2 + 2 * (d0 + d1 + delta), "signed history contrast bound")
    return d0, d1, delta


def triples_from_joint(joint: Joint) -> tuple[TripleTable, TripleTable]:
    result = []
    for y in range(2):
        table: TripleTable = {}
        for row, p in joint.items():
            triple = (row[0], row[2 + y], row[1])
            table[triple] = table.get(triple, F(0)) + p
        result.append(table)
    return result[0], result[1]


def routed_journal(prep: tuple[Cloud, tuple[Pair, ...]], y: int) -> TripleTable:
    """Internal history probe only: no projection/collapse or readout added."""
    cloud, initial_tags = prep
    stages: list[tuple[Cloud, dict[tuple[Pair, int], Pair], int, int]] = []
    for party, setting in ((0, 0), (1, y), (0, 1)):
        cloud, routes, gain, _ = route_block(cloud, ANALYZERS[party][setting])
        stages.append((cloud, routes, gain, party))
    need(tuple(item[2] for item in stages) == (2, 5, 2), "source gate-gain contract")
    records: Counter[Triple] = Counter()
    exits: set[Pair] = set()
    for source, first, bob, last in product(range(2), range(2), range(5), range(2)):
        tag = initial_tags[source]
        values = []
        for (current_cloud, routes, _, party), seed in zip(
            stages, (first, bob, last), strict=True
        ):
            tag = routes[tag, seed]
            values.append(RAILS[current_cloud[tag[0]][0]][party])
        need(
            RAILS[cloud[tag[0]][0]][1] == values[1],
            "later local analyzer rewrote Bob's recorded bit",
        )
        need(tag not in exits, "duplicate final tag")
        exits.add(tag)
        records[values[0], values[1], values[2]] += 1
    need(
        exits == pairs(cloud) and records.total() == 40,
        "all 40 seed histories retained",
    )
    table = {record: F(count, 40) for record, count in records.items()}
    need(
        all(
            sum((p for row, p in table.items() if row[index] == 0), F(0)) == F(1, 2)
            for index in range(3)
        ),
        "individual recorded bits remain fair",
    )
    print(
        f"Hidden journal y={y}: {dict(sorted(records.items()))}; Pr(A0=A1)={history_equal(table)}."
    )
    return table


def isotropic_controls() -> None:
    for visibility in (F(0), F(1, 4), F(1, 2), F(3, 5), F(7, 10), F(1)):
        box = unbiased_box((visibility, visibility, visibility, -visibility))
        if visibility < F(1, 2):
            facet = local_joint((F(1, 4),) * 4)
            joint = {
                row: 2 * visibility * facet.get(row, F(0)) + (1 - 2 * visibility) / 16
                for row in ASSIGNMENTS
            }
            need(joint_box(joint) == box, "local isotropic regime")
        else:
            # Preserve both A0 pairs; move only the two A1 pairs to the facet.
            joint = local_joint(
                (
                    (1 - visibility) / 2,
                    (1 - visibility) / 2,
                    visibility / 2,
                    visibility / 2,
                )
            )
        gaps = full_joint_bound(box, joint)
        d0, d1, delta = triple_bound(box, triples_from_joint(joint))
        need(delta == 0, "local joint history independent of Bob setting")
        if visibility >= F(1, 2):
            need(gaps[:2] == (F(0), F(0)), "causal-prefix pair preservation")
            need(d0 == d1 == visibility - F(1, 2), "sharp two-gap isotropic budget")
            need(
                chsh(box) == 2 + 2 * sum(gaps, F(0)) == 2 + 2 * (d0 + d1),
                "sharp isotropic bound",
            )
        else:
            need(
                sum(gaps, F(0)) == d0 == d1 == 0,
                "no disturbance needed for local isotropic box",
            )
    # Every pair of deterministic triple laws is an extreme-point control
    # of the binary identity, including negative r0-r1 and its endpoints.
    for first, second in product(TRIPLES, repeat=2):
        tables = ({first: F(1)}, {second: F(1)})
        seq = sequential_box(tables)
        need(
            abs(chsh(seq))
            <= 2 + 2 * (history_equal(tables[0]) - history_equal(tables[1])),
            "all 64 deterministic triple pairs",
        )
    print(
        "Six isotropic regimes (white noise through PR endpoint), all 16 local assignments, and 64 deterministic triple pairs checked."
    )


def mixed_setting_controls() -> None:
    mu = vector(F(1, 2), F(1, 2))
    write = Instrument(
        (
            (vector(F(1, 2), 0), vector(F(1, 2), 0)),
            (vector(0, F(1, 2)), vector(0, F(1, 2))),
        ),
        mu,
    )
    read = Instrument(
        (
            (vector(F(1, 2), F(1, 2)), vector(0, 0)),
            (vector(0, 0), vector(F(1, 2), F(1, 2))),
        ),
        mu,
    )
    for instrument in (write, read):
        need(
            unread_certificate(instrument).invariant, "single-setting unread invariance"
        )
        need(row_mul(mu, instrument.transition) == mu, "common stationary preparation")
        for length in range(6):
            for word in product(range(2), repeat=length):
                need(
                    record_probability(instrument, word) == F(1, 2**length),
                    "within-setting iid fair control",
                )

    def equal_after(first: Instrument, second: Instrument) -> F:
        return sum(
            (
                sum(row_mul(row_mul(mu, first.kernels[a]), second.kernels[a]), F(0))
                for a in range(2)
            ),
            F(0),
        )

    need(
        equal_after(write, read) == 1 and equal_after(read, write) == F(1, 2),
        "mixed-setting order contrast",
    )
    all_kernels = write.kernels + read.kernels
    rows = word_basis(mu, all_kernels, "row")
    columns = word_basis(vector(1, 1), all_kernels, "column")
    difference = mat_sub(write.transition, identity(2))
    failures = [
        dot(row_mul(row.value, difference), column.value)
        for row in rows
        for column in columns
    ]
    need(any(failures), "mixed-word basis must reject the stronger insertion premise")
    direct = dot(
        row_mul(mu, write.kernels[0]),
        col_mul(difference, col_mul(read.kernels[0], vector(1, 1))),
    )
    need(direct == F(-1, 4), "one unread tick breaks the write/read correlation")

    alternating = Instrument(
        ((vector(0, 1), vector(0, 0)), (vector(0, 0), vector(1, 0))), mu
    )
    need(
        mat_mul(alternating.transition, alternating.transition) == identity(2),
        "whole unread two-setting cycle is invisible",
    )
    need(
        not unread_certificate(alternating).invariant,
        "whole-cycle invariance is weaker",
    )
    need(
        record_probability(alternating, (0, 0)) == 0, "cyclic block does not yield iid"
    )
    print(
        "Single-setting iid and common stationarity coexist with Pr(equal|write,read)=1 versus 1/2 in reverse order."
    )
    print(
        "Mixed-context finite basis rejects insertion (witness -1/4); whole-cycle identity alone also fails to imply iid."
    )


def run() -> None:
    prep = prepare(True)
    source_tables = []
    for setting in SETTINGS:
        ab = raw_counts(run_setting(prep, setting, A_FIRST))
        ba = raw_counts(run_setting(prep, setting, B_FIRST))
        need(ab == ba, "standalone order control required for this comparison")
        source_tables.append(tuple4(tuple(F(count, 20) for count in ab)))
    box: Box = (source_tables[0], source_tables[1], source_tables[2], source_tables[3])
    need(
        box == unbiased_box(TARGET_CORRELATIONS) and chsh(box) == F(14, 5),
        "existing routed Bell source",
    )
    tables = (routed_journal(prep, 0), routed_journal(prep, 1))
    d0, d1, delta = triple_bound(box, tables)
    need(
        (d0, d1, delta) == (F(0), F(0), F(2, 5)),
        "hidden history contrast, not pair disturbance",
    )
    need(
        history_equal(tables[0]) == F(7, 10) and history_equal(tables[1]) == F(3, 10),
        "exact hidden parity rates",
    )
    need(chsh(box) == 2 + 2 * delta, "native journal saturates the two-triple bound")
    need(
        tv(history_table(tables[0]), history_table(tables[1])) == delta == F(2, 5),
        "full hidden-history TV equals the parity contrast",
    )
    joint = local_joint((F(1, 5), F(1, 5), F(3, 10), F(3, 10)))
    gaps = full_joint_bound(box, joint)
    alternative = triple_bound(box, triples_from_joint(joint))
    need(gaps == (F(0), F(0), F(1, 5), F(1, 5)), "sharp native local-joint distance")
    need(
        alternative == (F(1, 5), F(1, 5), F(0)),
        "same cost can occur as local incompatibility",
    )
    print("Routed S=14/5: hidden journal has (d0,d1,history contrast)=(0,0,2/5).")
    print(
        "Explicit local comparison instead has (1/5,1/5,0); minimum summed pair-TV distance is exactly 2/5."
    )
    isotropic_controls()
    mixed_setting_controls()
    print(
        "No physical access to hidden histories, no new signalling prediction, no empirical uncertainty estimate or Lean-proof claim."
    )


if __name__ == "__main__":
    run()
