"""A designed phase-program question for two supplied four-port conference stages.

Only the baseline even first-hit table is taken from the raw junction. The
gradient and two-shot laws below are alternative comparator experiments, not
native controls or measurements. Matrix indexing here is [output][input].
Run: python3 -m scripts.probe_phase_gradient_tomography
"""

import json
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations

if __package__:
    from . import probe_raw_bond_junction_rates as raw
else:
    import probe_raw_bond_junction_rates as raw


def require(test, message):
    if not test:
        raise ValueError(message)


@dataclass(frozen=True)
class PhaseNumber:
    """(a + bi) + (c + di)√3; the three-context sharpness witness needs √3."""

    a: F = 0
    b: F = 0
    c: F = 0
    d: F = 0

    def __add__(self, other):
        return PhaseNumber(
            self.a + other.a, self.b + other.b, self.c + other.c, self.d + other.d
        )

    def __mul__(self, other):
        a, b, c, d = self.a, self.b, self.c, self.d
        e, f, g, h = other.a, other.b, other.c, other.d
        return PhaseNumber(
            a * e - b * f + 3 * (c * g - d * h),
            a * f + b * e + 3 * (c * h + d * g),
            a * g - b * h + c * e - d * f,
            a * h + b * g + c * f + d * e,
        )

    def scale(self, s):
        return PhaseNumber(s * self.a, s * self.b, s * self.c, s * self.d)

    def conj(self):
        return PhaseNumber(self.a, -self.b, self.c, -self.d)

    def rational(self):
        require(self.b == self.c == self.d == 0, "expected a rational observable")
        return F(self.a)


PORTS = range(4)
PAIRS = tuple(combinations(PORTS, 2))
ZERO, ONE, I = PhaseNumber(), PhaseNumber(1), PhaseNumber(0, 1)
W = PhaseNumber(F(3, 5), F(4, 5))
GRADIENT = (ONE, W, W * W, W * W * W)
BASELINE = (ONE,) * 4
OMEGA = PhaseNumber(F(-1, 2), d=F(1, 2))
TWO = ((F(1, 2), (ONE, I, ONE, I)), (F(1, 2), (ONE, I, ONE.scale(-1), I.scale(-1))))
FOUR = tuple(
    (F(1, 4), tuple(ONE.scale((-1) ** ((r & j).bit_count())) for j in PORTS))
    for r in PORTS
)


def native_fixture():
    native = raw.report()
    rows = [
        row
        for row in native["literal"]
        if (row["law"], row["offset"], row["length"]) == ("free", 6, 14)
    ]
    require(sorted(row["input"] for row in rows) == list(PORTS), "missing native input")
    require(
        tuple(native["outcomes"]) == ("0", "1", "2", "3", "jam", "trap")
        and tuple(native["arm_order"]) == raw.ARMS,
        "unexpected native labels",
    )
    masses = [
        tuple(map(F, row["mass"])) for row in sorted(rows, key=lambda r: r["input"])
    ]
    require(
        all(
            len(m) == 6 and m[-2:] == (0, 0) and min(m) >= 0 and sum(m) == 1
            for m in masses
        ),
        "lossy or invalid native measure",
    )
    return native["comparison"]["supplied_C"], tuple(
        zip(*(m[:4] for m in masses), strict=True)
    )


def valid_phases(vector):
    require(
        len(vector) == 4 and all(z * z.conj() == ONE for z in vector),
        "need four unit phases",
    )


def valid_law(law):
    require(
        all(isinstance(prob, (int, F)) and prob > 0 for prob, _ in law)
        and sum(prob for prob, _ in law) == 1,
        "need exact positive normalized law",
    )
    for _, phases in law:
        valid_phases(phases)


def correlations(law):
    """Upper-triangle entries of Γ=E[ZZ*]; diagonal one and reflection understood."""
    valid_law(law)
    return {
        (k, l): sum(((z[k] * z[l].conj()).scale(p) for p, z in law), ZERO)
        for k, l in PAIRS
    }


def table(c, law, gradient=BASELINE):
    """Evaluate every cell as E|C diag(gradient * Z) C / 3|², including diagonals.

    Do not use the pair inversion here: this is the independent forward check.
    Individual three-point Fourier rows can have irrational responses; convert
    only *after* averaging. All ensemble tables tested here are rational.
    """
    valid_law(law)
    valid_phases(gradient)
    result = [[ZERO for _ in PORTS] for _ in PORTS]
    for prob, phases in law:
        tilted = [z * g for z, g in zip(phases, gradient, strict=True)]
        for i in PORTS:
            for j in PORTS:
                amplitude = sum(
                    (tilted[k].scale(c[i][k] * c[k][j]) for k in PORTS), ZERO
                )
                result[i][j] = result[i][j] + (amplitude * amplitude.conj()).scale(
                    F(prob, 9)
                )
    return tuple(tuple(x.rational() for x in row) for row in result)


def recover(base, tilted, program, inputs):
    """Invert only measured off-diagonal cells; no access to unselected inputs.

    q_ij=(2−2 Re Γ_kl)/9. In the second setting Γ_kl is multiplied
    by u=g_k conj(g_l), so its two real projections fix its imaginary
    part precisely when Im u != 0. Reflected observations must agree.
    """
    valid_phases(program)
    entries = {}
    for j in inputs:
        require(j in PORTS, "unknown input")
        for i in PORTS:
            if i == j:
                continue
            k, l = sorted(set(PORTS) - {i, j})
            u = program[k] * program[l].conj()
            require(
                u.c == u.d == 0 and u.b != 0, "nonidentifying or non-Gaussian program"
            )
            x = 1 - F(9, 2) * base[i][j]
            projection = 1 - F(9, 2) * tilted[i][j]
            entry = PhaseNumber(x, (u.a * x - projection) / u.b)
            pair = k, l
            require(
                pair not in entries or entries[pair] == entry,
                "reflected cells disagree",
            )
            entries[pair] = entry
    return entries


def three_contexts(a, b):
    """Assign X,iX to tested labels; X,Y,Z are the three orthogonal Fourier columns."""
    require(a in PORTS and b in PORTS and a != b, "need two distinct input labels")
    x, y = sorted(set(PORTS) - {a, b})
    rows = []
    for phase in (ONE, OMEGA, OMEGA * OMEGA):
        row = [ONE] * 4
        row[b], row[x], row[y] = I, phase, phase * phase
        rows.append((F(1, 3), tuple(row)))
    return tuple(rows)


def report():
    c, target = native_fixture()
    tilted = table(c, TWO, GRADIENT)
    require(
        table(c, TWO) == table(c, FOUR) == table(c, FOUR, GRADIENT) == target,
        "baseline alias or fully dephased control failed",
    )
    two = correlations(TWO)
    require(
        two
        == {pair: I.scale(-1) if pair in ((0, 1), (2, 3)) else ZERO for pair in PAIRS},
        "two-context Gram mismatch",
    )
    require(
        recover(target, tilted, GRADIENT, PORTS) == two,
        "gradient failed full inversion",
    )
    gap = tilted[2][3] - target[2][3]
    require(gap == F(8, 45), "incorrect separating response")
    sines = tuple(z.b for z in GRADIENT[1:])
    require(sines == (F(4, 5), F(24, 25), F(44, 125)), "aliased gradient")
    for n, coverage in enumerate((0, 3, 5, 6, 6)):
        for inputs in combinations(PORTS, n):
            entries = recover(target, target, GRADIENT, inputs)
            require(
                len(entries) == coverage and all(z == ZERO for z in entries.values()),
                "incorrect flat-column certificate",
            )
    for a, b in PAIRS:
        law = three_contexts(a, b)
        base3, tilted3 = table(c, law), table(c, law, GRADIENT)
        measured = recover(base3, tilted3, GRADIENT, PORTS)
        require(
            base3 == target
            and measured == correlations(law)
            and all(
                measured[q] == (I.scale(-1) if q == (a, b) else ZERO) for q in PAIRS
            ),
            "three-context sharpness control failed",
        )
        require(
            all(
                (all(row[j] == target[i][j] for i, row in enumerate(tilted3)))
                == (j in (a, b))
                for j in PORTS
            ),
            "wrong visible columns",
        )
    # Here both shots use the SAME bare cell and no applied gradient. No
    # conditional emission or inter-shot persistence is measured by the native table.
    hits = [table(c, ((F(1), z),))[1][3] for _, z in TWO]
    shared = sum(p * h * h for (p, _), h in zip(TWO, hits, strict=True))
    iid = sum(p * h for (p, _), h in zip(TWO, hits, strict=True)) ** 2
    require(
        hits == [0, F(4, 9)] and (shared, iid) == (F(8, 81), F(4, 81)),
        "two-shot comparator failed",
    )
    return {
        "scope": "Designed conditional comparator, not a native phase program or observed "
        "response. Both conference stages, alignment, known gradient and one common "
        "phase law across inputs and settings are supplied. No QM or physical claim.",
        "baseline": {
            "raw": "free, offset=6, length=14; indexed [output][input]",
            "table": [[str(v) for v in row] for row in target],
            "two_context_nonzero_pairs": {"01": "-i", "23": "-i"},
            "four_context_off_diagonal_gram": "zero",
        },
        "gradient": {
            "base_step": "(3+4i)/5",
            "powers": [0, 1, 2, 3],
            "sines": list(map(str, sines)),
            "input": 3,
            "output": 2,
            "two_context_before_after": [str(target[2][3]), str(tilted[2][3])],
            "difference": str(gap),
            "four_context_table_unchanged": True,
        },
        "flat_columns": {
            "offdiagonal_pairs_by_input_count": [0, 3, 5, 6, 6],
            "one": "Complementary 3x3 principal Gram = I3; at least three discrete contexts.",
            "two": "Five pairs only. For every input pair, three equiprobable Fourier contexts "
            "retain -i on precisely that missing pair and match both complete columns.",
            "three": "All six pairs: Γ=I4 iff these three gradient columns and baseline equal "
            "the target under the comparator. Four discrete contexts necessary and "
            "sufficient: each weighted outer product has rank one; Hadamard attains.",
            "limits": "The bound is on finite discrete support, not the number of possible "
            "laws. Continuous laws are allowed; no independence over time follows.",
        },
        "two_shot": {
            "input": 3,
            "output": 1,
            "gradient_applied": False,
            "conditional_hit_probabilities": list(map(str, hits)),
            "shared": str(shared),
            "iid": str(iid),
            "assumptions": "Repeated identical input; emissions independent given "
            "the phase draws. One shared draw versus two iid draws, "
            "not predictions for the native raw process.",
        },
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, ensure_ascii=False))
