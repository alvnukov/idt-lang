"""Finite residue obstructions are NOT lifted qutrit contextuality proofs.

For R5=Z[i,1/2,1/5], an inert prime p=3 or 7 permits reduction to
F_(p^2), with conjugation a+bi -> a-bi. A normalized ray cannot reduce
to zero or an isotropic ray. Norm-one projective gauge changes reduce to
nonzero scalars, so the residue line is well defined. An orthonormal basis
reduces to three DISTINCT orthogonal residue lines. Consequently an exact
one-per-basis 0/1 valuation of the finite graph WOULD pull back to every
lossless projective R5 context. The converse is false: a valuation upstairs
need not be constant on residue fibers, and finite residue incidences need
not lift using one consistent representative per ray.

Over F_(p^2), every nonzero field norm has a scalar inverse norm, so ALL
nonisotropic projective lines are unit-normalizable. Their number is
p^2(p^2-p+1). Each has p(p-1) orthogonal neighbors, paired uniquely into
bases, hence p(p-1)/2 incident bases. The code enumerates the lines and
orthogonal two-planes directly, not all matrices or unbounded gate words.

p=3: 63 rays, 63 bases, three bases through every ray. Exact-one valuation
search is UNSAT in 15 bounded backtracking nodes after fixing e1=1.
This symmetry choice is valid because the coordinate basis must select one
axis and coordinate permutations preserve every context (checked). Each
node propagates forced assignments or branches over ALL possible selected
rays in one unresolved basis; no external solver or heuristic cutoff result
is used as a certificate. A hard node cap raises an error, not UNSAT.

The p=3 orthogonality graph has NO cycle with five distinct vertices. Yet
native dyadic T/i alone reach every one of its 63 rays and 63 bases, and
z5=(3+4i)/5 reduces merely to -i. This residue cannot distinguish the
dyadic from the added-prime-5 control set. Surjectivity onto residue contexts
is NOT a coherent lift of their shared-ray identifications.

p=7: 2107 rays, 21 incident bases per ray, 14749 bases. A valuation would
require 21*selected=14749, impossible. The optional bounded enumeration
checks these counts and full native T/i coverage; no large valuation search
is needed. It also checks a residue C5 using the integer direction
(-1,-1,1), whose norm 3 forbids Gaussian-rational unit normalization in
characteristic zero. This is a residue witness, not a consistent R5 lift.
More generally
the uniform incidence count excludes p=7 mod 12 by nonintegral n/3.
No claim is made about all inert primes, in particular p=11 mod 12.

Two explicit safeguards against wrong lifting conclusions are checked:
  * Distinct R5 unit rays (1,1,0)/pi and (i*z5,1,0)/pi share a residue.
  * The genuine rational-unit pentagon with directions
    e1,e2,(4,0,3),(-3,-3,4),(0,4,3), using primes 5 AND 17, reduces to
    (e1,e2,e1,e3,e2). Thus a residue's lack of distinct C5s is not a
    general obstruction to a characteristic-zero pentagon. This comparator
    is not an R5-only witness. The asymmetric R5 pentagon remains OPEN.

REAL SUBCASE: normalized coordinatewise-real R5 vectors reduce modulo 3
only to the three axes: a sum of three squares is 1 mod 3 only when exactly
one coordinate is nonzero. Axis coloring therefore DOES pull back to this
restricted real normalized-coordinate theory. This is not all rational
real directions with Gaussian normalization, nor the full rational sphere
with arbitrary denominators, nor the Gaussian R5 sphere. In F3 a nonzero
quadratic norm need not be rescalable to one; that distinction is checked.

SPLIT-PRIME CAVEAT: no unital reduction R5 -> characteristic 5 exists,
since 5 is inverted. If 5 is NOT inverted (e.g. the dyadic ring), reducing
Z[i] modulo 5 gives F5 x F5, with conjugation swapping factors. Selecting
one root i=2 or i=-2 alone does not preserve conjugation. It must not be
treated as the inert Hermitian finite field used here.

These are exact finite controls and mathematical arguments, not Lean proofs,
a new physical readout principle, or a proof of contextuality of R5 gates.
Related source context: probe_native_qutrit_frames.py and
probe_native_rational_pentagon.py; no status or registry is changed.

Run: python3 -B -O -m scripts.probe_qutrit_residue_frames
Optional: --include-seven (2107 rays and 14749 bases, no SAT search).
"""

from __future__ import annotations

import argparse
import sys
from collections import deque
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import ONE, PI, ZERO, Gaussian, g

Scalar = tuple[int, int]
Ray = tuple[Scalar, Scalar, Scalar]
Basis = tuple[int, int, int]
QRay = tuple[Gaussian, Gaussian, Gaussian]


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError(reason)


@dataclass(frozen=True)
class Field:
    p: int

    def __post_init__(self) -> None:
        need(self.p in (3, 7), "only the two declared inert-prime cases are supported")

    @property
    def elements(self) -> tuple[Scalar, ...]:
        return tuple((a, b) for a in range(self.p) for b in range(self.p))

    def add(self, a: Scalar, b: Scalar) -> Scalar:
        return (a[0] + b[0]) % self.p, (a[1] + b[1]) % self.p

    def neg(self, a: Scalar) -> Scalar:
        return -a[0] % self.p, -a[1] % self.p

    def sub(self, a: Scalar, b: Scalar) -> Scalar:
        return self.add(a, self.neg(b))

    def mul(self, a: Scalar, b: Scalar) -> Scalar:
        return (a[0] * b[0] - a[1] * b[1]) % self.p, (
            a[0] * b[1] + a[1] * b[0]
        ) % self.p

    def star(self, a: Scalar) -> Scalar:
        return a[0], -a[1] % self.p

    def norm(self, a: Scalar) -> int:
        return (a[0] ** 2 + a[1] ** 2) % self.p

    def inv(self, a: Scalar) -> Scalar:
        scale = pow(self.norm(a), -1, self.p)
        return self.mul((scale, 0), self.star(a))

    def dot(self, v: Ray, w: Ray) -> Scalar:
        value = (0, 0)
        for a, b in zip(v, w, strict=True):
            value = self.add(value, self.mul(self.star(a), b))
        return value

    def scale(self, c: Scalar, v: Ray) -> Ray:
        return self.mul(c, v[0]), self.mul(c, v[1]), self.mul(c, v[2])

    def canonical(self, v: Ray) -> Ray:
        return self.scale(self.inv(next(z for z in v if z != (0, 0))), v)

    def cross(self, v: Ray, w: Ray) -> Ray:
        return (
            self.star(self.sub(self.mul(v[1], w[2]), self.mul(v[2], w[1]))),
            self.star(self.sub(self.mul(v[2], w[0]), self.mul(v[0], w[2]))),
            self.star(self.sub(self.mul(v[0], w[1]), self.mul(v[1], w[0]))),
        )

    def rational(self, z: Gaussian) -> Scalar:
        def reduce(x: F) -> int:
            need(
                x.denominator % self.p != 0,
                "denominator is not reducible at this prime",
            )
            return x.numerator * pow(x.denominator, -1, self.p) % self.p

        return reduce(z.re), reduce(z.im)

    def reduce_ray(self, v: QRay) -> Ray:
        return self.canonical(
            (self.rational(v[0]), self.rational(v[1]), self.rational(v[2]))
        )


AXES: tuple[Ray, Ray, Ray] = (
    ((1, 0), (0, 0), (0, 0)),
    ((0, 0), (1, 0), (0, 0)),
    ((0, 0), (0, 0), (1, 0)),
)


def projective_lines(field: Field) -> tuple[Ray, ...]:
    zero, one = (0, 0), (1, 0)
    candidates = (
        tuple((one, a, b) for a, b in product(field.elements, repeat=2))
        + tuple((zero, one, a) for a in field.elements)
        + ((zero, zero, one),)
    )
    return tuple(sorted(v for v in candidates if field.dot(v, v) != zero))


def neighbors(field: Field, v: Ray) -> tuple[Ray, ...]:
    """Enumerate the q^2+1 projective lines in one orthogonal two-plane."""
    pivot = next(j for j, z in enumerate(v) if z != (0, 0))
    denominator = field.inv(field.star(v[pivot]))
    spanning: list[Ray] = []
    for j in range(3):
        if j == pivot:
            continue
        u = [(0, 0)] * 3
        u[j] = (1, 0)
        u[pivot] = field.neg(field.mul(field.star(v[j]), denominator))
        spanning.append((u[0], u[1], u[2]))
    a, b = spanning
    candidates = [b]
    for scalar in field.elements:
        candidates.append(
            (
                field.add(a[0], field.mul(scalar, b[0])),
                field.add(a[1], field.mul(scalar, b[1])),
                field.add(a[2], field.mul(scalar, b[2])),
            )
        )
    result = tuple(
        sorted(field.canonical(w) for w in candidates if field.dot(w, w) != (0, 0))
    )
    need(len(result) == len(set(result)), "duplicate plane rays")
    need(all(field.dot(v, w) == (0, 0) for w in result), "nonorthogonal neighbor")
    return result


@dataclass(frozen=True)
class Frames:
    field: Field
    rays: tuple[Ray, ...]
    adjacent: tuple[frozenset[int], ...]
    bases: tuple[Basis, ...]


def enumerate_frames(p: int) -> Frames:
    field = Field(p)
    rays = projective_lines(field)
    index = {v: j for j, v in enumerate(rays)}
    need(len(rays) == p * p * (p * p - p + 1), "nonisotropic line count")
    # All nonisotropic lines, not only one norm class, are unit-normalizable.
    inverse_norms: dict[int, Scalar] = {}
    for scalar in field.elements:
        if field.norm(scalar):
            inverse_norms[pow(field.norm(scalar), -1, p)] = scalar
    need(len(inverse_norms) == p - 1, "field norm not onto")
    for v in rays:
        n = field.dot(v, v)
        need(n[1] == 0 and n[0] != 0, "Hermitian norm")
        need(
            field.dot(
                field.scale(inverse_norms[n[0]], v), field.scale(inverse_norms[n[0]], v)
            )
            == (1, 0),
            "unit normalization",
        )
    adjacent = tuple(frozenset(index[w] for w in neighbors(field, v)) for v in rays)
    need(all(len(row) == p * (p - 1) for row in adjacent), "neighbor degree")
    bases: set[Basis] = set()
    for j, row in enumerate(adjacent):
        for k in row:
            need(j in adjacent[k], "asymmetric orthogonality")
            third = index[field.canonical(field.cross(rays[j], rays[k]))]
            ids = sorted((j, k, third))
            need(len(set(ids)) == 3 and third in row & adjacent[k], "basis completion")
            bases.add((ids[0], ids[1], ids[2]))
    incidence = [0] * len(rays)
    for base in bases:
        for j in base:
            incidence[j] += 1
    need(set(incidence) == {p * (p - 1) // 2}, "nonuniform basis incidence")
    need(len(bases) * 3 == len(rays) * p * (p - 1) // 2, "basis count")
    return Frames(field, rays, adjacent, tuple(sorted(bases)))


def root_symmetry(frames: Frames) -> int:
    index = {v: j for j, v in enumerate(frames.rays)}
    root = tuple(sorted(index[v] for v in AXES))
    need(root in frames.bases, "missing root basis")
    bases = set(frames.bases)
    for perm in permutations(range(3)):
        action = tuple(
            index[frames.field.canonical((v[perm[0]], v[perm[1]], v[perm[2]]))]
            for v in frames.rays
        )
        moved = {tuple(sorted(action[j] for j in base)) for base in bases}
        need(moved == bases, "coordinate permutation not a context automorphism")
    return index[AXES[0]]


def valuation_search(
    frames: Frames, cap: int = 1000
) -> tuple[tuple[int, ...] | None, int, int]:
    """Exact-one exhaustive branching. A cap hit is an ERROR, never UNSAT."""
    root = root_symmetry(frames)
    nodes, conflicts = 0, 0

    def visit(state: list[int]) -> tuple[int, ...] | None:
        nonlocal nodes, conflicts
        nodes += 1
        need(nodes <= cap, "valuation node cap exceeded; result is unknown")
        changed = True
        while changed:
            changed = False
            for base in frames.bases:
                selected = sum(state[j] == 1 for j in base)
                unknown = [j for j in base if state[j] < 0]
                if selected > 1 or (selected == 0 and not unknown):
                    conflicts += 1
                    return None
                if selected == 1:
                    for j in unknown:
                        state[j], changed = 0, True
                elif len(unknown) == 1:
                    state[unknown[0]], changed = 1, True
        unresolved = [
            tuple(j for j in base if state[j] < 0)
            for base in frames.bases
            if all(state[j] != 1 for j in base)
        ]
        if not unresolved:
            need(
                all(sum(state[j] for j in base) == 1 for base in frames.bases),
                "invalid valuation",
            )
            return tuple(state)
        choice = min(unresolved, key=lambda ids: (len(ids), ids))
        need(len(choice) >= 2, "propagation did not close")
        for selected_ray in choice:
            child = state.copy()
            for j in choice:
                child[j] = int(j == selected_ray)
            result = visit(child)
            if result is not None:
                return result
        return None

    state = [-1] * len(frames.rays)
    state[root] = 1
    result = visit(state)
    return result, nodes, conflicts


def distinct_five_cycles(frames: Frames) -> int:
    need(len(frames.rays) <= 63, "cycle enumeration is restricted to the small graph")
    count = 0
    adjacent = frames.adjacent
    for a in range(len(adjacent)):
        for b in adjacent[a]:
            for c in adjacent[b] - {a}:
                for d in adjacent[c] - {a, b}:
                    count += len((adjacent[d] & adjacent[a]) - {b, c})
    need(count % 10 == 0, "five-cycle orientation count")
    return count // 10


def native_orbit(frames: Frames) -> tuple[int, int]:
    field = frames.field
    index = {v: j for j, v in enumerate(frames.rays)}
    half = field.inv((2, 0))
    diagonal = field.mul((1, 1), half)
    cross = field.mul((1, field.p - 1), half)
    operations = [("i", j, j) for j in range(3)] + [
        ("T", j, k) for j in range(3) for k in range(j + 1, 3)
    ]
    actions: list[tuple[int, ...]] = []
    for tag, j, k in operations:
        action = []
        for v in frames.rays:
            w = list(v)
            if tag == "i":
                w[j] = field.mul((0, 1), v[j])
            else:
                w[j] = field.add(field.mul(diagonal, v[j]), field.mul(cross, v[k]))
                w[k] = field.add(field.mul(cross, v[j]), field.mul(diagonal, v[k]))
            action.append(index[field.canonical((w[0], w[1], w[2]))])
        need(len(set(action)) == len(frames.rays), "native operation not a permutation")
        actions.append(tuple(action))
    root_ids = sorted(index[v] for v in AXES)
    root: Basis = (root_ids[0], root_ids[1], root_ids[2])
    seen, queue = {root}, deque((root,))
    all_bases = set(frames.bases)
    while queue:
        base = queue.popleft()
        for permutation in actions:
            ids = sorted(permutation[j] for j in base)
            target: Basis = (ids[0], ids[1], ids[2])
            need(target in all_bases, "native action did not preserve a basis")
            if target not in seen:
                seen.add(target)
                queue.append(target)
    ray_seen = {index[AXES[0]]}
    ray_queue = deque(ray_seen)
    while ray_queue:
        ray = ray_queue.popleft()
        for permutation in actions:
            target_ray = permutation[ray]
            if target_ray not in ray_seen:
                ray_seen.add(target_ray)
                ray_queue.append(target_ray)
    need(
        ray_seen == {j for base in seen for j in base},
        "fixed-axis and basis ray orbits differ",
    )
    return len(ray_seen), len(seen)


def qdivide(z: Gaussian, w: Gaussian) -> Gaussian:
    product0 = z * w.star()
    return g(product0.re / w.norm2(), product0.im / w.norm2())


def qnorm(v: QRay) -> F:
    return sum((z.norm2() for z in v), F(0))


def lift_controls() -> None:
    field = Field(3)
    z5, imaginary = g(F(3, 5), F(4, 5)), g(0, 1)
    need(field.rational(z5) == (0, 2), "phase-5 residue")
    first: QRay = (qdivide(ONE, PI), qdivide(ONE, PI), ZERO)
    second: QRay = (imaginary * z5 * first[0], first[1], ZERO)
    need(qnorm(first) == qnorm(second) == 1, "fiber-control normalization")
    need(
        first[0] * second[1] != first[1] * second[0],
        "fiber rays were projectively equal",
    )
    need(field.reduce_ray(first) == field.reduce_ray(second), "fiber did not coalesce")
    middle = tuple(qdivide(g(x), g(5, 3)) for x in (-3, -3, 4))
    rays: tuple[QRay, ...] = (
        (ONE, ZERO, ZERO),
        (ZERO, ONE, ZERO),
        (g(F(4, 5)), ZERO, g(F(3, 5))),
        (middle[0], middle[1], middle[2]),
        (ZERO, g(F(4, 5)), g(F(3, 5))),
    )
    for j, v in enumerate(rays):
        w = rays[(j + 1) % 5]
        need(qnorm(v) == 1, "pentagon unit normalization")
        need(
            sum((x.star() * y for x, y in zip(v, w, strict=True)), ZERO) == ZERO,
            "pentagon edge",
        )
        third: QRay = (
            (v[1] * w[2] - v[2] * w[1]).star(),
            (v[2] * w[0] - v[0] * w[2]).star(),
            (v[0] * w[1] - v[1] * w[0]).star(),
        )
        need(qnorm(third) == 1, "pentagon context completion")
    need(len(set(rays)) == 5, "pentagon vertices")
    need(
        tuple(field.reduce_ray(v) for v in rays)
        == (AXES[0], AXES[1], AXES[0], AXES[2], AXES[1]),
        "collapsed pentagon",
    )


def real_and_split_controls() -> None:
    normalized: set[tuple[int, int, int]] = set()
    nonsquare_norm = False
    for v in product(range(3), repeat=3):
        n = sum(x * x for x in v) % 3
        if n == 2:
            nonsquare_norm = True
            need(
                all(sum((s * x) ** 2 for x in v) % 3 != 1 for s in (1, 2)),
                "real norm-class caveat",
            )
        if n == 1:
            scale = pow(next(x for x in v if x), -1, 3)
            normalized.add((scale * v[0] % 3, scale * v[1] % 3, scale * v[2] % 3))
    need(
        nonsquare_norm and normalized == {(1, 0, 0), (0, 1, 0), (0, 0, 1)},
        "real residue axes",
    )
    # i -> 2 kills (2-i), but does not kill its conjugate (2+i).
    need((2 - 2) % 5 == 0 and (2 + 2) % 5 != 0, "split quotient star failure")
    for a, b in product(range(5), repeat=2):
        factors = ((a + 2 * b) % 5, (a - 2 * b) % 5)
        conjugate = ((a - 2 * b) % 5, (a + 2 * b) % 5)
        need(conjugate == factors[::-1], "split conjugation must exchange factors")
        need(factors[0] * factors[1] % 5 == (a * a + b * b) % 5, "split norm")
    need(all(5 * x % 5 == 0 for x in range(5)), "inverted 5 cannot map to a unit")


def solver_controls(frames: Frames) -> None:
    toy = Frames(
        Field(3),
        AXES,
        tuple(frozenset(k for k in range(3) if k != j) for j in range(3)),
        ((0, 1, 2),),
    )
    valuation, nodes, conflicts = valuation_search(toy)
    need(
        valuation == (1, 0, 0) and nodes == 1 and conflicts == 0,
        "positive valuation control",
    )
    try:
        valuation_search(frames, cap=0)
    except ValueError as error:
        need("cap exceeded" in str(error), "wrong bounded-search failure")
    else:
        raise ArithmeticError("cap exhaustion was incorrectly accepted")


def seven_pentagon(frames: Frames) -> tuple[int, ...]:
    field = frames.field
    need(field.p == 7, "this residue pentagon uses p=7")
    zero, one, minus = (0, 0), (1, 0), (6, 0)
    directions = (
        AXES[0],
        AXES[1],
        (one, zero, one),
        (minus, minus, one),
        (zero, one, one),
    )
    factors = (one, one, (2, 0), (2, 1), (2, 0))
    normalized = tuple(
        field.scale(scalar, v) for scalar, v in zip(factors, directions, strict=True)
    )
    need(all(field.dot(v, v) == one for v in normalized), "p=7 pentagon normalization")
    index = {v: j for j, v in enumerate(frames.rays)}
    ids = tuple(index[field.canonical(v)] for v in normalized)
    need(len(set(ids)) == 5, "p=7 pentagon collapsed")
    for j, ray in enumerate(ids):
        neighbor = ids[(j + 1) % 5]
        need(neighbor in frames.adjacent[ray], "missing p=7 pentagon edge")
        need(
            any(ray in base and neighbor in base for base in frames.bases),
            "incomplete p=7 pentagon context",
        )
    return ids


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--include-seven", action="store_true")
    args = parser.parse_args()
    frames = enumerate_frames(3)
    valuation, nodes, conflicts = valuation_search(frames)
    need(valuation is None and nodes == 15, "p=3 valuation regression")
    solver_controls(frames)
    need(distinct_five_cycles(frames) == 0, "unexpected residue pentagon")
    orbit = native_orbit(frames)
    need(orbit == (63, 63), "native residue orbit")
    lift_controls()
    real_and_split_controls()
    print(
        f"F9: {len(frames.rays)} rays, {len(frames.bases)} bases, valuation UNSAT ({nodes} nodes, {conflicts} conflicts)."
    )
    print(
        "No distinct residue C5; native T/i already cover all 63 rays and 63 bases; z5 reduces to -i."
    )
    print(
        "Checked distinct-ray fiber and a 5-and-17 pentagon collapsing to (e1,e2,e1,e3,e2)."
    )
    if args.include_seven:
        larger = enumerate_frames(7)
        need(
            (len(larger.rays), len(larger.bases)) == (2107, 14749),
            "p=7 incidence counts",
        )
        need(len(larger.bases) % 21 != 0, "p=7 incidence obstruction")
        need(native_orbit(larger) == (2107, 14749), "p=7 native orbit")
        seven_pentagon(larger)
        print(
            "F49: 2107 rays, 14749 bases, 21 bases/ray; valuation impossible since 14749/21 is nonintegral."
        )
        print(
            "Native T/i cover this quotient too; an explicit F49 pentagon exists but is not a lifted R5 witness."
        )
    else:
        print(
            "p=7 incidence formula gives 2107 rays and 14749 bases; use --include-seven to enumerate them."
        )
    print(
        "Real normalized R5 subcase: axis coloring pulls back. Gaussian R5: no valuation or KS lift obtained."
    )
    print(
        "At 5, R5 has no reduction; without inverted 5 the residue is a split ring, not a Hermitian field."
    )
    print(
        "Asymmetric prime-5 characteristic-zero pentagon and other-prime valuations remain untested here."
    )


if __name__ == "__main__":
    main()
