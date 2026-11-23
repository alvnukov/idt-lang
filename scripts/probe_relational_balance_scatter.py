"""What can a parallelogram comparison do without a marked zero or a scale?

D(a,b;c,d) reads "the directed edge a->b equals c->d". Values may be
anonymously renamed; the opposite-corner PAIRING is structure. We test
whether three input/output edges sum to zero and all input/output pairs
have the same formal sum. Neither constraint is implied by merely having
D. Only one relation is *queried*, not only one physical law assumed.

Conditional algebra. On a nonempty set assume only (i) D is an equivalence
on directed pairs, (ii) unique fourth filling from every triple, (iii)
corner interchange D(a,b;c,d) iff D(a,c;b,d). Interchange identifies all
diagonals via D(a,b;a,b). Interchange, exchange of equivalent pairs, and
interchange again give D(b,a;d,c): the reversed edge gives the inverse
transport. Transport alpha then beta is the same rectangle as beta then
alpha, so the class transports commute. A product agrees at one point
with a unique class transport; commute with the class sending that point
anywhere to extend agreement everywhere. This is a regular abelian group
action, with no selected origin. Conversely any abelian torsor has these
three properties. Unique filling and corner symmetries alone do NOT give
edge transitivity. This is a mathematical argument, not a Lean artifact.

In any temporary abelian chart, common pair sums mean y_i=b-x_i, and
transporting by each x_i->y_i closes iff 3b=2 sum(x). This argument works
without midpoints, halving, division primitives, metric, readout law or
time. Changing chart translates the formal common sum by twice the
translation. If tripling is bijective this is the unique involution;
in general the solution set is empty or a coset of ker(3). For arbitrary
abelian groups totality on triples is equivalent to 3A=A, since 2 is
invertible on A/3A. Torsion-free alone is NOT sufficient (take Z).
Even unique solvability in Q is not a local construction by repeated
fourth fills: from marks 0,1 such circuits make only integers, not 2/3.

The previous anonymous_midpoint_factory already constructed the glued
21-point counterworld and exhibited nonmediality of its midpoint. Here
the new tests compare translations of directed edges and classify a
three-port contact by closure from every possible witness origin. The
Lean balanced nonmedial mixer tests a different complex gate. No group
of physical records, actual contact, sign resource or QM is derived.
"""

from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import gcd


def need(condition, why):
    if not condition:
        raise ArithmeticError(why)


ORDERS = tuple(permutations(range(3)))


class Comparison:
    """Use only the supplied yes/no comparison; keep no fixture coordinates."""

    def __init__(self, n, compare):
        self.marks = tuple(range(n))
        rows = []
        for a, b, p in product(self.marks, repeat=3):
            fills = [z for z in self.marks if compare(a, b, p, z)]
            need(len(fills) == 1, "missing or ambiguous fourth record")
            z = fills[0]
            need(
                compare(p, z, a, b) and compare(b, a, z, p) and compare(a, p, b, z),
                "pair, simultaneous reversal or corner symmetry",
            )
            rows.append(z)
        self.shift = {
            edge: tuple(rows[j * n : (j + 1) * n])
            for j, edge in enumerate(product(self.marks, repeat=2))
        }
        need(
            all(set(col) == set(self.marks) for col in self.shift.values()),
            "class transport not bijective",
        )

    def transitivity_failures(self):
        # A related edge must present exactly the same possible comparisons.
        return sum(
            row != self.shift[p, q]
            for row in self.shift.values()
            for p, q in enumerate(row)
        )

    def pair_solutions(self, xs):
        # Choose y0; D(x_i,x_0;y_0,y_i) supplies all remaining outputs.
        return tuple(tuple(self.shift[x, xs[0]][y0] for x in xs) for y0 in self.marks)

    def returns(self, xs, ys, p, order):
        z = p
        for i in order:
            z = self.shift[xs[i], ys[i]][z]
        return p == z

    def contacts(self, xs):
        return {
            ys
            for ys in self.pair_solutions(xs)
            if all(
                self.returns(xs, ys, p, order) for p in self.marks for order in ORDERS
            )
        }

    def ordered_test(self, a, b, c):
        # Same three inputs. From b compare transport a->b then a->c,
        # and a->c then a->b. Only record equality is read at the end.
        u, v = self.shift[a, b], self.shift[a, c]
        return v[u[b]], u[v[b]]


def cyclic(n):
    return Comparison(n, lambda a, b, c, d: (b - a - (d - c)) % n == 0)


def affine_cases():
    rows = []
    for n in (2, 3, 4, 5, 6, 7, 9):
        r = cyclic(n)
        k = gcd(n, 3)
        need(r.transitivity_failures() == 0, "affine comparators lost transitivity")
        counts = Counter()
        graph = {}
        for xs in product(r.marks, repeat=3):
            got = r.contacts(xs)
            graph[xs] = got
            expected = {
                tuple((b - x) % n for x in xs)
                for b in r.marks
                if (3 * b - 2 * sum(xs)) % n == 0
            }
            need(
                got == expected,
                "relational lookup disagrees with independent affine equation",
            )
            counts[len(got)] += 1
            for ys in got:
                need(
                    all(
                        (x + y) % n == (xs[0] + ys[0]) % n
                        for x, y in zip(xs, ys, strict=True)
                    )
                    and (sum(xs) - sum(ys)) % n == 0,
                    "common sum or displacement conservation",
                )
        need(
            all(xs in graph[ys] for xs in graph for ys in graph[xs]),
            "contact not reversible",
        )
        need(
            counts[k] == n**3 // k and counts[0] == n**3 - n**3 // k,
            "torsion fiber census",
        )
        if n == 2:
            need(
                all(r.contacts(xs) == {xs} for xs in product(r.marks, repeat=3)),
                "self-opposed signs give identity",
            )
        if n == 5:
            need(r.contacts((0, 0, 1)) == {(4, 4, 3)}, "first nontrivial reflection")
            need(
                len(r.pair_solutions((0, 0, 1))) == 5
                and (0, 0, 1) not in r.pair_solutions((0, 0, 1)),
                "countercontrols: common sum alone is nonunique; identity conserves without common sum",
            )
        if k == 3:
            t = n // 3
            xs = (0, t, 2 * t)
            choices = r.contacts(xs)
            need(
                len(choices) == 3 and tuple((x + t) % n for x in xs) == xs[1:] + xs[:1],
                "translation is port rotation on the input",
            )
            need(
                all(
                    tuple((y + t) % n for y in ys) != ys[1:] + ys[:1] for ys in choices
                ),
                "anonymous deterministic branch on order-three translation orbit",
            )
        rows.append((n, counts[0], counts[k], k))
    # With no pairing of opposite roles, three distinct completions even
    # after forbidding repetitions. Full S4 role symmetry would force
    # D(b,a;a,b) from D(a,b;a,b), hence every displacement self-inverse.
    answers = {(a + b - c) % 7 for a, b, c in permutations((0, 1, 3))}
    need(answers == {2, 4, 5}, "unordered fourth point")
    return rows


def constructive_wall():
    # A pure forward-fill circuit can branch on comparison or choose/reuse
    # known values, but must not invent an arbitrary external record.
    # If its inputs are integers in Q, then b-a+c is integer at EVERY
    # call. In contrast, solving a globally quantified relation can name
    # a unique fractional output. Propagating this distinction matters.
    xs = (0, 0, 1)
    b = Fraction(2 * sum(xs), 3)
    ys = tuple(b - x for x in xs)
    need(
        ys == (Fraction(2, 3), Fraction(2, 3), Fraction(-1, 3))
        and all(y.denominator != 1 for y in ys),
        "rational affine-hull obstruction",
    )
    # Finite analogue. After h parallel rounds, reachable integer lifts
    # from {0,1} lie in [(1-3^h)/2,(1+3^h)/2], by min and max of b-a+c.
    # Every integer between the bounds occurs (sum/difference of intervals).
    # For any fixed h, a sufficiently large prime precludes 3*z=2 mod p
    # throughout this interval, hence no uniform depth over prime fields.
    # Check exact first reach for this supplied finite alphabet by lookup.
    p = 251
    want = {i for i in range(p) if 3 * i % p == 2 or 3 * i % p == p - 1}
    reached = {0, 1}
    for h in range(6):
        need(
            reached == {i % p for i in range((1 - 3**h) // 2, (1 + 3**h) // 2 + 1)},
            "forward completion reachability",
        )
        need((want <= reached) == (h == 5), "finite compilation depth")
        if h < 5:
            sums = {b + c for b in reached for c in reached}
            reached = {(s - a) % p for s in sums for a in reached}
    return ys, sorted(want)


def old_rival():
    # The previous counterworld's explicit line design. The coordinates
    # here generate the table; the new reader receives only the predicate.
    frame = (0, 1, 4, 14, 16)
    lines = tuple(tuple((a + t) % 21 for a in frame) for t in range(21))
    entries = {}
    for line in lines:
        for i, j in product(range(5), repeat=2):
            pair = (line[i], line[j])
            midpoint = line[3 * (i + j) % 5]
            need(
                entries.setdefault(pair, midpoint) == midpoint,
                "inconsistent line gluing",
            )
    need(len(entries) == 21**2, "missing table pair")
    return Comparison(21, lambda a, b, c, d: entries[b, c] == entries[a, d]), lines


def glued_cases():
    r, lines = old_rival()
    # Not just a few shallow controls: the directed-edge completion
    # itself restricts to the exact affine rule on EVERY five-mark line;
    # circuits fed from that line stay there by induction. Universal
    # quantification over independent remote witnesses is a stronger test.
    for line in lines:
        for a, b, c in product(range(5), repeat=3):
            need(
                r.shift[line[a], line[b]][line[c]] == line[(b - a + c) % 5],
                "in-line completion differs from affine calibration",
            )
    bad = r.transitivity_failures()
    need(
        bad == 8400,
        "transitivity failure census among 21 cubed related-edge presentations",
    )
    comm = [r.ordered_test(0, 1, c) for c in r.marks]
    fail = sum(left != right for left, right in comm)
    need(
        comm[2] == (12, 5) and fail == 15 and comm[12][0] == comm[12][1],
        "two-context transport discrimination (one accidental off-line hit)",
    )
    # The unique output of the in-line affine circuit. Verify all possible
    # origins and all six port orders, then reject EVERY alternative output
    # under the same universal criterion, not only this expected output.
    xs = (0, 0, 1)
    optimal = (16, 16, 14)
    returning = tuple(
        p for p in r.marks if all(r.returns(xs, optimal, p, o) for o in ORDERS)
    )
    need(
        set(returning) == set(lines[0])
        and all(
            not r.returns(xs, optimal, p, o)
            for p in r.marks
            if p not in returning
            for o in ORDERS
        )
        and not r.contacts(xs),
        "global witness dependence of the known line output",
    )
    need(
        r.contacts((0, 0, 0)) == {(0, 0, 0)} and r.contacts((0, 1, 4)) == {(4, 1, 0)},
        "overstrong conclusion: some contacts survive even across external witnesses",
    )
    return bad, fail, returning


def main():
    rows = affine_cases()
    bad, fail, returning = glued_cases()
    ys, finite = constructive_wall()
    print(
        "Cyclic order, unsupported ordered triples, supported triples, outputs per supported triple:",
        rows,
    )
    print(
        "Nonzero order-three shift: no deterministic translation- and port-equivariant branch on its orbit."
    )
    print(
        "Self-inverse signs at order two: identity contact. No opposite pairing at order seven: three completions."
    )
    print(
        f"Forward fourth fills on 0,1 in Q cannot create {tuple(map(str, ys))}; modulo 251 the required labels {finite} appear in round 5, not earlier."
    )
    print(
        f"Glued 21-tag rival: {bad} edge comparisons fail transport-row transitivity; {fail}/21 third labels fail the fixed commutator."
    )
    print(
        f"For x=(0,0,1), line output closes from {returning} only, all six orders; no globally closing alternative."
    )
    print(
        "Conditional incidence discriminator; no origin, distribution, physical displacement group, contact or quantum law inferred."
    )


if __name__ == "__main__":
    main()
