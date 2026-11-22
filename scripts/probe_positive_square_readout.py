"""Exact finite controls for squaring an unknown signed Bernoulli mean.

IID signs have P(+1)=p and mean mu=2*p-1. A source-blind single-click
protocol using at most n samples can be padded to length n and symmetrized.
Its click expectation is a Bernstein polynomial with coefficients in [0,1].
For n>=2, the unique coefficients of c+v*mu**2 are
    b[k] = c + v*((2*k-n)**2-n)/(n*(n-1)).
For v>=0 these are admissible exactly when c>=v/d and c+v<=1, where
d=n-1 for even n and d=n for odd n. This is an iid sampling restriction,
not a restriction on supplied correlated queries. Exact rational polynomial
expansion and n+1 rational evaluation points check each tested identity.
Uniqueness follows from the triangular Bernstein-to-power-basis matrix,
whose diagonal entries binomial(n,k) are nonzero.

There is also a general support argument, not a Lean theorem here. Every
finite binary transcript has positive probability at every interior p.
Integrating source-independent internal randomness gives a nonnegative
click weight for each stopping transcript. A positive finite click event
at one interior p therefore has positive probability at p=1/2. Countable
additivity extends this observation to an almost-surely finite stopping
rule: exact darkness at an interior p forces all finite click weights to
vanish, hence no interior source clicks. The executable checks below test
finite support instances; they do not exhaust infinite stopping rules.

An active alternative supplies an even catalogue size N, a threshold cut
A_m={0,...,m-1}, and the SAME fixed-point-free reverse pairing
tau(i)=N-1-i for every m. Querying signs at i and tau(i), with i uniform,
gives an equality flag of probability abs(2*m/N-1). Two independent such
flags have coincidence probability mu**2, using four classical queries.
Each queried sign separately has the Bernoulli marginal m/N, but the
queried pair is NOT iid. Reusing a flag or its paired index does not square
its expectation. Shuffled cuts and incompatible balanced partitions show
that the common pairing is supplied structure, not a marginal consequence.

Choosing a source once per entire run makes every click probability linear
in that source mixture. This differs from independently mixing the source
at every query. Signed Bernoulli means are not physical coherent amplitudes;
no field, Born rule, quantum closure, or physical realization is derived.
This standard-library-only finite fixture is not a formal proof artifact.
"""

from collections.abc import Sequence
from fractions import Fraction as F
from itertools import combinations, product
from math import comb

CHECKS = 0


def check(condition: bool, message: str) -> None:
    """Keep checks enabled under python -O."""
    global CHECKS
    CHECKS += 1
    if not condition:
        raise RuntimeError(message)


def coefficients(n: int, c: F, v: F) -> tuple[F, ...]:
    if n < 2 or v < 0:
        raise ValueError("require n>=2 and v>=0")
    return tuple(c + v * F((2 * k - n) ** 2 - n, n * (n - 1)) for k in range(n + 1))


def bernstein_expectation(values: Sequence[F], p: F) -> F:
    n = len(values) - 1
    return sum(
        (
            value * comb(n, k) * p**k * (1 - p) ** (n - k)
            for k, value in enumerate(values)
        ),
        F(0),
    )


def power_coefficients(values: Sequence[F]) -> tuple[F, ...]:
    n = len(values) - 1
    result = [F(0)] * (n + 1)
    for k, value in enumerate(values):
        for j in range(n - k + 1):
            result[k + j] += value * comb(n, k) * comb(n - k, j) * (-1) ** j
    return tuple(result)


def iid_controls() -> int:
    cases = 0
    for n in range(2, 13):
        d = n - 1 if n % 2 == 0 else n
        eps = F(1, 100 * n)
        for v in (F(0), F(1, 8), F(1, 2), F(d, d + 1), F(1)):
            for c in (F(0), v / d, v / d - eps, 1 - v, 1 - v + eps, F(1, 4), F(1, 2)):
                values = coefficients(n, c, v)
                check(min(values) == c - v / d, f"minimum n={n}")
                check(max(values) == c + v, f"maximum n={n}")
                admissible = all(0 <= value <= 1 for value in values)
                check(admissible == (c >= v / d and c + v <= 1), f"iff n={n}")
                target = (c + v, -4 * v, 4 * v) + (F(0),) * (n - 2)
                check(power_coefficients(values) == target, f"power expansion n={n}")
                for j in range(n + 1):
                    p = F(j, n)
                    check(
                        bernstein_expectation(values, p) == c + v * (2 * p - 1) ** 2,
                        f"rational evaluation n={n}, p={p}",
                    )
                cases += 1
        tight_v = F(d, d + 1)
        tight = coefficients(n, F(1, d + 1), tight_v)
        check(min(tight) == 0 and max(tight) == 1, f"tight threshold n={n}")
        check(min(coefficients(n, F(0), F(1))) < 0, f"no exact dark n={n}")
        # For the k-th basis polynomial the lowest nonzero power is p**k.
        for k in range(n + 1):
            unit = tuple(F(int(j == k)) for j in range(n + 1))
            powers = power_coefficients(unit)
            check(all(value == 0 for value in powers[:k]), "triangular basis")
            check(powers[k] == comb(n, k) > 0, "nonzero basis diagonal")
        signed = coefficients(n, F(0), F(1))
        plugin = tuple(F((2 * k - n) ** 2, n**2) for k in range(n + 1))
        unanimous = tuple(F(int(k in (0, n))) for k in range(n + 1))
        check(min(signed) == -F(1, d), "signed estimator has negative values")
        for j in range(n + 1):
            p = F(j, n)
            mu2 = (2 * p - 1) ** 2
            check(bernstein_expectation(signed, p) == mu2, "signed unbiased mean")
            check(
                bernstein_expectation(plugin, p) == mu2 + (1 - mu2) / n,
                "positive plug-in bias",
            )
            check(
                bernstein_expectation(unanimous, p) == p**n + (1 - p) ** n,
                "unanimity law",
            )
        check(bernstein_expectation(plugin, F(1, 2)) == F(1, n), "plug-in dark floor")
        check(
            bernstein_expectation(unanimous, F(1, 2)) == F(1, 2 ** (n - 1)),
            "unanimity is not an exact interior-dark readout",
        )
    return cases


def transcript_support_controls() -> int:
    leaves = 0
    for length in range(1, 9):
        for word in product((0, 1), repeat=length):
            k = sum(word)
            for p in (F(1, 7), F(1, 2), F(6, 7)):
                check(p**k * (1 - p) ** (length - k) > 0, "interior transcript support")
            leaves += 1
    # Stop at the first 1, capped at n; click only on stopping with a 1.
    for n in range(1, 9):
        for p in (F(1, 7), F(1, 2), F(6, 7)):
            click = sum(((1 - p) ** j * p for j in range(n)), F(0))
            check(click == 1 - (1 - p) ** n > 0, "bounded stopping control")
    return leaves


def equality_flags(n: int, cut: frozenset[int]) -> tuple[int, ...]:
    return tuple(int((i in cut) == (n - 1 - i in cut)) for i in range(n))


def active_pairing_controls() -> int:
    cases = 0
    for n in range(2, 22, 2):
        for m in range(n + 1):
            cut = frozenset(range(m))
            flags = equality_flags(n, cut)
            p = F(m, n)
            absolute_mean = abs(2 * p - 1)
            check(F(sum(flags), n) == absolute_mean, "threshold equality law")
            for i in range(n):
                check(n - 1 - i != i, "fixed-point-free pairing")
                check(n - 1 - (n - 1 - i) == i, "involutive pairing")
            # Uniform i and j are chosen independently, even when they coincide.
            independent = F(
                sum(flags[i] * flags[j] for i, j in product(range(n), repeat=2)), n**2
            )
            same_twice = F(sum(flag * flag for flag in flags), n)
            paired_twice = F(sum(flags[i] * flags[n - 1 - i] for i in range(n)), n)
            check(independent == (2 * p - 1) ** 2, "four-query independent coincidence")
            check(
                same_twice == paired_twice == absolute_mean,
                "shared flags do not square",
            )
            if 0 < absolute_mean < 1:
                check(independent < same_twice, "strict shared/independent separation")
            # Both members of the queried pair have the same single-sign law.
            check(F(sum(i in cut for i in range(n)), n) == p, "first marginal")
            check(F(sum(n - 1 - i in cut for i in range(n)), n) == p, "second marginal")
            iid_equality = p**2 + (1 - p) ** 2
            if 0 < p < 1:
                check(
                    absolute_mean < iid_equality,
                    "same marginals, different queried joint",
                )
            cases += 1
        # A shuffled half-cut generally fails for the supplied reverse pairing.
        half_cuts = (
            tuple(frozenset(cut) for cut in combinations(range(n), n // 2))
            if n <= 8
            else ()
        )
        if n >= 4 and half_cuts:
            check(
                any(sum(equality_flags(n, cut)) > 0 for cut in half_cuts),
                "arbitrary half-cuts need not be dark under fixed reverse pairing",
            )
    return cases


def incompatible_partition_control() -> None:
    # Every signature has even parity, hence none has its three-bit complement.
    signatures = ((0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0))
    pairings = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
    cuts = tuple(
        frozenset(i for i in range(4) if signatures[i][axis]) for axis in range(3)
    )
    check(all(len(cut) == 2 for cut in cuts), "three balanced cuts")

    def reverses(pairing: tuple[tuple[int, int], ...], axes: tuple[int, ...]) -> bool:
        return all(
            signatures[i][axis] != signatures[j][axis]
            for i, j in pairing
            for axis in axes
        )

    for axes in combinations(range(3), 2):
        check(
            any(reverses(pairing, axes) for pairing in pairings),
            "each pair of cuts feasible",
        )
    check(
        not any(reverses(pairing, (0, 1, 2)) for pairing in pairings),
        "no common triple pairing",
    )
    for signature in signatures:
        check(
            tuple(1 - bit for bit in signature) not in signatures, "missing complement"
        )
    shuffled = frozenset((0, 3))
    check(
        sum(equality_flags(4, shuffled)) == 4, "explicit shuffled balanced-cut failure"
    )


def mixture_control() -> None:
    # Choose an entire endpoint source once: 00/11, not four iid half-cut queries.
    endpoint_sources = ((F(1, 2), F(-1)), (F(1, 2), F(1)))
    mixed_mean = sum((weight * mean for weight, mean in endpoint_sources), F(0))
    mixed_click = sum((weight * mean**2 for weight, mean in endpoint_sources), F(0))
    check(
        mixed_click == 1 and mixed_mean**2 == 0, "whole-source mixture remains linear"
    )
    for weight in (F(0), F(1, 4), F(1, 2), F(3, 4), F(1)):
        # A source-independent readout on a two-bit transcript.
        readout = {(0, 0): F(1, 5), (0, 1): F(1, 3), (1, 0): F(2, 3), (1, 1): F(4, 5)}
        sources = (F(1, 5), F(4, 5))
        direct = F(0)
        source_clicks = []
        for p in sources:
            source_clicks.append(
                sum(
                    (
                        value * p ** sum(word) * (1 - p) ** (2 - sum(word))
                        for word, value in readout.items()
                    ),
                    F(0),
                )
            )
        for word, value in readout.items():
            k = sum(word)
            mixture_probability = weight * sources[0] ** k * (1 - sources[0]) ** (
                2 - k
            ) + (1 - weight) * sources[1] ** k * (1 - sources[1]) ** (2 - k)
            direct += value * mixture_probability
        check(
            direct == weight * source_clicks[0] + (1 - weight) * source_clicks[1],
            "linear source mixture",
        )


def main() -> None:
    cases = iid_controls()
    leaves = transcript_support_controls()
    active_cases = active_pairing_controls()
    incompatible_partition_control()
    mixture_control()
    print(f"PASS: {CHECKS} exact rational/finite checks (enabled under -O)")
    print(
        f"IID: n=2..12, {cases} offset/visibility cases; sharp Bernstein floor verified"
    )
    print(
        f"SUPPORT: {leaves} finite transcripts; general stopping argument stated, not formalized"
    )
    print(
        "CONTROLS: signed estimator negative; positive plug-in biased; unanimity not interior-dark"
    )
    print(
        f"ACTIVE: {active_cases} threshold cuts, even N=2..20; supplied reverse pairing + independent flags"
    )
    print("NEGATIVE: shared flags, shuffled cuts, and incompatible triple partitions")
    print(
        "BOUNDARY: finite classical fixture only; source-mixture linearity; no physical amplitude/Born derivation"
    )


if __name__ == "__main__":
    main()
