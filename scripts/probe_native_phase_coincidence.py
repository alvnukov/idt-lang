"""Finite coincidence, residue, and preparation controls on two frozen carriers.

Use two copies of the same 16-address three-context carrier. D advances
both copies by W=ABC; H advances the right copy by W inverse. Independently
enumerate their product orbits and recover them from colored equalizers.
Then realize the class plus a separation residue in a supplied four-cell
half-filled contact layout. Contact eligibility reads only occupancy,
not the equalizer, labels, phase, or a spectator. D and H select separate
fixed layouts; they are not simultaneously armed and no selector is derived.

Run: python3 -B -E -O -m scripts.probe_native_phase_coincidence
"""

import json
from collections import Counter, deque
from dataclasses import asdict, dataclass
from itertools import combinations, permutations, product

from scripts.probe_octagon_three_contexts import (
    Maps,
    Perm,
    action,
    affine,
    check_minimal_action,
    require,
    two_rings,
)

COLORS = "ABC"
SWAP = "BAC"
Pair = tuple[int, int]
Partition = set[frozenset[Pair]]
Labels = tuple[int, ...]


@dataclass(frozen=True)
class ContactAudit:
    class_rails: int
    residue_rails: int
    output_footprints: int
    forward_offers: dict[int, int]
    reverse_offers: dict[int, int]
    exact_forward: int
    exact_reverse: int


@dataclass(frozen=True)
class ModeReport:
    color_images: str
    product_orbits: int
    equalizer_classes: int
    partitions_agree: bool
    factored: ContactAudit
    private: ContactAudit
    class_dyad: ContactAudit
    class_dyad_with_spectators: ContactAudit
    lossy_z_edges: ContactAudit
    aligned_offers: dict[int, int]
    certified_null: bool


@dataclass(frozen=True)
class RestrictedBound:
    color_preserving_order: int
    central_w_order: int
    z_is_nonidentity_commutator: bool
    max_disjoint_stabilizer: int
    min_class_rails: int
    min_residue_rails: int
    c_edges_covariant: bool


@dataclass(frozen=True)
class Report:
    color_maps: dict[str, int]
    orientation_counts: dict[str, int]
    modes: dict[str, ModeReport]
    restricted_bound: RestrictedBound
    fixed_equality_counts: dict[str, tuple[int, int]]
    preparation_marginals_equal: bool
    scope: str


def compose(f: Perm, g: Perm) -> Perm:
    return tuple(f[j] for j in g)


def inverse(f: Perm) -> Perm:
    inv = [0] * len(f)
    for i, j in enumerate(f):
        inv[j] = i
    return tuple(inv)


def colored_maps(maps: Maps, image_colors: str) -> tuple[Perm, ...]:
    """Enumerate maps by propagating f(0)=root along each colored edge."""
    n = len(maps["A"])
    steps = tuple((maps[a], maps[b]) for a, b in zip(COLORS, image_colors, strict=True))
    found = []
    for root in range(n):
        dst = {0: root}
        pending = deque([0])
        consistent = True
        while pending and consistent:
            i = pending.popleft()
            for source, target in steps:
                j, value = source[i], target[dst[i]]
                if j in dst:
                    if dst[j] != value:
                        consistent = False
                        break
                else:
                    dst[j] = value
                    pending.append(j)
        if consistent and len(dst) == len(set(dst.values())) == n:
            found.append(tuple(dst[i] for i in range(n)))
    return tuple(found)


def even(image_colors: str) -> bool:
    return sum(a > b for a, b in combinations(image_colors, 2)) % 2 == 0


def checked_color_maps(
    maps: Maps, w: Perm, wi: Perm
) -> tuple[dict[str, tuple[Perm, ...]], dict[str, int]]:
    families = {}
    orientation: Counter[str] = Counter()
    n = len(w)
    for permutation in permutations(COLORS):
        pi = "".join(permutation)
        family = colored_maps(maps, pi)
        require(len(family) == n, f"wrong colored-map count for {pi}")
        # This demands regularity at every start, not just the BFS root.
        require(all({f[i] for f in family} == set(range(n)) for i in range(n)),
                f"colored maps did not cover every pair exactly once for {pi}")
        target = w if even(pi) else wi
        for f in family:
            require(compose(f, w) == compose(target, f), f"W orientation for {pi}")
            orientation["W" if even(pi) else "W_inverse"] += 1
        families[pi] = family
    require(len({f for family in families.values() for f in family}) == 96,
            "a map was duplicated across color images")
    return families, dict(orientation)


def walk(f: Perm, i: int) -> tuple[int, ...]:
    orbit = [i]
    j = f[i]
    while j != i:
        orbit.append(j)
        j = f[j]
    return tuple(orbit)


def product_orbits(w: Perm, right: Perm, pairs: tuple[Pair, ...]) -> Partition:
    groups: Partition = set()
    unseen = set(pairs)
    while unseen:
        i, j = start = min(unseen)
        orbit = {start}
        i, j = w[i], right[j]
        while (i, j) != start:
            orbit.add((i, j))
            i, j = w[i], right[j]
        unseen.difference_update(orbit)
        groups.add(frozenset(orbit))
    return groups


def equalizer_classes(
    w: Perm, family: tuple[Perm, ...], pairs: tuple[Pair, ...]
) -> tuple[Partition, Labels]:
    left_cycles = tuple(min(walk(w, i)) for i in range(len(w)))
    key_to_index: dict[Pair, int] = {}
    groups: dict[Pair, set[Pair]] = {}
    labels = []
    for i, j in pairs:
        (index,) = (idx for idx, f in enumerate(family) if f[i] == j)
        key = (index, left_cycles[i])
        key_to_index.setdefault(key, len(key_to_index))
        groups.setdefault(key, set()).add((i, j))
        labels.append(key_to_index[key])
    return {frozenset(g) for g in groups.values()}, tuple(labels)


def edge_labels(matching: Perm) -> Labels:
    index = {i: k for k, i in enumerate(i for i, j in enumerate(matching) if i < j)}
    return tuple(index[min(i, j)] for i, j in enumerate(matching))


def half_filled(occupancy: int, contacts: tuple[int, ...]) -> tuple[int, ...]:
    """Return every simultaneously eligible contact, not the intended one."""
    return tuple(mask for mask in contacts if (occupancy & mask).bit_count() == 2)


@dataclass(frozen=True)
class ContactLayout:
    inputs: tuple[int, ...]
    contacts: tuple[int, ...]
    class_rails: int
    residue_rails: int


def contact_layout(
    n: int, pairs: tuple[Pair, ...], first: Labels, second: Labels,
) -> ContactLayout:
    # The four role pools are disjoint. No side predicate augments the guard.
    n_first, n_second = max(first) + 1, max(second) + 1
    inputs = tuple((1 << i) | (1 << (n + j)) for i, j in pairs)
    contacts = tuple(
        ab | (1 << (2*n + c)) | (1 << (2*n + n_first + d))
        for ab, c, d in zip(inputs, first, second, strict=True)
    )
    require(len(set(contacts)) == len(inputs) and all(m.bit_count() == 4 for m in contacts),
            "not distinct four-cell contacts")
    require(len(set(first)) == n_first and len(set(second)) == n_second, "label gaps")
    return ContactLayout(inputs, contacts, n_first, n_second)


def audit_contacts(
    layout: ContactLayout, n: int, pairs: tuple[Pair, ...], *, spectators: bool = False,
) -> ContactAudit:
    forward: Counter[int] = Counter()
    reverse: Counter[int] = Counter()
    outputs = set()
    exact_forward = exact_reverse = 0
    for (i, j), source, mask in zip(pairs, layout.inputs, layout.contacts, strict=True):
        if spectators:
            offset = 2*n + layout.class_rails + layout.residue_rails
            source |= (1 << (offset + i)) | (1 << (offset + n + j))
        offered = half_filled(source, layout.contacts)
        forward[len(offered)] += 1
        exact_forward += offered == (mask,)
        require(mask in offered, "designated forward contact is not legal")
        output = source ^ mask
        outputs.add(output)
        offered = half_filled(output, layout.contacts)
        reverse[len(offered)] += 1
        exact_reverse += offered == (mask,)
        require(mask in offered, "designated inverse contact is not legal")
    return ContactAudit(layout.class_rails, layout.residue_rails, len(outputs),
                        dict(forward), dict(reverse), exact_forward, exact_reverse)


def check_mode(
    pi: str, w: Perm, right: Perm, family: tuple[Perm, ...], pairs: tuple[Pair, ...],
    c_labels: Labels, z_labels: Labels,
) -> tuple[ModeReport, tuple[int, ...]]:
    n = len(w)
    dynamic = product_orbits(w, right, pairs)
    relational, classes = equalizer_classes(w, family, pairs)
    require(dynamic == relational and len(dynamic) == 64 and {len(g) for g in dynamic} == {4},
            f"{pi}: different orbit partitions")
    c_residues = tuple(c_labels[i] for i, _ in pairs)
    z_residues = tuple(z_labels[i] for i, _ in pairs)
    private_labels = tuple(range(len(pairs)))
    layout = contact_layout(n, pairs, classes, c_residues)
    dyad_layout = contact_layout(n, pairs, classes, classes)
    factored = audit_contacts(layout, n, pairs)
    private = audit_contacts(contact_layout(n, pairs, private_labels, private_labels), n, pairs)
    dyad = audit_contacts(dyad_layout, n, pairs)
    spectator = audit_contacts(dyad_layout, n, pairs, spectators=True)
    lossy = audit_contacts(contact_layout(n, pairs, classes, z_residues), n, pairs)
    for checked, inverse_count, footprints, rails in (
        (factored, 1, 256, (64, 8)),
        (private, 1, 256, (256, 256)),
        (dyad, 4, 64, (64, 64)),
        (spectator, 4, 256, (64, 64)),
        (lossy, 2, 128, (64, 8)),
    ):
        require(checked.forward_offers == {1: 256} and checked.exact_forward == 256,
                f"{pi}: incorrect forward offer census")
        require(checked.reverse_offers == {inverse_count: 256}
                and checked.exact_reverse == (256 if inverse_count == 1 else 0),
                f"{pi}: incorrect inverse offer census")
        require(checked.output_footprints == footprints
                and (checked.class_rails, checked.residue_rails) == rails,
                f"{pi}: incorrect footprint census")

    # A single root alignment is a supplied partial layout, not a truth flag.
    (aligned,) = (f for f in family if f[0] == 0)
    contacts = tuple(
        cell for (i, j), cell in zip(pairs, layout.contacts, strict=True) if aligned[i] == j
    )
    offers: Counter[int] = Counter()
    for (i, j), state in zip(pairs, layout.inputs, strict=True):
        count = len(half_filled(state, contacts))
        require(count == int(aligned[i] == j), f"{pi}: aligned sheet offer mismatch")
        offers[count] += 1
    require(offers == {0: 240, 1: 16}, f"{pi}: wrong aligned sheet size")
    return ModeReport(pi, len(dynamic), len(relational), dynamic == relational, factored,
                      private, dyad, spectator, lossy, dict(offers), False), contacts


def residue_bound(
    maps: Maps, families: dict[str, tuple[Perm, ...]], w: Perm, z: Perm,
    c_labels: Labels, class_count: int,
) -> RestrictedBound:
    # Scope: class rail must name the class independently of a one-hot
    # residue, and the residue transmits an equivariant function of i alone.
    identity = tuple(range(len(w)))
    group = set(families[COLORS])
    center4 = {identity, w, z, inverse(w)}
    require(len(group) == 16 and identity in group and
            all(compose(g, h) in group for g, h in product(group, repeat=2)),
            "color-preserving maps are not the finite group of order sixteen")
    require(len(center4) == 4 and center4 <= group and compose(w, w) == z
            and compose(z, z) == identity and
            all(compose(g, h) == compose(h, g) for g, h in product(group, center4)),
            "not a central four-cycle subgroup")
    commutators = {
        compose(compose(g, h), compose(inverse(g), inverse(h)))
        for g, h in product(group, repeat=2)
    }
    require(z != identity and z in commutators, "Z is not a nonidentity commutator")
    # Residue must separate all four i in each class. By regularity an
    # equivariant one-hot output has a stabilizer K, and K intersects <W>
    # trivially. If |K|=4, G=<W>K would be abelian (order-4 K is abelian,
    # and <W> is central). |K|>4 is ruled out by the disjoint product bound.
    # Cross-check directly that no four-element subgroup disjoint from
    # <W> outside identity exists, independently of the algebraic argument.
    for choices in combinations(sorted(group - center4), 3):
        candidate = {identity, *choices}
        require(any(compose(g, h) not in candidate for g, h in product(candidate, repeat=2)),
                "four-element disjoint stabilizer found")
    require(len(set(c_labels)) == 8 and all(len({c_labels[j] for j in walk(w, i)}) == 4
                for i in range(len(w))), "C edge does not separate the lifted left cycle")
    for g in (*families[COLORS], *families[SWAP]):
        require(all(g[maps["C"][i]] == maps["C"][g[i]] for i in range(len(w))),
                "C edge did not transport under preserving/swap maps")
    stabilizer = {g for g in group if c_labels[g[0]] == c_labels[0]}
    require(len(stabilizer) == 2 and stabilizer & center4 == {identity},
            "C edge stabilizer does not attain the restricted bound")
    return RestrictedBound(len(group), len(center4), z in commutators, len(stabilizer),
                           class_count, len(group) // len(stabilizer), True)


def fixed_equality_preparations(
    w: Perm, wi: Perm, equality_contacts: tuple[int, ...]
) -> tuple[dict[str, tuple[int, int]], bool]:
    # Both identified copies use the same raw root. Check every root, with
    # one unchanged literal j=i instrument for all supplied preparations.
    counts: dict[str, tuple[int, int]] = {}
    n = len(w)
    for root in range(n):
        sites, back = walk(w, root), walk(wi, root)
        distributions = {
            "independent": tuple(product(sites, repeat=2)),
            "D_common": tuple(zip(sites, sites, strict=True)),
            "H_common": tuple(zip(sites, back, strict=True)),
        }
        marginal = {s: 1 for s in sites}
        for name, rows in distributions.items():
            multiplicity = len(rows) // len(sites)
            expected = {s: value * multiplicity for s, value in marginal.items()}
            require(Counter(i for i, _ in rows) == expected
                    and Counter(j for _, j in rows) == expected, "unequal marginals")
            hits = 0
            for i, j in rows:
                state = (1 << i) | (1 << (n + j))
                offered = half_filled(state, equality_contacts)
                require(len(offered) == int(i == j), "instrument changed from literal equality")
                hits += bool(offered)
            require(counts.setdefault(name, (hits, len(rows))) == (hits, len(rows)),
                    "count depends on root")
    require(counts == {"independent": (4, 16), "D_common": (4, 4), "H_common": (2, 4)},
            "different fixed-instrument counts")
    return counts, True


def run_probe() -> Report:
    maps = two_rings(affine(5, 0))
    check_minimal_action(maps)
    w, z = action(maps, "ABC"), action(maps, "ABAB")
    wi = inverse(w)
    n = len(w)
    require(n == 16, "wrong frozen carrier size")
    pairs = tuple(product(range(n), range(n)))
    families, orientation = checked_color_maps(maps, w, wi)
    c_labels, z_labels = edge_labels(maps["C"]), edge_labels(z)
    d_report, equality = check_mode(COLORS, w, w, families[COLORS], pairs, c_labels, z_labels)
    h_report, _ = check_mode(SWAP, w, wi, families[SWAP], pairs, c_labels, z_labels)
    bound = residue_bound(maps, families, w, z, c_labels, d_report.equalizer_classes)
    preparations, same_marginals = fixed_equality_preparations(w, wi, equality)
    return Report(
        {pi: len(family) for pi, family in families.items()}, orientation,
        {"D": d_report, "H": h_report}, bound, preparations, same_marginals,
        "Finite checks with supplied layouts, role pools, alignment and preparations. "
        "An absent offer is not a certified null; counts are not probabilities derived "
        "from the local law. The 64+8 bound is only for the stated equivariant one-hot "
        "class/residue architecture, not unrestricted encoders or detectors.",
    )


def main() -> None:
    print(json.dumps(asdict(run_probe()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
