"""Census of a frozen family of four-label contact laws on borrowed schedules.

A table contains the output codes for the 16 ordered inputs in lexicographic
order. Pair code ``4*a+b`` encodes ``(a,b)``. No quotient by label renaming or
fitting is used. This is evidence about specified finite instruments, not a
rejection of other schedules or a claim about physical law.

Run with ``python3 -m scripts.probe_four_label_law_census --enumerate`` to
emit the full replayable family and its exact raw signatures.
"""

import argparse
import json
from collections import Counter
from collections.abc import Iterator
from dataclasses import asdict, dataclass, replace
from hashlib import sha256
from itertools import permutations, product

from scripts import probe_colorless_packet_arms as arms
from scripts import probe_packet_free_pair_record as pair_record

Table = tuple[int, ...]
VACANT_SECTOR = (1, 2, 6)  # 01, 02, 12
MIXED_SECTOR = (3, 7, 11)  # 03, 13, 23
SETTINGS = tuple(product(arms.ARMS, arms.SWITCHES, arms.SWITCHES))
LAUNCH_STOCK = tuple(product(arms.SOURCE_SEEDS, arms.MASK_SEEDS))
CENTRAL_GROUPS = (
    tuple(i for i, (_, plates, opened) in enumerate(SETTINGS) if all(opened) and not any(plates)),
    tuple(i for i, (_, _, opened) in enumerate(SETTINGS) if all(opened)),
    tuple(i for i, (_, _, opened) in enumerate(SETTINGS) if sum(opened) == 1),
    tuple(i for i, (_, _, opened) in enumerate(SETTINGS) if not any(opened)),
)


def swap(code: int) -> int:
    left, right = divmod(code, 4)
    return 4 * right + left


def oriented_inputs(representatives: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(code for rep in representatives for code in (rep, swap(rep)))


def signed_sector(representatives: tuple[int, ...]) -> tuple[Table, ...]:
    """Involute the three swap orbits and give each involution cycle one sign."""
    size = len(representatives)
    outputs = []
    for perm in permutations(range(size)):
        if any(perm[perm[i]] != i for i in range(size)):
            continue
        cycles = tuple(min(i, perm[i]) for i in range(size))
        for values in product((False, True), repeat=len(set(cycles))):
            signs = dict(zip(sorted(set(cycles)), values, strict=True))
            images = tuple(swap(representatives[perm[i]]) if signs[cycles[i]]
                           else representatives[perm[i]] for i in range(size))
            outputs.append(tuple(code for image in images for code in (image, swap(image))))
    return tuple(sorted(outputs))


def exhaustive_sector(representatives: tuple[int, ...]) -> tuple[Table, ...]:
    """Independent brute permutation filter on the six ordered inputs."""
    inputs = oriented_inputs(representatives)
    outputs = []
    for values in permutations(inputs):
        table = dict(zip(inputs, values, strict=True))
        if all(table[table[code]] == code and table[swap(code)] == swap(table[code])
               for code in inputs):
            outputs.append(values)
    return tuple(sorted(outputs))


def law_family() -> tuple[Table, ...]:
    sectors = (VACANT_SECTOR, MIXED_SECTOR)
    rows = tuple(signed_sector(sector) for sector in sectors)
    for sector, signed in zip(sectors, rows, strict=True):
        if len(set(signed)) != 20 or signed != exhaustive_sector(sector):
            raise AssertionError(f"incomplete or inconsistent sector {sector}")
    tables = []
    for blank, mixed in product(*rows):
        table = list(range(16))
        for sector, images in zip(sectors, (blank, mixed), strict=True):
            for code, image in zip(oriented_inputs(sector), images, strict=True):
                table[code] = image
        tables.append(tuple(table))
    if len(set(tables)) != 400:
        raise AssertionError("incomplete four-label law family")
    return tuple(sorted(tables))


def original_table() -> Table:
    return tuple(4 * left + right for left, right in (
        pair_record.four_label_contact(divmod(code, 4)) for code in range(16)))


def image(table: Table, pair: arms.Pair) -> arms.Pair:
    return divmod(table[4 * pair[0] + pair[1]], 4)


def add_swap(table: Table, code: int) -> Table:
    reverse = swap(code)
    if code == reverse or table[code] != code or table[reverse] != reverse:
        raise ValueError("swap must replace two fixed off-diagonal inputs")
    result = list(table)
    result[code], result[reverse] = reverse, code
    return tuple(result)


Counts = tuple[int, int, int, int]  # detector L, detector R, dumps, unread
PairCounts = tuple[pair_record.Triple, pair_record.Triple]
Program = tuple[tuple[arms.State, ...], tuple[arms.Pair, ...]]


def central_programs() -> tuple[Program, ...]:
    """Freeze launches and flatten only the ordering within disjoint layers."""
    programs = []
    for source, plates, opened in SETTINGS:
        layers = arms.schedule(plates, opened)
        for layer in layers:
            sites = tuple(site for pair in layer for site in pair)
            if len(sites) != len(set(sites)):
                raise AssertionError(f"overlapping contacts in {layer}")
        word = tuple(pair for layer in layers for pair in layer)
        stock = tuple(arms.initial_state(source, seeds, masks) for seeds, masks in LAUNCH_STOCK)
        if any(state.count(arms.TOKEN) != 1 for state in stock):
            raise AssertionError("central stock changed its token number")
        programs.append((stock, word))
    return tuple(programs)


def central_counts(table: Table, programs: tuple[Program, ...]) -> tuple[Counts, ...]:
    rows = []
    # Candidate construction already guarantees occupancy conservation at each
    # contact. No code-space test, early termination or acceptance filter is used.
    for stock, word in programs:
        left = right = dumps = unread = 0
        for before in stock:
            cells = list(before)
            for i, j in word:
                cells[i], cells[j] = divmod(table[4 * cells[i] + cells[j]], 4)
            l, r, d = arms.meter(tuple(cells))
            left += l
            right += r
            dumps += d
            unread += 1 - (l + r + d)
        rows.append((left, right, dumps, unread))
    return tuple(rows)


def standalone_pair_counts(table: Table) -> PairCounts:
    # Same original uncolored stock, pairing schedule, reader word and meter;
    # the contact table is uniform across both preparation and reader.
    fixture = replace(pair_record.FOUR_LABEL, contact=lambda pair: image(table, pair))

    def counts(crossed: bool) -> pair_record.Triple:
        result = pair_record.run_pairing(fixture, crossed=crossed)
        return tuple(map(sum, zip(*(trial.occupation for trial in result.trials), strict=True)))

    return counts(False), counts(True)


@dataclass(frozen=True)
class Road:
    orbit: tuple[arms.Pair, ...]
    cycle_start: int | None

    @property
    def first_distinct(self) -> bool:
        a, b = self.orbit[1]
        return a != b

    @property
    def indefinite(self) -> bool:
        return self.cycle_start is not None


def road(table: Table) -> Road:
    """Track both next-receiver labels on a fresh shade-1 all-blank road."""
    current = (1, 2)
    orbit = [current]
    seen = {current: 0}
    while True:
        a, b = current
        current = (image(table, (a, 1))[1], image(table, (b, 1))[1])
        orbit.append(current)
        if current[0] == current[1]:
            return Road(tuple(orbit), None)
        if current in seen:
            return Road(tuple(orbit), seen[current])
        seen[current] = len(orbit) - 1


def raw_central_traces(table: Table) -> Iterator[tuple[arms.State, ...]]:
    """Replay complete per-contact configurations in frozen launch order."""
    for source, plates, opened in SETTINGS:
        word = arms.schedule(plates, opened)
        for seeds, masks in LAUNCH_STOCK:
            state = arms.initial_state(source, seeds, masks)
            yield arms.replay(state, word, contact=lambda pair: image(table, pair))


@dataclass(frozen=True)
class CentralTrace:
    launches: int
    contacts: int
    identical: bool
    input_counts: tuple[tuple[int, int], ...]
    original_sha256: str
    variant_sha256: str


def compare_central_traces(original: Table, variant: Table, programs: tuple[Program, ...]) -> CentralTrace:
    launches = contacts = 0
    identical = True
    frequencies = Counter()
    original_digest, variant_digest = sha256(), sha256()
    words = (word for stock, word in programs for _ in stock)
    for word, first, second in zip(words, raw_central_traces(original), raw_central_traces(variant), strict=True):
        if len(first) != len(second) or len(first) != len(word) + 1:
            raise AssertionError("missing central trace configurations")
        launches += 1
        contacts += len(word)
        identical &= first == second
        frequencies.update(4 * state[i] + state[j]
                           for state, (i, j) in zip(first[:-1], word, strict=True))
        for digest, trace in ((original_digest, first), (variant_digest, second)):
            digest.update(json.dumps((word, trace), separators=(",", ":")).encode("ascii"))
    return CentralTrace(launches, contacts, identical, tuple((i, frequencies[i]) for i in range(16)),
                        original_digest.hexdigest(), variant_digest.hexdigest())


@dataclass(frozen=True)
class LawRecord:
    table: Table
    central: tuple[Counts, ...]
    pair: PairCounts
    road: Road

    @property
    def identity(self) -> str:
        return "".join(format(code, "x") for code in self.table)

    @property
    def moved_types(self) -> int:
        return sum(self.table[code] != code for code in VACANT_SECTOR + MIXED_SECTOR)


@dataclass(frozen=True)
class Census:
    records: tuple[LawRecord, ...]
    original: LawRecord
    token_zero_variant: LawRecord
    shade_forwarding_control: LawRecord
    alternating_three_type_control: LawRecord
    central_trace: CentralTrace

    @property
    def central_survivors(self) -> tuple[LawRecord, ...]:
        return tuple(record for record in self.records if record.central == self.original.central)

    @property
    def pair_survivors(self) -> tuple[LawRecord, ...]:
        return tuple(record for record in self.records if record.pair == self.original.pair)

    @property
    def joint_survivors(self) -> tuple[LawRecord, ...]:
        return tuple(record for record in self.central_survivors if record.pair == self.original.pair)

    def _group_matches(self, rows: tuple[int, ...]) -> int:
        return sum(all(record.central[i] == self.original.central[i] for i in rows)
                   for record in self.records)

    @property
    def central_group_match_counts(self) -> tuple[int, ...]:
        return tuple(self._group_matches(rows) for rows in CENTRAL_GROUPS)

    @property
    def central_nested_match_counts(self) -> tuple[int, ...]:
        return tuple(self._group_matches(tuple(i for group in CENTRAL_GROUPS[:end] for i in group))
                     for end in range(1, len(CENTRAL_GROUPS) + 1))

    @property
    def isolated_token_zero(self) -> tuple[arms.Pair, arms.Pair]:
        return image(self.original.table, (3, 0)), image(self.token_zero_variant.table, (3, 0))


def run_census() -> Census:
    programs = central_programs()
    records = tuple(LawRecord(table, central_counts(table, programs), standalone_pair_counts(table), road(table))
                    for table in law_family())
    by_table = {record.table: record for record in records}
    original = original_table()
    token_zero = add_swap(original, 3)
    alternate = list(add_swap(tuple(range(16)), 3))
    for a, b in ((1, 6), (swap(1), swap(6))):
        alternate[a], alternate[b] = b, a
    return Census(records, by_table[original], by_table[token_zero], by_table[add_swap(original, 6)],
                  by_table[tuple(alternate)], compare_central_traces(original, token_zero, programs))


def record_payload(record: LawRecord) -> dict[str, object]:
    return {
        "id": record.identity,
        "central_counts": record.central,
        "pair_counts": record.pair,
        "moved_unordered_types": record.moved_types,
        "road": asdict(record.road),
    }


def report(census: Census, *, enumerate_all: bool = False) -> dict[str, object]:
    rows = tuple(map(record_payload, census.records))
    named_tables = {
        "original": census.original,
        "original_plus_token_zero_swap": census.token_zero_variant,
        "original_plus_vacant_12_swap": census.shade_forwarding_control,
        "alternate_three_type": census.alternating_three_type_control,
    }
    result = {
        "scope": "Frozen family and fixed borrowed schedules only; not a schedule-independent law exclusion.",
        "table_encoding": "ID digits are the 16 output pair codes 4*a+b in ordered input code order.",
        "family_size": len(rows),
        "family_sha256": sha256(json.dumps(rows, sort_keys=True, separators=(",", ":")).encode("ascii")).hexdigest(),
        "central": {
            "counts_order": ("detector_left", "detector_right", "dumps", "unread"),
            "counts_denominator": len(LAUNCH_STOCK),
            "settings": SETTINGS,
            "setting_fields": ("source", "plates", "opened"),
            "group_order": ("all_open_no_plates", "all_open", "single_open", "both_closed"),
            "group_match_counts": census.central_group_match_counts,
            "nested_match_counts": census.central_nested_match_counts,
            "matching_ids": tuple(record.identity for record in census.central_survivors),
            "named_table_matching_row_counts": {
                name: sum(a == b for a, b in zip(record.central, census.original.central, strict=True))
                for name, record in named_tables.items()
            },
            "survivor_trace_comparison": asdict(census.central_trace),
            "isolated_token_zero_responses": census.isolated_token_zero,
        },
        "standalone_pair": {
            "counts_order": ("A", "B", "fresh_token_input_cell"),
            "counts_denominator": len(pair_record.FOUR_LABEL.blank_stock) ** 4
                                 * len(pair_record.FOUR_LABEL.token_stock),
            "row_order": ("matched", "crossed"),
            "matching_ids": tuple(record.identity for record in census.pair_survivors),
        },
        "joint_matching_ids": tuple(record.identity for record in census.joint_survivors),
        "fresh_shade_one_road": {
            "source_shades": (1, 2),
            "first_receiver_distinct": sum(record.road.first_distinct for record in census.records),
            "indefinite": sum(record.road.indefinite for record in census.records),
            "indefinite_among_pair_matches": sum(record.road.indefinite for record in census.pair_survivors),
            "indefinite_among_central_matches": sum(record.road.indefinite for record in census.central_survivors),
        },
        "named_tables": {name: record_payload(record) for name, record in named_tables.items()},
    }
    if enumerate_all:
        result["records"] = rows
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--enumerate", action="store_true", help="include all 400 raw tables and signatures")
    options = parser.parse_args()
    print(json.dumps(report(run_census(), enumerate_all=options.enumerate), sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
