"""Offline replay of the published, fixed Apamea within-archive transfer protocol."""

from __future__ import annotations

import hashlib
import json
import sys
from collections.abc import Sequence
from pathlib import Path
from typing import TypedDict

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts import probe_measured_asi_loop_parity as measured

DATA = measured.DATA.parent / "ergodicity_asi_transfer"
PROTOCOL = measured.DATA / "transfer_protocol.json"
COMMIT = "e1b7b29fab0d29ae1e5f0f59ffabcf88da27e825"
PROTOCOL_SHA256 = "91937dbee50d8442939455565358e4e6f2716e2ec5fcc66a514975c0f1c7e9c2"
REPLAY_SHA256 = "ba47eeb7cc36be3a8c87294d3738b52900dfcbf6eb0bc86f0c85f2f5942efb2b"
NAMES = ("coordinates_000.dat", "coordinates_001.dat")
HASHES = {
    260: (
        "542027a22ebe9e1eb49572de69538b23884f98b97c4dd940b105d1c56d82fff9",
        "435e0c64c3e076eccfca5f159c1aba1513844ea14c193e5c1f916d771905f411",
    ),
    270: (
        "da226c88644daaca00309da3ff43c38a73439a8efbb19eb0d9de00e1950f3187",
        "061cb39aad0142fc81cd384b6942326a7a0749a92761b8eff530152346a95894",
    ),
    280: (
        "f53cd90369c6c3935866e6f16bd6d90d4e1c52af99b153345135de447fa4ecba",
        "2c781eaeaa4c4451690b394a50814feecd9c6a8f12433fced0dc6d29f093f53d",
    ),
    290: (
        "0cf8dbcca907acd6b0b768cc47fefcc5a28ddaa626456ac19d70c95cd4f98c8e",
        "9f27e22a71f5e3b493c6a75431cd5295b03d901fb1f5d921e038ae90965ff970",
    ),
    300: (
        "9cb81c35a40dccf61ac212b021340f955a0c5b8f1d0681a5a681efea8fcfe56b",
        "0d5045f7bd25ef1a55947bf50272e80bfda09e692b6dc5c1216bd206ab530957",
    ),
    310: (
        "1760299e0d05d632f7f7d8dfd745429c775b07a24c04de7ff4d0e9961856ae59",
        "935f80ec5c310b9c3d47ad1bf409bac92786f9c612651f689e9b3a93d36d2a1c",
    ),
}


class PairRow(TypedDict):
    status: str
    reasons: list[str]
    detail: list[str]
    row_counts: list[int | None]
    matched: int | None
    only_first: int | None
    only_second: int | None
    reversed_classifications: int | None
    geometry: dict[str, object] | None
    odd_complete_faces: int | None
    even_complete_faces: int | None


class TransferRow(PairRow):
    temperature_K: int
    members: list[str]
    sha256_expected: tuple[str, str]
    missing_members: list[str]


def empty_row() -> PairRow:
    return PairRow(
        status="inconclusive",
        reasons=[],
        detail=[],
        row_counts=[None, None],
        matched=None,
        only_first=None,
        only_second=None,
        reversed_classifications=None,
        geometry=None,
        odd_complete_faces=None,
        even_complete_faces=None,
    )


def analyze_pair(a: Sequence[measured.Spin], b: Sequence[measured.Spin]) -> PairRow:
    row = empty_row()
    row["row_counts"] = [len(a), len(b)]
    try:
        islands = measured.match(a, b)
    except ValueError as exc:
        if not str(exc).startswith("ambiguous same-axis pairing near rows "):
            raise
        row["reasons"].append("ambiguous_matching")
        row["detail"].append(str(exc))
        return row
    row["matched"] = sum(s.flip is not None for s in islands)
    row["only_first"] = sum(s.second is None for s in islands)
    row["only_second"] = sum(s.first is None for s in islands)
    row["reversed_classifications"] = sum(s.flip is True for s in islands)
    try:
        # Diagnostic mode keeps crossing evidence. Explicitly reject that embedding below.
        census = measured.faces(islands, 4, slope=1, diagnostic=True)
    except ValueError as exc:
        if str(exc) != "endpoint clustering produced a self/parallel edge":
            raise
        row["reasons"].append("self_or_parallel_edge")
        row["detail"].append(str(exc))
        return row
    row["geometry"] = census.summary()
    if census.crossings:
        row["reasons"].append("crossed_embedding")
    if not census.degrees.get(4):
        row["reasons"].append("no_fourfold_vertex")
    if not census.crossings:
        if not census.sizes:
            row["reasons"].append("no_bounded_simple_faces")
        if not census.flips:
            row["reasons"].append("no_complete_faces")
    if not row["reasons"]:
        row["status"] = "usable"
        row["odd_complete_faces"] = sum(n for k, n in census.flips.items() if k % 2)
        row["even_complete_faces"] = sum(
            n for k, n in census.flips.items() if not k % 2
        )
    return row


def replay_temperature(temperature: int, root: Path = DATA) -> TransferRow:
    digests = HASHES[temperature]
    names = [f"{temperature}K/{name}" for name in NAMES]
    missing: list[str] = []
    inputs: list[tuple[measured.Spin, ...]] = []
    pair = empty_row()
    for i, (name, digest) in enumerate(zip(names, digests, strict=True)):
        try:
            data = (root / name).read_bytes()
        except FileNotFoundError:
            missing.append(name)
            continue
        try:
            frame = measured.read_frame(data, digest)
        except ValueError as exc:
            if not str(exc).startswith(
                ("nonfinite input at row ", "unrecognized moment/axis encoding at row ")
            ):
                raise
            if "inapplicable_frame_encoding" not in pair["reasons"]:
                pair["reasons"].append("inapplicable_frame_encoding")
            pair["row_counts"][i] = len(data.splitlines())
            pair["detail"].append(f"{name}: {exc}")
            continue
        inputs.append(frame)
        pair["row_counts"][i] = len(frame)
    if missing:
        pair["reasons"].append("missing_source")
    if not pair["reasons"]:
        a, b = inputs
        pair = analyze_pair(a, b)
    return TransferRow(
        **pair,
        temperature_K=temperature,
        members=names,
        sha256_expected=digests,
        missing_members=missing,
    )


def report() -> dict[str, object]:
    protocol = PROTOCOL.read_bytes()
    if hashlib.sha256(protocol).hexdigest() != PROTOCOL_SHA256:
        raise ValueError("published transfer protocol SHA-256 mismatch")
    if (
        hashlib.sha256(Path(measured.__file__).read_bytes()).hexdigest()
        != REPLAY_SHA256
    ):
        raise ValueError("published primary replay SHA-256 mismatch")
    contract = json.loads(protocol)
    if contract["test_temperatures_K"] != list(HASHES) or contract[
        "frames_in_each_temperature_directory"
    ] != list(NAMES):
        raise ValueError("transfer inputs disagree with published selection")
    return {
        "schema": "idt-apamea-fixed-transfer-result/1",
        "protocol_commit": COMMIT,
        "protocol_sha256": PROTOCOL_SHA256,
        "primary_replay_sha256": REPLAY_SHA256,
        "source_version_doi": contract["source_version_doi"],
        "scope": contract["scope"],
        "rows": [replay_temperature(t) for t in contract["test_temperatures_K"]],
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
