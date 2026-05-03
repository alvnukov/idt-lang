"""Fetch external SPARC data artifacts required by verifier gates."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Final
from urllib.request import urlopen


RECORD_API_URL: Final = "https://zenodo.org/api/records/16284118"
TARGET_DIR: Final = Path(__file__).resolve().parents[1] / "data" / "sparc" / "raw"

EXPECTED_SHA256: Final = {
    "Rotmod_LTG.zip": "0a80cc90714828cc28b7dd57923576714d209f2490328c087c4a4ad607faf588",
    "SPARC_Lelli2016c.mrt": "5aa0501f6b0d881fa579030e315e7b5b6ef561a5bd3a07472f9929c7e5728243",
}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def fetch_json(url: str) -> dict[str, object]:
    with urlopen(url, timeout=60) as response:
        payload = response.read().decode("utf-8")
    data = json.loads(payload)
    if not isinstance(data, dict):
        raise RuntimeError("Zenodo API response is not a JSON object")
    return data


def file_links(record: dict[str, object]) -> dict[str, str]:
    files = record.get("files")
    if not isinstance(files, list):
        raise RuntimeError("Zenodo API response has no files list")
    links: dict[str, str] = {}
    for item in files:
        if not isinstance(item, dict):
            continue
        key = item.get("key")
        item_links = item.get("links")
        if not isinstance(key, str) or not isinstance(item_links, dict):
            continue
        download_url = item_links.get("self")
        if isinstance(download_url, str):
            links[key] = download_url
    return links


def download_file(url: str, target: Path) -> None:
    with urlopen(url, timeout=120) as response:
        target.write_bytes(response.read())


def main() -> None:
    TARGET_DIR.mkdir(parents=True, exist_ok=True)
    links = file_links(fetch_json(RECORD_API_URL))
    for filename, expected_hash in EXPECTED_SHA256.items():
        target = TARGET_DIR / filename
        if target.exists() and sha256_file(target) == expected_hash:
            print(f"ok: {target}")
            continue
        url = links.get(filename)
        if url is None:
            raise RuntimeError(f"Zenodo record does not expose {filename}")
        download_file(url, target)
        computed_hash = sha256_file(target)
        if computed_hash != expected_hash:
            target.unlink(missing_ok=True)
            raise RuntimeError(
                f"checksum mismatch for {filename}: expected {expected_hash}, got {computed_hash}"
            )
        print(f"downloaded: {target}")


if __name__ == "__main__":
    main()
