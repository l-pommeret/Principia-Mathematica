#!/usr/bin/env python3
"""Index PM source-page candidates without turning OCR into canonical text.

The output is a review queue: a detected number is never a source backfill,
metadata item, or Lean target until a human/audited collation records it.
"""

from __future__ import annotations

import argparse
import json
import re
import urllib.request


PM_ITEM = re.compile(r"[✱*]\s*(\d+)\s*[·.]\s*(\d+)")


def candidates(url: str, volume: int) -> dict:
    with urllib.request.urlopen(url, timeout=30) as response:
        text = response.read().decode("utf-8", errors="replace")
    numbers = sorted({f"PM{volume}:✱{star}·{suffix}"
                      for star, suffix in PM_ITEM.findall(text)})
    return {
        "kind": "pm-source-harvest-candidates",
        "volume": volume,
        "source_url": url,
        "candidate_ids": numbers,
        "status": "unreviewed-never-canonical",
        "required_before_catalogue": [
            "facsimile/print collation",
            "PM-VERBATIM transcription",
            "demonstration skeleton",
            "item metadata and integration gate",
        ],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("url")
    parser.add_argument("--volume", type=int, required=True)
    options = parser.parse_args()
    print(json.dumps(candidates(options.url, options.volume), ensure_ascii=False, indent=2))
