#!/usr/bin/env python3
"""Verify the generated edition has no missing local links or item pages."""

from __future__ import annotations

import argparse
import json
import re
import sys
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit

from verify_dependencies import pm_order

ROOT = Path(__file__).resolve().parents[1]


class Links(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.links: list[str] = []
        self.images: list[dict[str, str | None]] = []
        self.ids: set[str] = set()

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = dict(attrs)
        if values.get("id"):
            self.ids.add(values["id"] or "")
        if tag in {"a", "link", "script"}:
            attr = "href" if tag != "script" else "src"
            if values.get(attr):
                self.links.append(values[attr] or "")
        if tag == "img":
            self.images.append(values)


def fail(message: str) -> None:
    print(f"site error: {message}", file=sys.stderr)
    raise SystemExit(1)


def verify(site: Path) -> None:
    manifest_path = site / "edition-manifest.json"
    if not (site / "index.html").is_file() or not manifest_path.is_file():
        fail("index.html or edition-manifest.json is missing")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    graph_path = site / manifest.get("dependency_graph", "")
    if not graph_path.is_file():
        fail("dependency graph JSON is missing")
    graph = json.loads(graph_path.read_text(encoding="utf-8"))
    if graph.get("coverage", {}).get("status") != "kernel-checked-items-only":
        fail("dependency graph lacks its limited coverage statement")
    expected_ids = sorted(
        item["id"]
        for metadata_path in sorted((ROOT / "metadata/items").glob("*.json"))
        for item in json.loads(metadata_path.read_text(encoding="utf-8"))["items"]
    )
    if manifest.get("item_ids") != expected_ids:
        fail("generated manifest does not match metadata/items")
    expected_order = sorted(expected_ids, key=pm_order)
    if manifest.get("ordered_item_ids") != expected_order:
        fail("generated manifest does not follow PM decimal item order")
    index_source = (site / "index.html").read_text(encoding="utf-8")
    rendered_order = re.findall(r'<li data-item-id="([^"]+)"', index_source)
    if rendered_order != expected_order:
        fail("index does not render formal items in PM decimal order")
    expected_source_ids = sorted(
        json.loads(path.read_text(encoding="utf-8"))["id"]
        for path in sorted((ROOT / "metadata/source_blocks").glob("*.json"))
    )
    if manifest.get("source_block_ids") != expected_source_ids:
        fail("generated manifest does not match metadata/source_blocks")
    pages = sorted((site / "items").glob("*.html"))
    expected_page_count = manifest["items"] + manifest["source_blocks"]
    if len(pages) != expected_page_count:
        fail(
            f"manifest says {expected_page_count} edition pages but "
            f"{len(pages)} pages exist"
        )
    html_paths = [site / "index.html", site / "dependencies.html", *pages]
    for path in html_paths:
        source = path.read_text(encoding="utf-8")
        if re.search(r"arstl_[A-Za-z0-9]+", source):
            fail(f"credential-like string leaked into {path}")
        parser = Links()
        parser.feed(source)
        if path != site / "index.html" and "content" not in parser.ids:
            fail(f"{path} lacks the main content landmark")
        if path not in {site / "index.html", site / "dependencies.html"}:
            if "scan-placeholder" in source:
                fail(f"facsimile placeholder remains in {path}")
            if len(parser.images) != 1:
                fail(f"{path} must contain exactly one facsimile image")
            image = parser.images[0]
            src = image.get("src") or ""
            if urlsplit(src).scheme != "https":
                fail(f"facsimile image in {path} does not use an HTTPS src")
            if urlsplit(src).hostname != "upload.wikimedia.org":
                fail(f"facsimile image in {path} is not served by Wikimedia")
            if not re.search(r"/page\d+-1280px-.*\.(?:djvu|pdf)\.jpg$", urlsplit(src).path, re.I):
                fail(f"facsimile image in {path} is not an exact scan-page derivative")
            if image.get("loading") != "lazy" or not image.get("alt"):
                fail(f"facsimile image in {path} lacks lazy loading or alternative text")
        for link in parser.links:
            parts = urlsplit(link)
            if parts.scheme or link.startswith("//") or not parts.path:
                continue
            target = (path.parent / unquote(parts.path)).resolve()
            if not target.is_file():
                fail(f"broken local link in {path}: {link}")
    required = {"assets/edition.css", "assets/edition.js", ".nojekyll"}
    missing = [name for name in required if not (site / name).is_file()]
    if missing:
        fail(f"missing generated assets: {missing}")
    for path in site.rglob("*"):
        if path.is_file() and re.search(r"arstl_[A-Za-z0-9]+", path.read_text(encoding="utf-8")):
            fail(f"credential-like string leaked into {path}")
    print(f"site checks passed ({len(pages)} edition pages)")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--site", type=Path, default=ROOT / "site")
    args = parser.parse_args()
    verify(args.site.resolve())


if __name__ == "__main__":
    main()
