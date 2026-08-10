#!/usr/bin/env python3
"""Build the static, reader-facing PM edition using only the Python stdlib."""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import shutil
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import quote
from urllib.parse import unquote
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
VERBATIM = re.compile(
    r"PM-VERBATIM-BEGIN\s+(\S+)\s*\n(.*?)\nPM-VERBATIM-END\s+\1", re.DOTALL
)


@dataclass(frozen=True)
class SourceBlock:
    text: str
    path: Path


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def source_blocks() -> dict[str, SourceBlock]:
    found: dict[str, SourceBlock] = {}
    for path in sorted((ROOT / "Principia").rglob("*.lean")):
        source = path.read_text(encoding="utf-8")
        for match in VERBATIM.finditer(source):
            found[match.group(1)] = SourceBlock(match.group(2).rstrip(), path)
    return found


def lean_excerpt(item: dict) -> str:
    path = ROOT / item["lean_path"]
    source = path.read_text(encoding="utf-8")
    declaration = item["declaration"].split(".")[-1]
    lines = source.splitlines()
    declaration_line = next(
        (index for index, line in enumerate(lines) if re.search(rf"\b{re.escape(declaration)}\b", line)),
        None,
    )
    if declaration_line is None:
        return f"-- declaration indexed as {item['declaration']}\n-- see {item['lean_path']}"
    start = declaration_line
    while start and lines[start - 1].lstrip().startswith(("/--", "--")):
        start -= 1
    end = min(len(lines), declaration_line + 16)
    for index in range(declaration_line + 1, end):
        if not lines[index].strip():
            end = index
            break
    return "\n".join(lines[start:end]).rstrip()


def scope_reading(item: dict) -> str:
    path = ROOT / item["lean_path"]
    source = path.read_text(encoding="utf-8")
    stem = item["declaration"].split(".")[-1].removesuffix("_printed")
    vicinity = re.search(
        rf"def\s+{re.escape(stem)}_reading\b(.*?)(?=\n(?:def|theorem|end)\b)",
        source,
        re.DOTALL,
    )
    if vicinity and (match := re.search(r'scopeReading\s*:=\s*"([^"]*)"', vicinity.group(0))):
        return match.group(1)
    return item.get("formal_scope", "No separate scope reading has yet been recorded.")


def slug(item_id: str) -> str:
    return "item-" + quote(item_id, safe="").replace("%", "-").lower()


def page(title: str, body: str, *, depth: int = 0) -> str:
    prefix = "../" * depth
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="color-scheme" content="light dark">
  <title>{html.escape(title)} · Principia Mathematica</title>
  <link rel="stylesheet" href="{prefix}assets/edition.css">
  <script defer src="{prefix}assets/edition.js"></script>
</head>
<body>
<a class="skip-link" href="#content">Skip to the edition</a>
<header class="masthead">
  <a class="brand" href="{prefix}index.html"><span>Whitehead &amp; Russell</span> Principia Mathematica</a>
  <p>A source-critical Lean edition · First edition</p>
</header>
<main id="content">{body}</main>
<footer>Working edition. Diplomatic source text, editorial apparatus, and formal reconstruction are kept distinct.</footer>
</body>
</html>"""


def external_link(uri: str, label: str) -> str:
    if urlsplit(uri).scheme not in {"http", "https"}:
        return html.escape(label) + f" ({html.escape(uri or 'not recorded')})"
    safe = html.escape(uri, quote=True)
    return f'<a href="{safe}" rel="noreferrer">{html.escape(label)}</a>'


def scan_urls(canonical_scan: str, leaf: int | str) -> dict[str, str]:
    """Return deterministic Wikimedia URLs for a page in a multipage scan.

    MediaWiki's ``Special:Redirect/file`` currently renders page 1 even when a
    ``page`` query parameter is supplied.  Wikimedia's documented thumbnail
    layout is deterministic, however: it uses the MD5 of the underscore-
    normalised file name and a ``pageN-Wpx`` derivative name.  Generating that
    path here keeps the static build reproducible and network-free.
    """
    parts = urlsplit(canonical_scan)
    marker = "/wiki/File:"
    if parts.scheme != "https" or marker not in parts.path:
        raise ValueError(f"unsupported canonical scan URL: {canonical_scan}")
    filename = unquote(parts.path.split(marker, 1)[1]).replace(" ", "_")
    if not filename.lower().endswith((".djvu", ".pdf")):
        raise ValueError(f"canonical scan is not multipage: {canonical_scan}")
    page_number = int(leaf)
    if page_number < 1:
        raise ValueError(f"invalid scan leaf: {leaf}")
    digest = hashlib.md5(filename.encode("utf-8")).hexdigest()
    encoded = quote(filename, safe="_,.-()")
    base = (
        "https://upload.wikimedia.org/wikipedia/commons/thumb/"
        f"{digest[0]}/{digest[:2]}/{encoded}/"
    )

    def thumbnail(width: int) -> str:
        return f"{base}page{page_number}-{width}px-{encoded}.jpg"

    page_title = quote(f"Page:{filename}/{page_number}", safe="_:,.-()")
    file_title = quote(f"File:{filename}", safe="_:,.-()")
    return {
        "display": thumbnail(1280),
        "zoom": thumbnail(1920),
        "page": f"https://en.wikisource.org/wiki/{page_title}",
        "file": f"https://commons.wikimedia.org/wiki/{file_title}",
    }


def apparatus_html(records: list[dict]) -> str:
    if not records:
        return '<p class="quiet">No apparatus entry is currently linked to this item.</p>'
    cards = []
    for record in records:
        witnesses = "".join(
            f'<li><b>{html.escape(w["siglum"])}</b>: {html.escape(w["reading"])} '
            f'({external_link(w["uri"], "witness")})</li>'
            for w in record["witnesses"]
        )
        marker = f' · <b>{html.escape(record["marker"])}</b>' if record.get("marker") else ""
        cards.append(f"""<article class="apparatus-card">
<h3>{html.escape(record['id'])}</h3>
<p><span class="badge">{html.escape(record['classification'])}</span>{marker}</p>
<dl><dt>Diplomatic reading</dt><dd>{html.escape(record['diplomatic_reading'])}</dd>
<dt>Evidence</dt><dd>{html.escape(record['evidence'])}</dd></dl>
<details><summary>Witness readings</summary><ul>{witnesses}</ul></details>
</article>""")
    return "".join(cards)


def printed_formula_markup(printed: str) -> str:
    """Escape a formula while making PM's printed scope punctuation addressable."""
    return "".join(
        f'<span class="scope-mark">{html.escape(char)}</span>'
        if char in ".:" and not (char == "." and index == len(printed) - 1)
        else html.escape(char)
        for index, char in enumerate(printed)
    )


def item_page(item: dict, batch: dict, block: SourceBlock, apparatus: list[dict]) -> str:
    scan = batch["source_range"]["canonical_scan"]
    leaf = item.get("scan_leaf")
    scan_media = scan_urls(scan, leaf)
    printed = printed_formula_markup(item["printed"])
    source = html.escape(block.text)
    lean = html.escape(lean_excerpt(item))
    scope = html.escape(scope_reading(item))
    run = batch.get("ci_evidence", {}).get("run", "")
    evidence = (external_link(run, "Successful GitHub Actions run")
                if urlsplit(run).scheme in {"http", "https"} else "Pending CI evidence")
    body = f"""
<nav aria-label="Breadcrumb"><a href="../index.html">Contents</a> / Volume {item['volume'] if 'volume' in item else batch['volume']} / {html.escape(item['id'])}</nav>
<article class="edition-item">
<header class="item-header"><p class="eyebrow">Volume {batch['volume']} · printed page {item['printed_page']}</p>
<h1>{html.escape(item['id'].split(':', 1)[1])}</h1><p class="formula" data-pm-formula>{printed}</p>
<p><span class="badge">{html.escape(item['kind'])}</span> <span class="badge">{html.escape(item['source_status'])}</span></p></header>
<div class="scope-box"><h2>Scope reading</h2><p>{scope}</p>
<button type="button" class="scope-toggle" aria-pressed="false">Show printed scope marks</button></div>
<div class="parallel" aria-label="Source and formal edition">
<section class="panel scan"><h2>Facsimile</h2><p>Canonical witness: first edition scan, leaf {leaf}.</p>
<figure class="scan-figure"><a class="scan-image-link" href="{html.escape(scan_media['zoom'], quote=True)}" target="_blank" rel="noreferrer" aria-label="Open a larger image of scan leaf {leaf}"><img src="{html.escape(scan_media['display'], quote=True)}" loading="lazy" decoding="async" width="1280" alt="Principia Mathematica, volume {batch['volume']}, first edition: scan leaf {leaf}, printed page {item['printed_page']}"></a>
<figcaption><a href="{html.escape(scan_media['page'], quote=True)}" rel="noreferrer">Page and transcription on Wikisource</a> · <a href="{html.escape(scan_media['file'], quote=True)}" rel="noreferrer">Original scan and provenance on Wikimedia Commons</a> · <a href="{html.escape(scan_media['zoom'], quote=True)}" target="_blank" rel="noreferrer">Larger image</a></figcaption></figure></section>
<section class="panel transcription"><h2>Diplomatic transcription</h2><pre class="source-text">{source}</pre></section>
<section class="panel lean"><h2>Lean reconstruction</h2><pre><code>{lean}</code></pre>
<dl><dt>Declaration</dt><dd><code>{html.escape(item['declaration'])}</code></dd><dt>Formal scope</dt><dd>{html.escape(item['formal_scope'])}</dd></dl></section>
</div>
<section class="apparatus"><h2>Critical apparatus</h2>{apparatus_html(apparatus)}</section>
<section class="provenance"><h2>Provenance and verification</h2><dl>
<dt>Source file</dt><dd><code>{html.escape(str(block.path.relative_to(ROOT)))}</code></dd>
<dt>Lean file</dt><dd><code>{html.escape(item['lean_path'])}</code></dd>
<dt>CI evidence</dt><dd>{evidence}</dd><dt>Commit</dt><dd><code>{html.escape(batch.get('ci_evidence', {}).get('commit', 'not recorded'))}</code></dd>
</dl></section></article>"""
    return page(item["id"], body, depth=1)


def build(output: Path) -> None:
    blocks = source_blocks()
    batches = [load_json(path) for path in sorted((ROOT / "metadata/items").glob("*.json"))]
    apparatus = [load_json(path) for path in sorted((ROOT / "metadata/apparatus").glob("*.json"))]
    items: list[tuple[dict, dict]] = [(item, batch) for batch in batches for item in batch["items"]]
    if output.exists():
        shutil.rmtree(output)
    (output / "items").mkdir(parents=True)
    shutil.copytree(ROOT / "edition/assets", output / "assets")
    cards = []
    indexed_ids = {item["id"] for item, _ in items}
    for item, batch in items:
        linked = [record for record in apparatus if record["item"] == item["id"]]
        target = output / "items" / f"{slug(item['id'])}.html"
        target.write_text(item_page(item, batch, blocks[item["id"]], linked), encoding="utf-8")
        cards.append(f"""<li><a href="items/{target.name}"><b>{html.escape(item['id'].split(':', 1)[1])}</b>
<span>{html.escape(item['kind'])}</span><small>p. {item['printed_page']} · {html.escape(item['printed'])}</small></a></li>""")
    orphan = [record for record in apparatus if record["item"] not in indexed_ids]
    orphan_note = ""
    if orphan:
        orphan_note = ("<section><h2>Apparatus awaiting an item page</h2><p>These records are retained but the corresponding "
                       "edition item is not yet present: " + ", ".join(html.escape(r["item"]) for r in orphan) + ".</p></section>")
    body = f"""<section class="hero"><p class="eyebrow">First edition · Volumes I–III</p>
<h1>A formal edition faithful to the printed page</h1>
<p>Read the historical English, inspect the facsimile, and compare the audited Lean reconstruction. Scope punctuation and editorial interventions remain visible.</p></section>
<section><h2>Available items</h2><ol class="contents">{''.join(cards)}</ol></section>{orphan_note}
<section class="method"><h2>How to read this edition</h2><p>The transcription is diplomatic. A <i>sic</i> is rendered only from a reviewed apparatus record and never inserted into canonical source bytes. Lean declarations are reconstructions, not silent replacements for PM's notation.</p></section>"""
    (output / "index.html").write_text(page("Contents", body), encoding="utf-8")
    (output / ".nojekyll").write_text("", encoding="utf-8")
    manifest = {"items": len(items), "apparatus": len(apparatus), "item_ids": sorted(indexed_ids)}
    (output / "edition-manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"built {len(items)} item pages in {output}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "site")
    args = parser.parse_args()
    build(args.output.resolve())


if __name__ == "__main__":
    main()
