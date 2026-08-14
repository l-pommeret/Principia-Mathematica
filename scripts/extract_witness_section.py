#!/usr/bin/env python3
"""Extract one numbered section's body from a Project Gutenberg witness.

PM's witnesses carry each formula as an image whose LaTeX source travels in a
``data-tex`` attribute, so the mathematics is recoverable — but the plain text
also repeats every starred number in the table of contents, in cross-references,
and in the running heads. Matching the first occurrence of ``*9.`` yields the
contents page, not ✱9; that mistake has already cost two agents a wasted run and
produced a witness truncated to 2,467 bytes.

The body of a section is identified structurally instead: PM opens each one with
the number, its title in capitals, and a ``Summary of ✱N`` paragraph.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def to_text(source: str) -> str:
    """Flatten witness HTML, restoring each formula from its ``data-tex``."""
    def image(match: re.Match[str]) -> str:
        tag = match.group(0)
        tex = re.search(r'data-tex="([^"]*)"', tag)
        if tex:
            return " " + html.unescape(tex.group(1)) + " "
        alt = re.search(r'alt="([^"]*)"', tag)
        if alt and alt.group(1) not in ("", "decorative"):
            return f" [FIGURE: {html.unescape(alt.group(1))[:80]}] "
        return " "

    text = re.sub(r"<img[^>]*>", image, source)
    text = re.sub(r"<(script|style)[^>]*>.*?</\1>", " ", text, flags=re.S | re.I)
    text = re.sub(r"<br\s*/?>", "\n", text, flags=re.I)
    text = re.sub(r"</(p|div|h[1-6]|tr|table|li)>", "\n\n", text, flags=re.I)
    text = html.unescape(re.sub(r"<[^>]+>", "", text))
    text = re.sub(r"[ \t]+", " ", text)
    return re.sub(r"\n{3,}", "\n\n", text)


def section_body(text: str, number: int) -> tuple[int, int] | None:
    """Span of ✱``number``'s body, located by PM's own opening structure.

    A section opens with its number and a capitalised title, and is followed
    within a few hundred characters by ``Summary of *N``.  The table of contents
    repeats the number and title but never the summary, which is what
    distinguishes them.
    """
    candidates = [
        match.start()
        # Volume I sets its section titles in title case, volume II in capitals;
        # both are accepted, and the `Summary of` line below is what actually
        # separates a body from its table-of-contents echo.
        for match in re.finditer(rf"(?m)^\s*\*{number}\.\s+(?:[A-Z]\S|\\\S)", text)
    ]
    def is_body(start: int) -> bool:
        """Distinguish a section body from its table-of-contents echo.

        Most sections open with a ``Summary of ✱N`` paragraph, which the contents
        page never repeats.  A few — ✱12, on the hierarchy of types and the axiom
        of reducibility — have no summary at all; there the running title is what
        separates them, since PM sets the body heading in capitals and the
        contents entry in title case.
        """
        window = text[start: start + 4000]
        if re.search(rf"Summary of \*{number}\b", window):
            return True
        # `^\s*` in the candidate pattern may have consumed the preceding
        # newline, so the heading has to be read from the asterisk itself.
        asterisk = text.index("*", start)
        line_end = text.find("\n", asterisk)
        heading = text[asterisk: line_end if line_end > 0 else asterisk + 200]
        letters = [c for c in heading if c.isalpha()]
        return bool(letters) and all(c.isupper() for c in letters)

    for start in candidates:
        if is_body(start):
            # Search from past the header line, and skip any re-match on this
            # section's own number: `^\s*` can consume the preceding newline, so
            # the same header matches again one byte later and the body comes out
            # empty.
            after = text.index("\n", start) + 1
            for match in re.finditer(
                r"(?m)^\s*\*(\d{1,3})\.\s+[A-Z]\S", text[after:]
            ):
                if int(match.group(1)) == number:
                    continue
                nxt = after + match.start()
                if re.search(r"Summary of \*\d", text[nxt: nxt + 4000]):
                    return start, nxt
            return start, len(text)
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witness", type=Path, help="the witness HTML or flattened text")
    parser.add_argument("number", type=int, help="starred number, e.g. 9")
    parser.add_argument("--out", type=Path, required=True)
    arguments = parser.parse_args()

    raw = arguments.witness.read_text(encoding="utf-8", errors="replace")
    text = to_text(raw) if "<" in raw[:2000] else raw

    span = section_body(text, arguments.number)
    if span is None:
        print(
            f"✱{arguments.number}: no section body found — only table-of-contents "
            "or cross-reference matches. Refusing to write a misleading extract.",
            file=sys.stderr,
        )
        return 1
    body = text[span[0]: span[1]]
    if len(body) < 3000:
        print(
            f"✱{arguments.number}: extracted body is only {len(body)} bytes, which is "
            "too short to be a section. Refusing to write it.",
            file=sys.stderr,
        )
        return 1

    arguments.out.write_text(body, encoding="utf-8")
    demonstrations = body.count("Dem.")
    print(
        f"✱{arguments.number}: {len(body)} bytes, {demonstrations} demonstrations, "
        f"sha256 {hashlib.sha256(body.encode()).hexdigest()[:16]} -> {arguments.out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
