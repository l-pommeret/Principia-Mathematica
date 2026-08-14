#!/usr/bin/env python3
"""Convert witness LaTeX into PM's diplomatic notation.

Project Gutenberg renders PM's formulae as images carrying their LaTeX source in
a ``data-tex`` attribute, so a transcription taken from that witness arrives as
LaTeX: ``\\vdash :\\dot{\\exists} !P.\\supset .P\\downarrow_{.,} \\in 1\\rightarrow 1``.
That is a faithful record of the witness but it is not what the page shows, and
an edition that prints it under the heading "diplomatic transcription" is
misdescribing itself.

This converts the LaTeX alphabet actually observed in the catalogue (59 commands)
into the diplomatic alphabet the hand-transcribed items already use.  It never
guesses: anything it cannot map is reported and left untouched, so a residual
backslash is a visible failure rather than a silent mangling.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ITEMS = ROOT / "metadata" / "items"

#: Combining marks PM uses over a letter.
COMBINING = {
    "dot": "\u0307",          # φ̇ — the dotted operators of relation-arithmetic
    "breve": "\u030c",        # Ř — PM's converse mark
    "hat": "\u0302",          # ẑ — circumflex of class abstraction
    "overrightarrow": "\u20d7",
    "overleftarrow": "\u20d6",
    "overline": "\u0305",
    "check": "\u030c",
}

#: Single-token commands, mapped to the character the hand-transcribed items use.
SYMBOLS = {
    r"\vdash": "⊢", r"\dashv": "⊣",
    r"\supset": "⊃", r"\equiv": "≡", r"\sim": "∼", r"\lor": "∨", r"\vee": "∨",
    r"\land": "∧", r"\wedge": "∧",
    r"\in": "∈", r"\subset": "⊂", r"\supseteq": "⊇", r"\subseteq": "⊆",
    r"\cap": "∩", r"\cup": "∪",
    r"\exists": "∃", r"\forall": "∀",
    r"\Lambda": "Λ", r"\Delta": "Δ", r"\Sigma": "Σ", r"\Pi": "Π",
    r"\Omega": "Ω", r"\Theta": "Θ",
    r"\alpha": "α", r"\beta": "β", r"\gamma": "γ", r"\delta": "δ",
    r"\epsilon": "ε", r"\varepsilon": "ε", r"\zeta": "ζ", r"\eta": "η",
    r"\theta": "θ", r"\iota": "ι", r"\kappa": "κ", r"\lambda": "λ",
    r"\mu": "μ", r"\nu": "ν", r"\xi": "ξ", r"\pi": "π", r"\varpi": "ϖ",
    r"\rho": "ρ", r"\sigma": "σ", r"\tau": "τ", r"\phi": "φ", r"\varphi": "φ",
    r"\chi": "χ", r"\psi": "ψ", r"\omega": "ω",
    r"\rightarrow": "→", r"\leftarrow": "←", r"\leftrightarrow": "↔",
    r"\downarrow": "↓", r"\uparrow": "↑",
    r"\upharpoonright": "↾", r"\upharpoonleft": "↿",
    r"\mid": "|", r"\parallel": "∥", r"\dagger": "†",
    r"\times": "×", r"\neq": "≠", r"\geq": "≥", r"\leq": "≤",
    r"\colon": ":", r"\ldotp": ".", r"\cdot": ".",
    r"\infty": "∞", r"\emptyset": "∅", r"\prime": "′",
}

#: Spacing and grouping that carries no diplomatic content.
DROP = (
    r"\quad", r"\qquad", r"\,", r"\;", r"\!", r"\ ", r"\left", r"\right",
    r"\displaystyle", r"\limits", r"\nolimits", r"\notag", r"\\",
)

SUBSCRIPTS = str.maketrans("0123456789aeoxhklmnpstij", "₀₁₂₃₄₅₆₇₈₉ₐₑₒₓₕₖₗₘₙₚₛₜᵢⱼ")
SUPERSCRIPTS = str.maketrans("0123456789n", "⁰¹²³⁴⁵⁶⁷⁸⁹ⁿ")


def _unicode_escapes(text: str) -> str:
    return re.sub(
        r"\\unicode\{x([0-9A-Fa-f]+)\}",
        lambda m: chr(int(m.group(1), 16)),
        text,
    )


def _combining(text: str) -> str:
    """``\\dot{x}`` -> ``ẋ``.  Applied repeatedly for nested marks."""
    # Accepts both real braces and the sentinels that stand in for PM's own
    # escaped braces, so a mark applied inside `\\{ … \\}` is still recognised.
    pattern = re.compile(
        r"\\(" + "|".join(COMBINING) + r")\s*[{\u0001]([^{}\u0001\u0002]*)[}\u0002]"
    )
    previous = None
    while previous != text:
        previous = text
        text = pattern.sub(lambda m: m.group(2) + COMBINING[m.group(1)], text)
    return text


def _scripts(text: str) -> str:
    """Lower and raise indices where a Unicode form exists."""
    def lower(match: re.Match[str]) -> str:
        body = match.group(1)
        return body.translate(SUBSCRIPTS) if all(
            c in "0123456789aeoxhklmnpstij" for c in body
        ) else "_" + body

    def raise_(match: re.Match[str]) -> str:
        body = match.group(1)
        return body.translate(SUPERSCRIPTS) if all(
            c in "0123456789n" for c in body
        ) else "^" + body

    text = re.sub(r"_\{([^{}]*)\}", lower, text)
    text = re.sub(r"\^\{([^{}]*)\}", raise_, text)
    text = re.sub(r"_([0-9a-z])", lambda m: m.group(1).translate(SUBSCRIPTS), text)
    return text



def _balanced(text: str, start: int) -> tuple[str, int] | None:
    """Content of the brace group beginning at ``start``, and the index after it."""
    if start >= len(text) or text[start] != "{":
        return None
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1: index], index + 1
    return None


def _fractions(text: str) -> str:
    """``\\frac{a}{b}`` -> ``a/b``, tolerating nested groups."""
    out = []
    index = 0
    while index < len(text):
        if text.startswith(r"\frac", index):
            first = _balanced(text, index + 5)
            if first:
                second = _balanced(text, first[1])
                if second:
                    out.append(_fractions(first[0]) + "/" + _fractions(second[0]))
                    index = second[1]
                    continue
        out.append(text[index])
        index += 1
    return "".join(out)


def convert(text: str) -> str:
    """Best-faith diplomatic rendering.  Residual ``\\`` marks a failure."""
    out = _unicode_escapes(text)
    out = re.sub(r"\\text\s*\{([^{}]*)\}", r"\1", out)
    out = re.sub(r"\\(?:begin|end)\s*\{[^{}]*\}", " ", out)
    # PM's substitution bracket is set as a fraction: `[✱43·5 S,S̆/Q,R]` prints
    # the substituted terms above the variables they replace.  Rendered with a
    # solidus, which is how the hand-transcribed items already write it.
    out = _fractions(out)
    # Escaped braces are PM's own braces, not LaTeX grouping.  Protected here so
    # the grouping-brace strip below cannot swallow them — this was the cause of
    # most residuals (`\{Q` surviving as a spurious `\Q`).
    out = out.replace(r"\{", "\u0001").replace(r"\}", "\u0002")
    out = _combining(out)
    for token in DROP:
        out = out.replace(token, " ")
    # Longest first, so `\subseteq` is not eaten by `\subset`.
    for command in sorted(SYMBOLS, key=len, reverse=True):
        out = out.replace(command, SYMBOLS[command])
    out = _scripts(out)
    out = out.replace(r"\(", "").replace(r"\)", "")
    out = out.replace(r"\[", "").replace(r"\]", "")
    out = out.replace("&", " ").replace("$", "")
    out = re.sub(r"\{([^{}]*)\}", r"\1", out)
    # LaTeX's escaped space carries no diplomatic content.  Restricted to
    # whitespace and brackets so a meaningful backslash still survives as a
    # visible failure rather than being dropped.
    out = re.sub(r"\\(?=[\s\[\]])", "", out)
    out = out.replace("\u0001", "{").replace("\u0002", "}")
    out = re.sub(r"[ \t]+", " ", out).strip()
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="apply the conversion")
    parser.add_argument("--sample", type=int, default=12)
    arguments = parser.parse_args()

    paths = sorted(ITEMS.glob("*.json"))
    if not paths:
        print(f"no catalogue items under {ITEMS}", file=sys.stderr)
        return 1

    converted = residual = 0
    leftovers: Counter[str] = Counter()
    samples: list[tuple[str, str, str]] = []
    touched: list[Path] = []

    for path in paths:
        batch = json.loads(path.read_text(encoding="utf-8"))
        dirty = False
        for item in batch.get("items", []):
            printed = item.get("printed", "")
            if "\\" not in printed:
                continue
            rendered = convert(printed)
            if "\\" in rendered:
                residual += 1
                leftovers.update(re.findall(r"\\[a-zA-Z]+", rendered))
                continue  # never write a half-converted reading
            converted += 1
            if len(samples) < arguments.sample:
                samples.append((item.get("id", "?"), printed, rendered))
            if arguments.write:
                item["printed_latex_witness"] = printed
                item["printed"] = rendered
                dirty = True
        if dirty:
            path.write_text(
                json.dumps(batch, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
            )
            touched.append(path)

    for identifier, before, after in samples:
        print(f"{identifier}\n  LaTeX : {before[:150]}\n  PM    : {after[:150]}\n")
    print(f"convertibles : {converted}")
    print(f"non convertibles (laissés intacts) : {residual}")
    if leftovers:
        print("commandes non couvertes :", dict(leftovers.most_common(12)))
    if arguments.write:
        print(f"écrits : {len(touched)} catalogues")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
